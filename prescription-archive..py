# -*- coding: utf-8 -*-
"""Medical Prescription Archive - Full CustomTkinter Edition (FIXED)

Fixes applied over v3.1.4:
 1. WAL-safe backup/restore (checkpoint + clean -wal/-shm files).
 2. Fullscreen viewer no longer mutates the form's image path.
 3. Date and age validation on save.
 4. Case-insensitive medication uniqueness via COLLATE NOCASE.
 5. Autocomplete: keyboard nav, prefix search, robust FocusOut.
 6. Background threading for image compression + saves (no UI freeze).
 7. Multi-line notes via CTkTextbox.
 8. Scrollable form page.
 9. AND / OR toggle for multi-medicine search.
10. Pillow resampling compatibility fallback.
11. Removed dead code and unused constants.
"""

import os
import sys
import json
import shutil
import sqlite3
import zipfile
import tempfile
import logging
import uuid
import threading
import tkinter as tk
from datetime import datetime
from pathlib import Path
from contextlib import contextmanager

import customtkinter as ctk
from tkinter import filedialog, messagebox, simpledialog
from PIL import Image, ImageOps, ImageTk

# --- Pillow compatibility (older versions lack Image.Resampling) -------------
try:
    RESAMPLE_LANCZOS = Image.Resampling.LANCZOS
except AttributeError:                       # Pillow < 9.1
    RESAMPLE_LANCZOS = Image.LANCZOS

APP_NAME = "Medical Prescription Archive"
APP_VERSION = "3.2.0"
SCHEMA_VERSION = 3
MAX_IMAGE_SIDE = 2400
JPEG_QUALITY = 88
AUTO_BACKUP_KEEP = 5
MAX_AGE = 150

DEFAULT_CATEGORIES = ["General", "Antibiotics", "Pediatrics", "Chronic", "Dermatology", "Emergency"]
ROUTES = ["", "Oral", "IV", "IM", "SC", "Topical", "Inhalation", "Rectal", "Ophthalmic", "Otic", "Nasal", "Other"]
GENDERS = ["", "Male", "Female", "Other"]

BG = "#F4F7FB"
CARD = "#FFFFFF"
TEXT = "#172033"
MUTED = "#64748B"
BORDER = "#D9E1EC"
ACCENT = "#2563EB"
SIDEBAR = "#0F172A"
SIDEBAR_ACTIVE = "#1E3A8A"


# ---------------------------------------------------------------------------
def get_base_dir():
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))


BASE_DIR = get_base_dir()
DATA_DIR = os.path.join(BASE_DIR, "data")
IMAGES_DIR = os.path.join(DATA_DIR, "images")
BACKUPS_DIR = os.path.join(DATA_DIR, "backups")
LOGS_DIR = os.path.join(DATA_DIR, "logs")
DB_PATH = os.path.join(DATA_DIR, "prescriptions.db")
LOG_PATH = os.path.join(LOGS_DIR, "app.log")

for directory in (DATA_DIR, IMAGES_DIR, BACKUPS_DIR, LOGS_DIR):
    os.makedirs(directory, exist_ok=True)

logging.basicConfig(filename=LOG_PATH, level=logging.INFO,
                    format="%(asctime)s | %(levelname)s | %(message)s")
LOGGER = logging.getLogger("prescription_archive")


@contextmanager
def connect(db_path=DB_PATH):
    conn = sqlite3.connect(db_path, timeout=15)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    conn.execute("PRAGMA busy_timeout = 15000")
    conn.execute("PRAGMA journal_mode = WAL")
    conn.execute("PRAGMA synchronous = NORMAL")
    try:
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def checkpoint_wal(db_path=DB_PATH):
    """Flush WAL contents into the main DB file so a plain file-copy is safe."""
    if not os.path.exists(db_path):
        return
    try:
        conn = sqlite3.connect(db_path, timeout=15)
        try:
            conn.execute("PRAGMA wal_checkpoint(TRUNCATE)")
        finally:
            conn.close()
    except Exception as exc:
        LOGGER.warning("wal_checkpoint failed: %s", exc)


def table_columns(conn, table_name):
    return {row[1] for row in conn.execute(f"PRAGMA table_info({table_name})").fetchall()}


def init_db():
    with connect() as conn:
        c = conn.cursor()
        c.execute("""CREATE TABLE IF NOT EXISTS prescriptions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            patient_name TEXT, age TEXT, gender TEXT, doctor_name TEXT,
            date TEXT, category TEXT, notes TEXT, image_path TEXT,
            created_at TEXT, updated_at TEXT, deleted_at TEXT)""")
        # Case-insensitive uniqueness on medication name.
        c.execute("""CREATE TABLE IF NOT EXISTS medications (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL COLLATE NOCASE UNIQUE)""")
        c.execute("""CREATE TABLE IF NOT EXISTS prescription_items (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            prescription_id INTEGER NOT NULL, medication_id INTEGER NOT NULL,
            strength TEXT, dose TEXT, frequency TEXT, duration TEXT,
            route TEXT, item_notes TEXT,
            FOREIGN KEY (prescription_id) REFERENCES prescriptions(id) ON DELETE CASCADE,
            FOREIGN KEY (medication_id) REFERENCES medications(id))""")
        c.execute("CREATE TABLE IF NOT EXISTS categories (id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT UNIQUE)")
        c.execute("CREATE TABLE IF NOT EXISTS search_history (id INTEGER PRIMARY KEY AUTOINCREMENT, query TEXT, searched_at TEXT)")
        c.execute("CREATE TABLE IF NOT EXISTS app_settings (key TEXT PRIMARY KEY, value TEXT)")
        c.execute("""CREATE TABLE IF NOT EXISTS audit_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT, prescription_id INTEGER,
            action TEXT NOT NULL, details TEXT DEFAULT '', created_at TEXT NOT NULL,
            FOREIGN KEY (prescription_id) REFERENCES prescriptions(id) ON DELETE SET NULL)""")

        cols = table_columns(conn, "prescriptions")
        for col, decl in {"updated_at": "TEXT", "deleted_at": "TEXT", "notes": "TEXT"}.items():
            if col not in cols:
                c.execute(f"ALTER TABLE prescriptions ADD COLUMN {col} {decl}")

        if c.execute("SELECT COUNT(*) FROM categories").fetchone()[0] == 0:
            c.executemany("INSERT OR IGNORE INTO categories(name) VALUES(?)",
                          [(x,) for x in DEFAULT_CATEGORIES])

        # Case-insensitive unique index for existing databases (safe if it fails).
        try:
            c.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_medications_name_nocase "
                      "ON medications(name COLLATE NOCASE)")
        except sqlite3.IntegrityError:
            LOGGER.warning("Could not create NOCASE index (duplicates exist). "
                           "Cleaning duplicates…")
            c.execute("""DELETE FROM medications WHERE id NOT IN (
                            SELECT MIN(id) FROM medications GROUP BY LOWER(name))""")

        c.execute("INSERT OR REPLACE INTO app_settings(key,value) VALUES('schema_version',?)",
                  (str(SCHEMA_VERSION),))
        c.execute("INSERT OR REPLACE INTO app_settings(key,value) VALUES('app_version',?)",
                  (APP_VERSION,))

        for stmt in (
            "CREATE INDEX IF NOT EXISTS idx_prescriptions_date ON prescriptions(date)",
            "CREATE INDEX IF NOT EXISTS idx_prescriptions_deleted ON prescriptions(deleted_at)",
            "CREATE INDEX IF NOT EXISTS idx_prescriptions_category ON prescriptions(category)",
            "CREATE INDEX IF NOT EXISTS idx_items_prescription ON prescription_items(prescription_id)",
            "CREATE INDEX IF NOT EXISTS idx_items_medication ON prescription_items(medication_id)",
            "CREATE INDEX IF NOT EXISTS idx_search_history_query ON search_history(query)",
            "CREATE INDEX IF NOT EXISTS idx_audit_prescription ON audit_log(prescription_id)",
        ):
            c.execute(stmt)
    LOGGER.info("Database initialized at %s", DB_PATH)


def integrity_check(db_path=DB_PATH):
    try:
        with connect(db_path) as conn:
            result = conn.execute("PRAGMA integrity_check").fetchone()[0]
            fk = conn.execute("PRAGMA foreign_key_check").fetchall()
            if result != "ok":
                return False, f"SQLite integrity_check: {result}"
            if fk:
                return False, f"Foreign-key errors: {len(fk)}"
            return True, "Database integrity is OK."
    except Exception as exc:
        return False, str(exc)


def save_compressed_image(src_path, dst_path):
    with Image.open(src_path) as raw:
        img = ImageOps.exif_transpose(raw)
        if img.mode in ("RGBA", "LA", "P"):
            if img.mode == "P":
                img = img.convert("RGBA")
            bg = Image.new("RGB", img.size, "white")
            if img.mode == "RGBA":
                bg.paste(img, mask=img.getchannel("A"))
            else:
                bg.paste(img)
            img = bg
        elif img.mode != "RGB":
            img = img.convert("RGB")
        w, h = img.size
        if max(w, h) > MAX_IMAGE_SIDE:
            ratio = MAX_IMAGE_SIDE / max(w, h)
            img = img.resize((max(1, int(w * ratio)), max(1, int(h * ratio))),
                             RESAMPLE_LANCZOS)
        img.save(dst_path, "JPEG", quality=JPEG_QUALITY, optimize=True)


def levenshtein(a, b):
    if a == b: return 0
    if not a: return len(b)
    if not b: return len(a)
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(cur[-1] + 1, prev[j] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def safe_path(relative):
    if not relative:
        return None
    base = Path(BASE_DIR).resolve()
    target = (base / relative).resolve()
    try:
        target.relative_to(base)
    except ValueError:
        return None
    return str(target)


# --- Validators ------------------------------------------------------------
def valid_date(text):
    """Empty allowed; otherwise must be YYYY-MM-DD."""
    text = (text or "").strip()
    if not text:
        return True
    try:
        datetime.strptime(text, "%Y-%m-%d")
        return True
    except ValueError:
        return False


def valid_age(text):
    """Empty allowed; otherwise a non-negative integer ≤ MAX_AGE."""
    text = (text or "").strip()
    if not text:
        return True
    if not text.isdigit():
        return False
    return 0 <= int(text) <= MAX_AGE


# ===========================================================================
# AutocompleteEntry  (with keyboard nav + prefix search + safe FocusOut)
# ===========================================================================
class AutocompleteEntry(ctk.CTkEntry):
    def __init__(self, master, suggestions_callback, **kwargs):
        super().__init__(master, **kwargs)
        self._suggest = suggestions_callback
        self._popup = None
        self._listbox = None
        self._hide_job = None
        self.bind("<KeyRelease>", self._on_key)
        self.bind("<Down>", self._on_down_from_entry)
        self.bind("<FocusOut>", self._on_focus_out)
        self.bind("<Escape>", lambda e: self._hide(return_focus=True))
        self.bind("<Return>", self._on_return_from_entry)

    # -- events ------------------------------------------------------------
    def _on_key(self, event):
        if event.keysym in ("Up", "Down", "Return", "Escape", "Tab",
                            "Left", "Right", "Home", "End", "Prior", "Next"):
            return
        text = self.get().strip()
        if len(text) < 2:
            self._hide()
            return
        try:
            items = self._suggest(text)[:8]
        except Exception:
            items = []
        if items:
            self._show(items)
        else:
            self._hide()

    def _on_down_from_entry(self, event=None):
        if self._listbox and self._listbox.size() > 0:
            self._listbox.focus_set()
            self._listbox.selection_clear(0, "end")
            self._listbox.selection_set(0)
            self._listbox.activate(0)
            return "break"

    def _on_return_from_entry(self, event=None):
        # If popup visible, pick the first suggestion; otherwise let Return bubble.
        if self._listbox and self._listbox.size() > 0:
            self.delete(0, "end")
            self.insert(0, self._listbox.get(0))
            self._hide()
            return "break"

    def _on_focus_out(self, event=None):
        # Defer so a click on the listbox can register first.
        if self._hide_job:
            try:
                self.after_cancel(self._hide_job)
            except Exception:
                pass
        self._hide_job = self.after(180, self._check_hide)

    def _check_hide(self):
        self._hide_job = None
        try:
            focused = self.focus_get()
        except Exception:
            focused = None
        if focused is self._listbox:
            return
        self._hide()

    # -- popup -------------------------------------------------------------
    def _show(self, items):
        # Update in place if possible (avoids flicker).
        if self._listbox is None:
            self._popup = tk.Toplevel(self)
            self._popup.wm_overrideredirect(True)
            self._popup.attributes("-topmost", True)
            self._listbox = tk.Listbox(self._popup, activestyle="none",
                                       font=("Segoe UI", 10), borderwidth=0,
                                       exportselection=False,
                                       highlightthickness=1,
                                       highlightbackground=BORDER)
            self._listbox.pack(fill="both", expand=True)
            self._listbox.bind("<<ListboxSelect>>", self._pick)
            self._listbox.bind("<Return>", self._pick)
            self._listbox.bind("<Escape>", lambda e: self._hide(return_focus=True))
            self._listbox.bind("<Up>", self._on_up_in_listbox)
            self._listbox.bind("<FocusOut>", self._on_focus_out)
        else:
            self._listbox.delete(0, "end")

        for it in items:
            self._listbox.insert("end", it)

        x = self.winfo_rootx()
        y = self.winfo_rooty() + self.winfo_height()
        w = max(self.winfo_width(), 220)
        h = min(len(items), 8) * 24
        self._popup.geometry(f"{w}x{h}+{x}+{y}")
        self._popup.deiconify()

    def _on_up_in_listbox(self, event=None):
        if self._listbox and self._listbox.curselection():
            if self._listbox.curselection()[0] == 0:
                self.focus_set()
                return "break"

    def _pick(self, event=None):
        if self._listbox:
            sel = self._listbox.curselection()
            if sel:
                self.delete(0, "end")
                self.insert(0, self._listbox.get(sel[0]))
        self._hide(return_focus=True)

    def _hide(self, return_focus=False):
        if self._hide_job:
            try:
                self.after_cancel(self._hide_job)
            except Exception:
                pass
            self._hide_job = None
        if self._popup:
            try:
                self._popup.destroy()
            except Exception:
                pass
            self._popup = None
            self._listbox = None
        if return_focus:
            try:
                self.focus_set()
            except Exception:
                pass


# ===========================================================================
# MedicationCard
# ===========================================================================
class MedicationCard(ctk.CTkFrame):
    def __init__(self, parent, app, data=None, remove_callback=None):
        super().__init__(parent, corner_radius=14, fg_color="#F8FAFC",
                         border_width=1, border_color=BORDER)
        self.app = app
        self.remove_callback = remove_callback
        for i in range(4):
            self.grid_columnconfigure(i, weight=1)

        ctk.CTkLabel(self, text="Medicine", font=("Segoe UI", 11, "bold"),
                     text_color=TEXT).grid(row=0, column=0, sticky="w",
                                            padx=12, pady=(10, 3))
        ctk.CTkButton(self, text="✕", width=34, height=30, corner_radius=9,
                      fg_color="#FEE2E2", hover_color="#FECACA", text_color="#991B1B",
                      command=self._remove).grid(row=0, column=3, sticky="e",
                                                  padx=10, pady=7)

        self.name = AutocompleteEntry(self, suggestions_callback=app._med_suggestions,
                                      height=38, corner_radius=9,
                                      placeholder_text="Medicine name",
                                      font=("Segoe UI", 12))
        self.name.grid(row=1, column=0, columnspan=4, sticky="ew",
                       padx=10, pady=(0, 9))

        self.strength = self._field("Strength", 2, 0, "e.g. 500 mg")
        self.dose = self._field("Dose", 2, 1, "e.g. 1 tablet")
        self.frequency = self._field("Frequency", 2, 2, "e.g. twice daily")
        self.duration = self._field("Duration", 2, 3, "e.g. 7 days")
        self.route = self._combo("Route", 3, 0, ROUTES)
        self.note = self._field("Item note", 3, 1, "Optional note", span=3)

        if data:
            self.set_data(data)

    def _field(self, label, row, col, placeholder, span=1):
        box = ctk.CTkFrame(self, fg_color="transparent")
        box.grid(row=row, column=col, columnspan=span, sticky="ew", padx=6, pady=5)
        box.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(box, text=label, font=("Segoe UI", 10, "bold"),
                     text_color=MUTED).grid(row=0, column=0, sticky="w",
                                             padx=4, pady=(0, 3))
        entry = ctk.CTkEntry(box, height=36, corner_radius=8,
                             placeholder_text=placeholder, font=("Segoe UI", 11))
        entry.grid(row=1, column=0, sticky="ew", padx=4, pady=(0, 3))
        return entry

    def _combo(self, label, row, col, values):
        box = ctk.CTkFrame(self, fg_color="transparent")
        box.grid(row=row, column=col, sticky="ew", padx=6, pady=5)
        box.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(box, text=label, font=("Segoe UI", 10, "bold"),
                     text_color=MUTED).grid(row=0, column=0, sticky="w",
                                             padx=4, pady=(0, 3))
        combo = ctk.CTkComboBox(box, values=values, height=36, corner_radius=8,
                                font=("Segoe UI", 11), dropdown_font=("Segoe UI", 11))
        combo.grid(row=1, column=0, sticky="ew", padx=4, pady=(0, 3))
        return combo

    def _remove(self):
        if self.remove_callback:
            self.remove_callback(self)

    def get_data(self):
        return {
            "name": self.name.get().strip(),
            "strength": self.strength.get().strip(),
            "dose": self.dose.get().strip(),
            "frequency": self.frequency.get().strip(),
            "duration": self.duration.get().strip(),
            "route": self.route.get().strip(),
            "item_notes": self.note.get().strip(),
        }

    def set_data(self, data):
        self.name.delete(0, "end"); self.name.insert(0, data.get("name", ""))
        for widget, key in ((self.strength, "strength"), (self.dose, "dose"),
                            (self.frequency, "frequency"), (self.duration, "duration"),
                            (self.note, "item_notes")):
            widget.delete(0, "end"); widget.insert(0, data.get(key, ""))
        self.route.set(data.get("route", ""))


# ===========================================================================
# ImageViewer  (tk.Canvas + PIL, fixed size)
# ===========================================================================
class ImageViewer(ctk.CTkFrame):
    def __init__(self, parent, width=380, height=280):
        super().__init__(parent, fg_color="#111827", corner_radius=12,
                         width=width, height=height)
        self._init_width = width
        self._init_height = height
        self.grid_propagate(False)
        self.pack_propagate(False)

        self.canvas = tk.Canvas(self, bg="#111827", highlightthickness=0, bd=0)
        self.canvas.pack(fill="both", expand=True, padx=6, pady=6)

        self.image = None
        self.tk_image = None
        self.zoom = 1.0
        self.fit_mode = True
        self.rotation = 0
        self._render_job = None

        self.canvas.bind("<Configure>", self._schedule_render)
        self.after(10, self._draw_placeholder)

    def _schedule_render(self, _event=None):
        if self._render_job:
            try:
                self.after_cancel(self._render_job)
            except Exception:
                pass
        self._render_job = self.after(50, self._render)

    def _draw_placeholder(self):
        self.canvas.delete("all")
        cw = self.canvas.winfo_width() or self._init_width
        ch = self.canvas.winfo_height() or self._init_height
        if cw <= 1: cw = self._init_width
        if ch <= 1: ch = self._init_height
        self.canvas.create_text(cw // 2, ch // 2, text="No image",
                                fill="#9CA3AF", font=("Segoe UI", 12),
                                anchor="center")

    def load(self, path):
        try:
            with Image.open(path) as im:
                self.image = ImageOps.exif_transpose(im).convert("RGB").copy()
        except Exception as exc:
            self.image = None
            self.tk_image = None
            self.canvas.delete("all")
            cw = self.canvas.winfo_width() or self._init_width
            ch = self.canvas.winfo_height() or self._init_height
            if cw <= 1: cw = self._init_width
            if ch <= 1: ch = self._init_height
            self.canvas.create_text(cw // 2, ch // 2,
                                    text=f"Could not load image\n{exc}",
                                    fill="#F87171", font=("Segoe UI", 10),
                                    anchor="center", justify="center")
            return
        self.zoom = 1.0
        self.fit_mode = True
        self.rotation = 0
        try:
            self.update_idletasks()
        except Exception:
            pass
        self._render()
        self.after(80, self._render)
        self.after(250, self._render)

    def clear(self):
        self.image = None
        self.tk_image = None
        self._draw_placeholder()

    def _render(self):
        self._render_job = None
        if self.image is None:
            return
        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        if cw <= 1 or ch <= 1:
            cw = self._init_width
            ch = self._init_height
        img = self.image.rotate(-self.rotation, expand=True) if self.rotation else self.image
        ratio = min(cw / img.width, ch / img.height) if self.fit_mode else self.zoom
        new_w = max(1, int(img.width * ratio))
        new_h = max(1, int(img.height * ratio))
        resized = img.resize((new_w, new_h), RESAMPLE_LANCZOS)
        self.tk_image = ImageTk.PhotoImage(resized)
        self.canvas.delete("all")
        x = max((cw - new_w) // 2, 0)
        y = max((ch - new_h) // 2, 0)
        self.canvas.create_image(x, y, anchor="nw", image=self.tk_image)

    def zoom_in(self):
        self.fit_mode = False
        self.zoom = min(self.zoom * 1.2, 8)
        self._render()

    def zoom_out(self):
        self.fit_mode = False
        self.zoom = max(self.zoom / 1.2, 0.05)
        self._render()

    def fit(self):
        self.fit_mode = True
        self._render()

    def rotate(self):
        if self.image:
            self.rotation = (self.rotation + 90) % 360
            self._render()


# ===========================================================================
# Main application
# ===========================================================================
class PrescriptionApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        init_db()
        self.title(f"{APP_NAME}  •  v{APP_VERSION}")
        self.geometry("1420x900")
        self.minsize(1100, 720)
        self.configure(fg_color=BG)
        ctk.set_appearance_mode("light")
        ctk.set_default_color_theme("blue")

        self.editing_id = None
        self.current_image_path = None
        self.current_image_dirty = False
        self.medication_cards = []
        self.selected_search_id = None
        self.selected_trash_id = None
        self._save_in_progress = False

        self.grid_rowconfigure(0, weight=1)
        self.grid_columnconfigure(0, weight=0, minsize=225)
        self.grid_columnconfigure(1, weight=1)

        self._build_sidebar()
        self._build_pages()
        self._bind_shortcuts()
        self.protocol("WM_DELETE_WINDOW", self._on_close)

        self._show_page("dashboard")
        self._refresh_categories()
        self._clear_form()
        self._refresh_all()

    # ---------------- sidebar / pages ----------------
    def _build_sidebar(self):
        self.sidebar = ctk.CTkFrame(self, width=225, corner_radius=0, fg_color=SIDEBAR)
        self.sidebar.grid(row=0, column=0, sticky="nsew")
        self.sidebar.grid_propagate(False)
        self.sidebar.grid_rowconfigure(8, weight=1)

        ctk.CTkLabel(self.sidebar, text="PRESCRIPTION", font=("Segoe UI", 19, "bold"),
                     text_color="white").grid(row=0, column=0, sticky="w", padx=22, pady=(28, 0))
        ctk.CTkLabel(self.sidebar, text="ARCHIVE", font=("Segoe UI", 11, "bold"),
                     text_color="#93C5FD").grid(row=1, column=0, sticky="w",
                                                 padx=22, pady=(0, 25))

        items = [
            ("dashboard", "⌂", "Dashboard"), ("form", "+", "New Prescription"),
            ("search", "⌕", "Search Archive"), ("trash", "♲", "Trash"),
            ("stats", "▥", "Statistics"), ("tools", "⚙", "Tools"),
        ]
        self.nav_buttons = {}
        for i, (key, icon, text) in enumerate(items, 2):
            btn = ctk.CTkButton(self.sidebar, text=f"  {icon}   {text}", anchor="w",
                                height=45, corner_radius=10, fg_color="transparent",
                                hover_color="#1E293B", text_color="#CBD5E1",
                                font=("Segoe UI", 12, "bold"),
                                command=lambda k=key: self._show_page(k))
            btn.grid(row=i, column=0, sticky="ew", padx=12, pady=5)
            self.nav_buttons[key] = btn

        ctk.CTkLabel(self.sidebar, text=f"v{APP_VERSION}\nLocal / Offline",
                     justify="left", font=("Segoe UI", 10), text_color="#64748B"
                     ).grid(row=9, column=0, sticky="sw", padx=22, pady=22)

    def _build_pages(self):
        self.content = ctk.CTkFrame(self, fg_color=BG, corner_radius=0)
        self.content.grid(row=0, column=1, sticky="nsew")
        self.content.grid_rowconfigure(0, weight=1)
        self.content.grid_columnconfigure(0, weight=1)

        builders = (
            ("dashboard", self._page_dashboard),
            ("form",      self._page_form),
            ("search",    self._page_search),
            ("trash",     self._page_trash),
            ("stats",     self._page_stats),
            ("tools",     self._page_tools),
        )
        self.pages = {}
        for key, builder in builders:
            if key == "search":
                scroller = ctk.CTkScrollableFrame(self.content, fg_color=BG)
                scroller.grid(row=0, column=0, sticky="nsew")
                scroller.grid_remove()
                frame = ctk.CTkFrame(scroller, fg_color=BG)
                frame.pack(fill="both", expand=True)
                frame.grid_rowconfigure(2, weight=1)
                frame.grid_columnconfigure(0, weight=1)
                self.pages[key] = scroller
                builder(frame)
            else:
                frame = ctk.CTkFrame(self.content, fg_color=BG)
                frame.grid(row=0, column=0, sticky="nsew")
                frame.grid_remove()
                self.pages[key] = frame
                builder(frame)

    def _show_page(self, key):
        for page in self.pages.values():
            page.grid_remove()
        self.pages[key].grid()
        for name, btn in self.nav_buttons.items():
            btn.configure(fg_color=SIDEBAR_ACTIVE if name == key else "transparent")
        if key == "dashboard": self._refresh_dashboard()
        elif key == "search": self._refresh_search()
        elif key == "trash": self._refresh_trash()
        elif key == "stats": self._refresh_stats()

    def _header(self, parent, title, subtitle):
        frame = ctk.CTkFrame(parent, fg_color="transparent")
        frame.grid(row=0, column=0, sticky="ew", padx=26, pady=(24, 12))
        frame.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(frame, text=title, font=("Segoe UI", 27, "bold"),
                     text_color=TEXT).grid(row=0, column=0, sticky="w")
        ctk.CTkLabel(frame, text=subtitle, font=("Segoe UI", 11),
                     text_color=MUTED).grid(row=1, column=0, sticky="w", pady=(3, 0))
        return frame

    def _card(self, parent, row, col, rowspan=1, colspan=1, **kwargs):
        card = ctk.CTkFrame(parent, corner_radius=16, fg_color=CARD,
                            border_width=1, border_color=BORDER, **kwargs)
        card.grid(row=row, column=col, rowspan=rowspan, columnspan=colspan,
                  sticky="nsew", padx=8, pady=8)
        return card

    # ---------------- dashboard ----------------
    def _page_dashboard(self, p):
        p.grid_rowconfigure(2, weight=1)
        p.grid_columnconfigure(0, weight=1); p.grid_columnconfigure(1, weight=1)
        self._header(p, "Dashboard", "Overview of your local prescription archive")
        cards = ctk.CTkFrame(p, fg_color="transparent")
        cards.grid(row=1, column=0, columnspan=2, sticky="ew", padx=18, pady=4)
        for i in range(4):
            cards.grid_columnconfigure(i, weight=1)
        self.stat_cards = {}
        for i, (key, label) in enumerate((("total", "Active Prescriptions"),
                                          ("meds", "Unique Medicines"),
                                          ("trash", "In Trash"),
                                          ("month", "This Month"))):
            card = ctk.CTkFrame(cards, corner_radius=14, fg_color=CARD,
                                border_width=1, border_color=BORDER)
            card.grid(row=0, column=i, sticky="ew", padx=7, pady=7)
            ctk.CTkLabel(card, text=label, font=("Segoe UI", 11),
                         text_color=MUTED).pack(anchor="w", padx=18, pady=(16, 3))
            val = ctk.CTkLabel(card, text="0", font=("Segoe UI", 25, "bold"),
                               text_color=TEXT)
            val.pack(anchor="w", padx=18, pady=(0, 16))
            self.stat_cards[key] = val

        recent = self._card(p, 2, 0, colspan=2)
        recent.grid_columnconfigure(0, weight=1); recent.grid_rowconfigure(1, weight=1)
        ctk.CTkLabel(recent, text="Recent Prescriptions", font=("Segoe UI", 16, "bold"),
                     text_color=TEXT).grid(row=0, column=0, sticky="w", padx=18, pady=(16, 10))
        self.dashboard_list = ctk.CTkTextbox(recent, height=330, corner_radius=10,
                                             fg_color="#F8FAFC", font=("Consolas", 11))
        self.dashboard_list.grid(row=1, column=0, sticky="nsew", padx=18, pady=(0, 18))

    def _refresh_dashboard(self):
        with connect() as conn:
            total = conn.execute("SELECT COUNT(*) FROM prescriptions WHERE deleted_at IS NULL").fetchone()[0]
            meds = conn.execute("SELECT COUNT(*) FROM medications").fetchone()[0]
            trash = conn.execute("SELECT COUNT(*) FROM prescriptions WHERE deleted_at IS NOT NULL").fetchone()[0]
            month = datetime.now().replace(day=1).strftime("%Y-%m-%d")
            month_count = conn.execute("SELECT COUNT(*) FROM prescriptions WHERE deleted_at IS NULL AND date >= ?", (month,)).fetchone()[0]
            rows = conn.execute("""SELECT p.id,p.patient_name,p.doctor_name,p.date,p.category,
                GROUP_CONCAT(m.name, ', ') meds FROM prescriptions p
                LEFT JOIN prescription_items pi ON pi.prescription_id=p.id
                LEFT JOIN medications m ON m.id=pi.medication_id
                WHERE p.deleted_at IS NULL GROUP BY p.id ORDER BY p.id DESC LIMIT 15""").fetchall()
        for k, v in (("total", total), ("meds", meds), ("trash", trash), ("month", month_count)):
            self.stat_cards[k].configure(text=f"{v:,}")
        self.dashboard_list.configure(state="normal")
        self.dashboard_list.delete("1.0", "end")
        if not rows:
            self.dashboard_list.insert("end", "No prescriptions yet.\n")
        else:
            for r in rows:
                self.dashboard_list.insert("end",
                    f"#{r['id']:<5} {r['date'] or '-':<12} {r['patient_name'] or '-':<25} "
                    f"{r['category'] or '-':<15} {r['meds'] or '-'}\n")
        self.dashboard_list.configure(state="disabled")

    # ---------------- form ----------------
    def _page_form(self, p):
        p.grid_rowconfigure(1, weight=1)
        p.grid_columnconfigure(0, weight=1)
        self._header(p, "New Prescription",
                     "Add medicines, attach the image, then fill patient details")

        # Scrollable content area (fixes layout on small screens).
        scroll = ctk.CTkScrollableFrame(p, fg_color=BG, corner_radius=0)
        scroll.grid(row=1, column=0, sticky="nsew", padx=0, pady=0)
        scroll.grid_columnconfigure(0, weight=1)

        body = ctk.CTkFrame(scroll, fg_color="transparent")
        body.grid(row=0, column=0, sticky="nsew", padx=10, pady=(0, 6))
        body.grid_columnconfigure(0, weight=3)
        body.grid_columnconfigure(1, weight=1, minsize=320)

        # -- medicines card --
        left = self._card(body, 0, 0)
        left.grid_rowconfigure(1, weight=1)
        left.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(left, text="Medicines", font=("Segoe UI", 16, "bold"),
                     text_color=TEXT).grid(row=0, column=0, sticky="w",
                                            padx=18, pady=(16, 12))

        meds_section = ctk.CTkFrame(left, corner_radius=12, fg_color="#F8FAFC",
                                    border_width=1, border_color=BORDER)
        meds_section.grid(row=1, column=0, sticky="nsew", padx=10, pady=(0, 10))
        meds_section.grid_rowconfigure(1, weight=1)
        meds_section.grid_columnconfigure(0, weight=1)

        head = ctk.CTkFrame(meds_section, fg_color="transparent")
        head.grid(row=0, column=0, sticky="ew", padx=12, pady=(10, 4))
        head.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(head, text="Medicine list", font=("Segoe UI", 12, "bold"),
                     text_color=TEXT).grid(row=0, column=0, sticky="w")
        ctk.CTkButton(head, text="+ Add Medicine", width=135, height=34,
                      command=self._add_medication_card).grid(row=0, column=1, sticky="e")

        self.med_scroll = ctk.CTkScrollableFrame(meds_section, fg_color="transparent",
                                                  height=380)
        self.med_scroll.grid(row=1, column=0, sticky="nsew", padx=8, pady=(4, 10))
        self.med_scroll.grid_columnconfigure(0, weight=1)
        self.medication_cards = []

        # -- image card --
        right = self._card(body, 0, 1)
        right.grid_rowconfigure(1, weight=1)
        right.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(right, text="Prescription Image", font=("Segoe UI", 16, "bold"),
                     text_color=TEXT).grid(row=0, column=0, sticky="w",
                                            padx=16, pady=(16, 10))
        viewer_wrap = ctk.CTkFrame(right, fg_color="transparent")
        viewer_wrap.grid(row=1, column=0, sticky="nsew", padx=14, pady=4)
        viewer_wrap.grid_rowconfigure(0, weight=1)
        viewer_wrap.grid_columnconfigure(0, weight=1)
        self.form_viewer = ImageViewer(viewer_wrap, width=280, height=280)
        self.form_viewer.grid(row=0, column=0, sticky="nsew")

        toolbar = ctk.CTkFrame(right, fg_color="transparent")
        toolbar.grid(row=2, column=0, sticky="ew", padx=14, pady=(6, 14))
        toolbar.grid_columnconfigure(0, weight=1)
        toolbar.grid_columnconfigure(1, weight=1)
        ctk.CTkButton(toolbar, text="Choose Image", height=38,
                      command=self._choose_image).grid(row=0, column=0, sticky="ew",
                                                        padx=(0, 5))
        ctk.CTkButton(toolbar, text="Remove Image", height=38,
                      fg_color="#FEE2E2", hover_color="#FECACA", text_color="#991B1B",
                      command=self._remove_image).grid(row=0, column=1, sticky="ew",
                                                        padx=(5, 0))

        # -- details card --
        details_card = ctk.CTkFrame(scroll, corner_radius=14, fg_color=CARD,
                                    border_width=1, border_color=BORDER)
        details_card.grid(row=1, column=0, sticky="ew", padx=18, pady=(0, 6))
        details_card.grid_columnconfigure(0, weight=1)

        ctk.CTkLabel(details_card, text="Patient & Prescription Details",
                     font=("Segoe UI", 13, "bold"), text_color=TEXT
                     ).grid(row=0, column=0, sticky="w", padx=14, pady=(10, 6))

        grid = ctk.CTkFrame(details_card, fg_color="transparent")
        grid.grid(row=1, column=0, sticky="ew", padx=8, pady=(0, 10))
        for c in (1, 3, 5, 7):
            grid.grid_columnconfigure(c, weight=1)

        def _lbl(parent, text, row, col):
            ctk.CTkLabel(parent, text=text, font=("Segoe UI", 9, "bold"),
                         text_color=MUTED).grid(row=row, column=col, sticky="e",
                                                 padx=(8, 4), pady=3)

        def _entry(parent, row, col, placeholder=""):
            e = ctk.CTkEntry(parent, height=30, corner_radius=7, fg_color="#F8FAFC",
                             placeholder_text=placeholder, font=("Segoe UI", 10))
            e.grid(row=row, column=col, sticky="ew", padx=(0, 8), pady=3)
            return e

        def _combo(parent, row, col, values):
            cb = ctk.CTkComboBox(parent, values=values, height=30, corner_radius=7,
                                 fg_color="#F8FAFC", font=("Segoe UI", 10),
                                 dropdown_font=("Segoe UI", 10))
            cb.grid(row=row, column=col, sticky="ew", padx=(0, 8), pady=3)
            return cb

        _lbl(grid, "Patient", 0, 0)
        self.p_patient = _entry(grid, 0, 1, placeholder="Full name")
        _lbl(grid, "Age", 0, 2)
        self.p_age = _entry(grid, 0, 3, placeholder="e.g. 34")
        _lbl(grid, "Gender", 0, 4)
        self.p_gender = _combo(grid, 0, 5, GENDERS)
        _lbl(grid, "Doctor", 0, 6)
        self.p_doctor = _entry(grid, 0, 7, placeholder="Dr. …")

        _lbl(grid, "Date", 1, 0)
        self.p_date = _entry(grid, 1, 1, placeholder="YYYY-MM-DD")
        self.p_date.insert(0, datetime.now().strftime("%Y-%m-%d"))
        _lbl(grid, "Category", 1, 2)
        self.p_category = _combo(grid, 1, 3, [])

        # Multi-line notes.
        _lbl(grid, "Notes", 2, 0)
        self.p_notes = ctk.CTkTextbox(grid, height=60, corner_radius=7,
                                      fg_color="#F8FAFC", font=("Segoe UI", 10),
                                      border_width=1, border_color=BORDER)
        self.p_notes.grid(row=2, column=1, columnspan=7, sticky="ew",
                          padx=(0, 8), pady=3)

        # -- status + bottom bar --
        self.form_status = ctk.CTkLabel(p, text="Ready for a new prescription",
                                        text_color=MUTED, anchor="w")
        self.form_status.grid(row=2, column=0, sticky="ew", padx=20, pady=(0, 4))

        self.bottom_bar = ctk.CTkFrame(p, fg_color=BG, corner_radius=0)
        self.bottom_bar.grid(row=3, column=0, sticky="ew", padx=18, pady=(0, 12))
        self.bottom_bar.grid_columnconfigure(0, weight=1)
        self.bottom_bar.grid_columnconfigure(1, weight=0)
        self.cancel_btn = ctk.CTkButton(self.bottom_bar, text="Cancel", width=110,
                                        height=44, state="disabled",
                                        command=self._cancel_edit)
        self.cancel_btn.grid(row=0, column=0, sticky="e", padx=(0, 8))
        self.save_btn = ctk.CTkButton(self.bottom_bar, text="SAVE PRESCRIPTION",
                                      width=210, height=46,
                                      font=("Segoe UI", 13, "bold"), command=self._save)
        self.save_btn.grid(row=0, column=1, sticky="e")

        self._add_medication_card()
        self._refresh_categories()

    def _add_medication_card(self, data=None):
        card = MedicationCard(self.med_scroll, self, data, self._remove_medication_card)
        card.grid(row=len(self.medication_cards), column=0, sticky="ew", padx=4, pady=5)
        self.medication_cards.append(card)

    def _remove_medication_card(self, card):
        if len(self.medication_cards) <= 1:
            card.set_data({}); return
        self.medication_cards.remove(card); card.destroy()
        for i, item in enumerate(self.medication_cards):
            item.grid_configure(row=i)

    def _med_suggestions(self, text):
        """Prefix-first, then contains fallback, case-insensitive."""
        with connect() as conn:
            rows = conn.execute(
                "SELECT name FROM medications WHERE name LIKE ? COLLATE NOCASE "
                "ORDER BY name LIMIT 20", (f"{text}%",)).fetchall()
            if not rows:
                rows = conn.execute(
                    "SELECT name FROM medications WHERE name LIKE ? COLLATE NOCASE "
                    "ORDER BY name LIMIT 20", (f"%{text}%",)).fetchall()
        return [r[0] for r in rows]

    # ---------------- image ----------------
    def _choose_image(self):
        path = filedialog.askopenfilename(
            title="Choose prescription image",
            filetypes=[("Images", "*.png *.jpg *.jpeg *.bmp *.gif *.tif *.tiff *.webp"),
                       ("All files", "*.*")])
        if path:
            self.current_image_path = path
            self.current_image_dirty = True
            self.form_viewer.load(path)
            self.form_status.configure(text=f"Image selected: {Path(path).name}")

    def _remove_image(self):
        self.current_image_path = None
        self.current_image_dirty = True
        self.form_viewer.clear()
        self.form_status.configure(text="Image removed")

    def _open_fullscreen(self, path=None):
        """Open fullscreen viewer. If path is None, use current form image.

        FIX: this never mutates the form's image path, even when called with an
        explicit path (from the search page).
        """
        target = path or self.current_image_path
        if not target or not os.path.exists(target):
            messagebox.showinfo("No image", "No image is available."); return
        win = ctk.CTkToplevel(self); win.title("Prescription Image")
        win.geometry("1000x750"); win.minsize(700, 500); win.transient(self)
        win.grid_rowconfigure(0, weight=1); win.grid_columnconfigure(0, weight=1)
        viewer = ImageViewer(win, width=900, height=650)
        viewer.grid(row=0, column=0, sticky="nsew", padx=12, pady=12)
        viewer.load(target)
        bar = ctk.CTkFrame(win, corner_radius=12)
        bar.grid(row=1, column=0, sticky="ew", padx=12, pady=(0, 12))
        for txt, cmd in (("Zoom −", viewer.zoom_out), ("Fit", viewer.fit),
                         ("Zoom +", viewer.zoom_in), ("Rotate", viewer.rotate),
                         ("Close", win.destroy)):
            ctk.CTkButton(bar, text=txt, width=100, height=38,
                          command=cmd).pack(side="left", padx=5, pady=8)
        win.bind("<Escape>", lambda e: win.destroy())

    # ---------------- save / edit ----------------
    def _clear_form(self):
        if self._save_in_progress:
            return
        self.editing_id = None
        self.current_image_path = None
        self.current_image_dirty = False
        self.form_viewer.clear()
        for card in list(self.medication_cards):
            card.destroy()
        self.medication_cards.clear()
        self._add_medication_card()

        self.p_patient.delete(0, "end")
        self.p_age.delete(0, "end")
        self.p_gender.set("")
        self.p_doctor.delete(0, "end")
        self.p_date.delete(0, "end")
        self.p_date.insert(0, datetime.now().strftime("%Y-%m-%d"))
        with connect() as conn:
            row = conn.execute("SELECT name FROM categories ORDER BY name LIMIT 1").fetchone()
        self.p_category.set(row[0] if row else "General")
        self.p_notes.delete("1.0", "end")

        self.save_btn.configure(text="SAVE PRESCRIPTION", state="normal")
        self.cancel_btn.configure(state="disabled")
        self.form_status.configure(text="Ready for a new prescription")

    def _cancel_edit(self):
        self._clear_form()

    def _save(self):
        if self._save_in_progress:
            return

        rows = [r.get_data() for r in self.medication_cards if r.get_data()["name"]]
        if not rows:
            messagebox.showwarning("Missing Medicine",
                                    "Please enter at least one medicine name."); return
        if not self.editing_id and not self.current_image_path:
            messagebox.showwarning("Missing Image",
                                    "Please choose the prescription image."); return

        # ---- validate date & age ----
        date = self.p_date.get().strip() or datetime.now().strftime("%Y-%m-%d")
        if not valid_date(date):
            messagebox.showwarning("Invalid Date",
                                    "Date must be in YYYY-MM-DD format."); return
        age = self.p_age.get().strip()
        if not valid_age(age):
            messagebox.showwarning("Invalid Age",
                                    f"Age must be a whole number between 0 and {MAX_AGE}."); return

        # ---- similar names check ----
        names = [x["name"] for x in rows]
        for i in range(len(names)):
            for j in range(i + 1, len(names)):
                a, b = names[i].lower(), names[j].lower()
                if a != b and abs(len(a) - len(b)) <= 2 and levenshtein(a, b) <= 2:
                    if not messagebox.askyesno("Similar Medicine Names",
                        f"'{names[i]}' and '{names[j]}' look similar. Save anyway?"):
                        return

        # ---- capture state for the worker thread ----
        patient = self.p_patient.get().strip()
        gender = self.p_gender.get().strip()
        doctor = self.p_doctor.get().strip()
        category = self.p_category.get().strip() or "General"
        notes = self.p_notes.get("1.0", "end").strip()
        editing_id = self.editing_id
        image_source = self.current_image_path
        image_dirty = self.current_image_dirty

        # ---- lock UI ----
        self._save_in_progress = True
        self.save_btn.configure(state="disabled", text="SAVING…")
        self.cancel_btn.configure(state="disabled")
        self.form_status.configure(text="Saving, please wait…")

        threading.Thread(
            target=self._save_worker,
            args=(editing_id, image_source, image_dirty, rows,
                  patient, age, gender, doctor, date, category, notes),
            daemon=True,
        ).start()

    def _save_worker(self, editing_id, image_source, image_dirty, rows,
                     patient, age, gender, doctor, date, category, notes):
        new_image = None
        try:
            # 1) Handle image (slow part, hence the thread).
            image_rel = None
            if editing_id and not image_dirty:
                with connect() as conn:
                    r = conn.execute("SELECT image_path FROM prescriptions WHERE id=?",
                                     (editing_id,)).fetchone()
                    image_rel = r[0] if r else None
            elif image_source:
                new_name = f"{datetime.now():%Y%m%d_%H%M%S}_{uuid.uuid4().hex[:8]}.jpg"
                new_image = os.path.join(IMAGES_DIR, new_name)
                save_compressed_image(image_source, new_image)
                image_rel = os.path.relpath(new_image, BASE_DIR)

            # 2) Database work (creates its own connection → thread-safe).
            now = datetime.now().isoformat()
            old_image = None
            with connect() as conn:
                c = conn.cursor()
                if editing_id:
                    pid = editing_id
                    old = c.execute("SELECT image_path FROM prescriptions WHERE id=?",
                                    (pid,)).fetchone()
                    old_image = old[0] if old else None
                    c.execute("""UPDATE prescriptions SET patient_name=?,age=?,gender=?,
                                 doctor_name=?,date=?,category=?,notes=?,image_path=?,
                                 updated_at=? WHERE id=?""",
                              (patient, age, gender, doctor, date, category,
                               notes, image_rel, now, pid))
                    c.execute("DELETE FROM prescription_items WHERE prescription_id=?", (pid,))
                    action = "UPDATE"
                else:
                    c.execute("""INSERT INTO prescriptions
                        (patient_name,age,gender,doctor_name,date,category,notes,
                         image_path,created_at,updated_at) VALUES(?,?,?,?,?,?,?,?,?,?)""",
                              (patient, age, gender, doctor, date, category,
                               notes, image_rel, now, now))
                    pid = c.lastrowid
                    action = "CREATE"

                for r in rows:
                    normalized = " ".join(r["name"].split())
                    # Case-insensitive lookup (fixes Panadol/panadol duplication).
                    existing = c.execute(
                        "SELECT id FROM medications WHERE name = ? COLLATE NOCASE",
                        (normalized,)).fetchone()
                    if existing:
                        mid = existing[0]
                    else:
                        c.execute("INSERT INTO medications(name) VALUES(?)", (normalized,))
                        mid = c.lastrowid
                    c.execute("""INSERT INTO prescription_items
                        (prescription_id,medication_id,strength,dose,frequency,
                         duration,route,item_notes) VALUES(?,?,?,?,?,?,?,?)""",
                              (pid, mid, r["strength"], r["dose"], r["frequency"],
                               r["duration"], r["route"], r["item_notes"]))
                c.execute("""INSERT INTO audit_log(prescription_id,action,details,
                             created_at) VALUES(?,?,?,?)""",
                          (pid, action, json.dumps({"medicine_count": len(rows)}), now))

            # 3) Delete the old image file (only after a successful save).
            if old_image and old_image != image_rel:
                old_full = safe_path(old_image)
                if old_full and os.path.exists(old_full):
                    try: os.remove(old_full)
                    except OSError: pass

            # 4) Notify the main thread.
            self.after(0, lambda: self._save_succeeded(pid))

        except Exception as exc:
            # Clean up any half-written new image file.
            if new_image and os.path.exists(new_image):
                try: os.remove(new_image)
                except OSError: pass
            LOGGER.exception("Save failed")
            self.after(0, lambda e=exc: self._save_failed(e))

    def _save_succeeded(self, pid):
        self._save_in_progress = False
        messagebox.showinfo("Saved", f"Prescription #{pid} saved successfully.")
        self._clear_form()
        self._refresh_all()
        self._show_page("dashboard")

    def _save_failed(self, exc):
        self._save_in_progress = False
        self.save_btn.configure(state="normal", text="SAVE PRESCRIPTION")
        self.cancel_btn.configure(state="normal" if self.editing_id else "disabled")
        self.form_status.configure(text="Save failed")
        messagebox.showerror("Save Error", str(exc))

    def _edit_from_id(self, pid):
        with connect() as conn:
            row = conn.execute("SELECT * FROM prescriptions WHERE id=?", (pid,)).fetchone()
            items = conn.execute("""SELECT m.name,pi.strength,pi.dose,pi.frequency,
                pi.duration,pi.route,pi.item_notes FROM prescription_items pi
                JOIN medications m ON m.id=pi.medication_id
                WHERE pi.prescription_id=? ORDER BY pi.id""", (pid,)).fetchall()
        if not row: return
        self._show_page("form")
        self._clear_form()
        self.editing_id = pid
        self.current_image_dirty = False

        self.p_patient.delete(0, "end"); self.p_patient.insert(0, row["patient_name"] or "")
        self.p_age.delete(0, "end");     self.p_age.insert(0, row["age"] or "")
        self.p_gender.set(row["gender"] or "")
        self.p_doctor.delete(0, "end");  self.p_doctor.insert(0, row["doctor_name"] or "")
        self.p_date.delete(0, "end")
        self.p_date.insert(0, row["date"] or datetime.now().strftime("%Y-%m-%d"))
        if row["category"]:
            self.p_category.set(row["category"])
        self.p_notes.delete("1.0", "end")
        if row["notes"]:
            self.p_notes.insert("1.0", row["notes"])

        for card in list(self.medication_cards): card.destroy()
        self.medication_cards.clear()
        for item in items:
            self._add_medication_card({
                "name": item[0], "strength": item[1] or "", "dose": item[2] or "",
                "frequency": item[3] or "", "duration": item[4] or "",
                "route": item[5] or "", "item_notes": item[6] or ""})
        if not items:
            self._add_medication_card()
        if row["image_path"]:
            path = safe_path(row["image_path"])
            if path and os.path.exists(path):
                self.current_image_path = path
                self.form_viewer.load(path)
        self.save_btn.configure(text="UPDATE PRESCRIPTION")
        self.cancel_btn.configure(state="normal")
        self.form_status.configure(text=f"Editing prescription #{pid}")

    # ---------------- search ----------------
    def _page_search(self, p):
        p.grid_rowconfigure(2, weight=1)
        p.grid_columnconfigure(0, weight=1)
        self._header(p, "Search Archive",
                     "Find prescriptions by medicine, patient, doctor, category or date")

        filters = ctk.CTkFrame(p, corner_radius=14, fg_color=CARD,
                               border_width=1, border_color=BORDER)
        filters.grid(row=1, column=0, sticky="ew", padx=18, pady=6)
        for i in range(4):
            filters.grid_columnconfigure(i, weight=1 if i else 2)

        self.s_meds = self._filter_entry(filters, "Medicines (comma = ALL)", 0, 0)
        self.s_people = self._filter_entry(filters, "Patient / Doctor", 0, 1)
        self.s_category = self._filter_combo(filters, "Category",
                                              ["Any"] + DEFAULT_CATEGORIES, 0, 2)
        self.s_date_from = self._filter_entry(filters, "From date", 0, 3)
        self.s_date_to = self._filter_entry(filters, "To date", 1, 3)

        self.s_meds.bind("<Return>", lambda e: self._refresh_search())
        self.s_people.bind("<Return>", lambda e: self._refresh_search())

        # AND/OR toggle for multi-medicine search.
        self.s_or_mode = ctk.BooleanVar(value=False)
        ctk.CTkCheckBox(filters, text="Match ANY medicine (OR)",
                        variable=self.s_or_mode, font=("Segoe UI", 10),
                        checkbox_width=18, checkbox_height=18
                        ).grid(row=1, column=0, sticky="w", padx=12, pady=(0, 8))

        btns = ctk.CTkFrame(filters, fg_color="transparent")
        btns.grid(row=1, column=1, columnspan=2, sticky="w", padx=10, pady=8)
        ctk.CTkButton(btns, text="SEARCH", width=130, height=38,
                      font=("Segoe UI", 11, "bold"),
                      command=self._refresh_search).pack(side="left", padx=4)
        ctk.CTkButton(btns, text="Show All", width=110, height=38,
                      fg_color="#E5E7EB", hover_color="#D1D5DB", text_color=TEXT,
                      command=self._search_show_all).pack(side="left", padx=4)

        results = ctk.CTkFrame(p, fg_color="transparent")
        results.grid(row=2, column=0, sticky="nsew", padx=18, pady=8)
        results.grid_rowconfigure(0, weight=1)
        results.grid_columnconfigure(0, weight=3)
        results.grid_columnconfigure(1, weight=2, minsize=420)

        left = self._card(results, 0, 0)
        left.grid_rowconfigure(1, weight=1)
        left.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(left, text="Results", font=("Segoe UI", 15, "bold"),
                     text_color=TEXT).grid(row=0, column=0, sticky="w",
                                            padx=16, pady=(14, 8))
        self.search_scroll = ctk.CTkScrollableFrame(left, fg_color="#F8FAFC")
        self.search_scroll.grid(row=1, column=0, sticky="nsew", padx=10, pady=(0, 10))
        self.search_scroll.grid_columnconfigure(0, weight=1)

        right = self._card(results, 0, 1)
        right.grid_columnconfigure(0, weight=1)
        right.grid_rowconfigure(1, weight=1, minsize=120)
        right.grid_rowconfigure(2, weight=0, minsize=280)

        ctk.CTkLabel(right, text="Prescription Snapshot",
                     font=("Segoe UI", 15, "bold"), text_color=TEXT
                     ).grid(row=0, column=0, sticky="w", padx=16, pady=(14, 8))

        self.snapshot = ctk.CTkTextbox(right, height=140, corner_radius=10,
                                       fg_color="#F8FAFC", font=("Consolas", 10),
                                       wrap="word")
        self.snapshot.grid(row=1, column=0, sticky="nsew", padx=12, pady=6)

        self.search_viewer = ImageViewer(right, width=380, height=280)
        self.search_viewer.grid(row=2, column=0, sticky="nsew", padx=12, pady=6)

        actions = ctk.CTkFrame(right, fg_color="transparent")
        actions.grid(row=3, column=0, sticky="ew", padx=10, pady=8)
        ctk.CTkButton(actions, text="Edit", height=36,
                      command=self._edit_selected_search).pack(side="left", padx=3)
        ctk.CTkButton(actions, text="Move to Trash", height=36, fg_color="#FEF3C7",
                      hover_color="#FDE68A", text_color="#92400E",
                      command=self._trash_selected).pack(side="left", padx=3)
        ctk.CTkButton(actions, text="Fullscreen", height=36,
                      command=self._open_search_fullscreen).pack(side="left", padx=3)

    def _filter_entry(self, parent, label, row, col):
        box = ctk.CTkFrame(parent, fg_color="transparent")
        box.grid(row=row, column=col, sticky="ew", padx=8, pady=6)
        box.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(box, text=label, font=("Segoe UI", 10, "bold"),
                     text_color=MUTED).grid(row=0, column=0, sticky="w",
                                             padx=4, pady=(0, 3))
        e = ctk.CTkEntry(box, height=38, corner_radius=9,
                         placeholder_text=label, font=("Segoe UI", 11))
        e.grid(row=1, column=0, sticky="ew", padx=4)
        return e

    def _filter_combo(self, parent, label, values, row, col):
        box = ctk.CTkFrame(parent, fg_color="transparent")
        box.grid(row=row, column=col, sticky="ew", padx=8, pady=6)
        box.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(box, text=label, font=("Segoe UI", 10, "bold"),
                     text_color=MUTED).grid(row=0, column=0, sticky="w",
                                             padx=4, pady=(0, 3))
        cb = ctk.CTkComboBox(box, values=values, height=38, corner_radius=9,
                             font=("Segoe UI", 11), dropdown_font=("Segoe UI", 11))
        cb.set("Any"); cb.grid(row=1, column=0, sticky="ew", padx=4)
        return cb

    def _refresh_search(self):
        if not hasattr(self, "search_scroll"): return
        for w in self.search_scroll.winfo_children(): w.destroy()
        meds = self.s_meds.get().strip(); people = self.s_people.get().strip()
        cat = self.s_category.get().strip(); df = self.s_date_from.get().strip()
        dt = self.s_date_to.get().strip()
        terms = [x.strip() for x in meds.replace(";", ",").split(",") if x.strip()]
        or_mode = bool(self.s_or_mode.get())

        sql = ("SELECT DISTINCT p.id,p.patient_name,p.age,p.doctor_name,p.date,p.category "
               "FROM prescriptions p WHERE p.deleted_at IS NULL")
        params = []
        if terms:
            if or_mode:
                sub = " OR ".join("m.name LIKE ? COLLATE NOCASE" for _ in terms)
                sql += (" AND p.id IN (SELECT pi.prescription_id FROM prescription_items pi "
                        "JOIN medications m ON m.id=pi.medication_id WHERE " + sub + ")")
                for t in terms:
                    params.append(f"%{t}%")
            else:
                for t in terms:
                    sql += (" AND p.id IN (SELECT pi.prescription_id FROM prescription_items pi "
                            "JOIN medications m ON m.id=pi.medication_id "
                            "WHERE m.name LIKE ? COLLATE NOCASE)")
                    params.append(f"%{t}%")
        if people:
            sql += " AND (p.patient_name LIKE ? OR p.doctor_name LIKE ?)"
            params += [f"%{people}%", f"%{people}%"]
        if cat and cat != "Any":
            sql += " AND p.category=?"; params.append(cat)
        if df and valid_date(df):
            sql += " AND p.date>=?"; params.append(df)
        if dt and valid_date(dt):
            sql += " AND p.date<=?"; params.append(dt)
        sql += " ORDER BY p.date DESC,p.id DESC"

        with connect() as conn:
            rows = conn.execute(sql, params).fetchall()
            for r in rows:
                meds2 = [x[0] for x in conn.execute(
                    "SELECT m.name FROM prescription_items pi "
                    "JOIN medications m ON m.id=pi.medication_id "
                    "WHERE pi.prescription_id=? ORDER BY pi.id", (r["id"],)).fetchall()]
                self._result_card(r, meds2)
            if meds:
                conn.execute("INSERT INTO search_history(query,searched_at) VALUES(?,?)",
                             (meds, datetime.now().isoformat()))
        self.selected_search_id = None
        self._clear_snapshot()

    def _result_card(self, row, meds):
        card = ctk.CTkFrame(self.search_scroll, corner_radius=11, fg_color=CARD,
                            border_width=1, border_color=BORDER)
        card.grid(row=len(self.search_scroll.winfo_children()), column=0,
                  sticky="ew", padx=4, pady=4)
        card.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(card, text=f"#{row['id']}  •  {row['patient_name'] or 'Unnamed patient'}",
                     font=("Segoe UI", 12, "bold"), text_color=TEXT
                     ).grid(row=0, column=0, sticky="w", padx=12, pady=(10, 2))
        ctk.CTkLabel(card,
            text=f"{row['date'] or '-'}  |  {row['doctor_name'] or '-'}  |  "
                 f"{row['category'] or '-'}\n{', '.join(meds) or 'No medicines'}",
            font=("Segoe UI", 10), text_color=MUTED, justify="left"
            ).grid(row=1, column=0, sticky="w", padx=12, pady=(0, 10))
        card.bind("<Button-1>", lambda e, pid=row['id']: self._select_search(pid))
        for child in card.winfo_children():
            child.bind("<Button-1>", lambda e, pid=row['id']: self._select_search(pid))

    def _select_search(self, pid):
        self.selected_search_id = pid
        self._load_snapshot(pid)

    def _clear_snapshot(self):
        self.snapshot.configure(state="normal"); self.snapshot.delete("1.0", "end")
        self.snapshot.configure(state="disabled")
        self.search_viewer.clear()

    def _load_snapshot(self, pid):
        with connect() as conn:
            row = conn.execute("SELECT * FROM prescriptions WHERE id=?", (pid,)).fetchone()
            items = conn.execute("""SELECT m.name,pi.strength,pi.dose,pi.frequency,
                pi.duration,pi.route,pi.item_notes FROM prescription_items pi
                JOIN medications m ON m.id=pi.medication_id
                WHERE pi.prescription_id=? ORDER BY pi.id""", (pid,)).fetchall()
        if not row: return
        lines = [f"Prescription #{pid}", "-" * 55]
        for label, key in (("Patient", "patient_name"), ("Age", "age"),
                            ("Gender", "gender"), ("Doctor", "doctor_name"),
                            ("Date", "date"), ("Category", "category"),
                            ("Notes", "notes")):
            if row[key]: lines.append(f"{label}: {row[key]}")
        lines.append(""); lines.append("MEDICINES")
        for i, x in enumerate(items, 1):
            lines.append(f"{i}. {x[0]}")
            meta = [v for v in x[1:5] if v]
            if x[5]: meta.append("Route: " + x[5])
            if meta: lines.append("   " + " | ".join(meta))
            if x[6]: lines.append("   Note: " + x[6])
        self.snapshot.configure(state="normal"); self.snapshot.delete("1.0", "end")
        self.snapshot.insert("1.0", "\n".join(lines))
        self.snapshot.configure(state="disabled")

        path = safe_path(row["image_path"] or "")
        if path and os.path.exists(path):
            self.search_viewer.load(path)
        else:
            self.search_viewer.clear()

    def _edit_selected_search(self):
        if self.selected_search_id: self._edit_from_id(self.selected_search_id)
        else: messagebox.showinfo("Select", "Select a prescription first.")

    def _open_search_fullscreen(self):
        """FIX: pass the path directly; do not touch self.current_image_path."""
        if not self.selected_search_id:
            return
        with connect() as conn:
            r = conn.execute("SELECT image_path FROM prescriptions WHERE id=?",
                             (self.selected_search_id,)).fetchone()
        path = safe_path(r[0] if r else "")
        if path and os.path.exists(path):
            self._open_fullscreen(path)          # <-- path passed explicitly

    def _search_show_all(self):
        self.s_meds.delete(0, "end"); self.s_people.delete(0, "end")
        self.s_category.set("Any"); self.s_date_from.delete(0, "end")
        self.s_date_to.delete(0, "end"); self._refresh_search()

    # ---------------- trash ----------------
    def _page_trash(self, p):
        p.grid_rowconfigure(1, weight=1); p.grid_columnconfigure(0, weight=1)
        self._header(p, "Trash",
                     "Restore deleted prescriptions or permanently remove them")
        card = self._card(p, 1, 0)
        card.grid_rowconfigure(1, weight=1); card.grid_columnconfigure(0, weight=1)
        bar = ctk.CTkFrame(card, fg_color="transparent")
        bar.grid(row=0, column=0, sticky="ew", padx=14, pady=10)
        ctk.CTkButton(bar, text="Refresh", width=100, height=36,
                      command=self._refresh_trash).pack(side="left", padx=4)
        ctk.CTkButton(bar, text="Restore Selected", width=145, height=36,
                      command=self._restore_selected).pack(side="left", padx=4)
        ctk.CTkButton(bar, text="Delete Permanently", width=160, height=36,
                      fg_color="#FEE2E2", hover_color="#FECACA", text_color="#991B1B",
                      command=self._permanent_delete_selected).pack(side="left", padx=4)
        ctk.CTkButton(bar, text="Empty Trash", width=120, height=36,
                      fg_color="#FEE2E2", hover_color="#FECACA", text_color="#991B1B",
                      command=self._empty_trash).pack(side="right", padx=4)
        self.trash_scroll = ctk.CTkScrollableFrame(card, fg_color="#F8FAFC")
        self.trash_scroll.grid(row=1, column=0, sticky="nsew", padx=12, pady=(0, 12))
        self.trash_scroll.grid_columnconfigure(0, weight=1)

    def _refresh_trash(self):
        if not hasattr(self, "trash_scroll"): return
        for w in self.trash_scroll.winfo_children(): w.destroy()
        with connect() as conn:
            rows = conn.execute("SELECT * FROM prescriptions WHERE deleted_at IS NOT NULL "
                                "ORDER BY deleted_at DESC").fetchall()
            for r in rows:
                meds = [x[0] for x in conn.execute(
                    "SELECT m.name FROM prescription_items pi "
                    "JOIN medications m ON m.id=pi.medication_id "
                    "WHERE pi.prescription_id=?", (r['id'],)).fetchall()]
                card = ctk.CTkFrame(self.trash_scroll, corner_radius=11, fg_color=CARD,
                                    border_width=1, border_color=BORDER)
                card.grid(row=len(self.trash_scroll.winfo_children()), column=0,
                          sticky="ew", padx=4, pady=4)
                card.grid_columnconfigure(0, weight=1)
                ctk.CTkLabel(card, text=f"#{r['id']}  {r['patient_name'] or 'Unnamed'}",
                             font=("Segoe UI", 12, "bold"), text_color=TEXT
                             ).grid(row=0, column=0, sticky="w", padx=12, pady=(10, 2))
                ctk.CTkLabel(card,
                    text=f"Deleted: {(r['deleted_at'] or '')[:19].replace('T', ' ')}  |  "
                         f"{r['date'] or '-'}  |  {r['category'] or '-'}\n"
                         f"{', '.join(meds) or '-'}",
                    font=("Segoe UI", 10), text_color=MUTED, justify="left"
                    ).grid(row=1, column=0, sticky="w", padx=12, pady=(0, 10))
                ctk.CTkButton(card, text="Select", width=80, height=30,
                              command=lambda pid=r['id']: self._select_trash(pid)
                              ).grid(row=0, column=1, rowspan=2, padx=12)

    def _select_trash(self, pid): self.selected_trash_id = pid

    def _restore_selected(self):
        if not self.selected_trash_id:
            messagebox.showinfo("Select", "Select an item first."); return
        pid = self.selected_trash_id
        with connect() as conn:
            conn.execute("UPDATE prescriptions SET deleted_at=NULL,updated_at=? WHERE id=?",
                         (datetime.now().isoformat(), pid))
            conn.execute("INSERT INTO audit_log(prescription_id,action,details,created_at) "
                         "VALUES(?,?,?,?)", (pid, "RESTORE", "", datetime.now().isoformat()))
        self.selected_trash_id = None; self._refresh_all()

    def _permanent_delete_selected(self):
        if not self.selected_trash_id:
            messagebox.showinfo("Select", "Select an item first."); return
        if messagebox.askyesno("Confirm",
            "Permanently delete this prescription? This cannot be undone."):
            self._permanent_delete(self.selected_trash_id)
            self.selected_trash_id = None
            self._refresh_all()

    def _permanent_delete(self, pid):
        with connect() as conn:
            row = conn.execute("SELECT image_path FROM prescriptions WHERE id=?",
                               (pid,)).fetchone()
            img = safe_path(row[0] if row else "")
            conn.execute("DELETE FROM prescription_items WHERE prescription_id=?", (pid,))
            conn.execute("DELETE FROM prescriptions WHERE id=?", (pid,))
        if img and os.path.exists(img):
            try: os.remove(img)
            except OSError: pass

    def _empty_trash(self):
        with connect() as conn:
            rows = conn.execute("SELECT id FROM prescriptions WHERE deleted_at IS NOT NULL").fetchall()
        if not rows:
            messagebox.showinfo("Trash", "Trash is already empty."); return
        if not messagebox.askyesno("Confirm", f"Permanently delete {len(rows)} item(s)?"):
            return
        for r in rows: self._permanent_delete(r[0])
        self._refresh_all()

    def _trash_selected(self):
        if not self.selected_search_id:
            messagebox.showinfo("Select", "Select a prescription first."); return
        if not messagebox.askyesno("Confirm", "Move this prescription to Trash?"):
            return
        pid = self.selected_search_id
        with connect() as conn:
            conn.execute("UPDATE prescriptions SET deleted_at=?,updated_at=? WHERE id=?",
                         (datetime.now().isoformat(), datetime.now().isoformat(), pid))
            conn.execute("INSERT INTO audit_log(prescription_id,action,details,created_at) "
                         "VALUES(?,?,?,?)", (pid, "TRASH", "", datetime.now().isoformat()))
        self.selected_search_id = None; self._refresh_all()

    # ---------------- stats ----------------
    def _page_stats(self, p):
        p.grid_rowconfigure(1, weight=1); p.grid_columnconfigure(0, weight=1)
        self._header(p, "Statistics",
                     "Usage, medicine frequency and category breakdown")
        card = self._card(p, 1, 0)
        card.grid_rowconfigure(0, weight=1); card.grid_columnconfigure(0, weight=1)
        self.stats_box = ctk.CTkTextbox(card, corner_radius=12,
                                        fg_color="#F8FAFC", font=("Consolas", 11))
        self.stats_box.grid(row=0, column=0, sticky="nsew", padx=16, pady=16)

    def _refresh_stats(self):
        if not hasattr(self, "stats_box"): return
        with connect() as conn:
            total = conn.execute("SELECT COUNT(*) FROM prescriptions WHERE deleted_at IS NULL").fetchone()[0]
            meds = conn.execute("SELECT COUNT(*) FROM medications").fetchone()[0]
            trash = conn.execute("SELECT COUNT(*) FROM prescriptions WHERE deleted_at IS NOT NULL").fetchone()[0]
            month = conn.execute(
                "SELECT COUNT(*) FROM prescriptions WHERE deleted_at IS NULL AND date>=?",
                (datetime.now().replace(day=1).strftime("%Y-%m-%d"),)).fetchone()[0]
            top = conn.execute("""SELECT m.name,COUNT(pi.id) cnt FROM medications m
                JOIN prescription_items pi ON pi.medication_id=m.id
                JOIN prescriptions p ON p.id=pi.prescription_id
                WHERE p.deleted_at IS NULL
                GROUP BY m.id ORDER BY cnt DESC LIMIT 10""").fetchall()
            cats = conn.execute("""SELECT COALESCE(category,'(none)') cat,COUNT(*) cnt
                FROM prescriptions WHERE deleted_at IS NULL
                GROUP BY cat ORDER BY cnt DESC""").fetchall()
            searched = conn.execute("""SELECT query,COUNT(*) cnt FROM search_history
                GROUP BY query ORDER BY cnt DESC LIMIT 5""").fetchall()
        lines = ["MEDICAL PRESCRIPTION ARCHIVE", "=" * 62,
                 f"Active prescriptions : {total:,}",
                 f"Unique medicines     : {meds:,}",
                 f"In trash             : {trash:,}",
                 f"This month           : {month:,}", "", "TOP MEDICINES", "-" * 62]
        lines += [f"{r['name']:<40} {r['cnt']:>6}" for r in top] or ["(none)"]
        lines += ["", "BY CATEGORY", "-" * 62]
        lines += [f"{r['cat']:<40} {r['cnt']:>6}" for r in cats] or ["(none)"]
        lines += ["", "TOP SEARCHES", "-" * 62]
        lines += [f"{r['query']:<40} {r['cnt']:>6}" for r in searched] or ["(none)"]
        self.stats_box.configure(state="normal"); self.stats_box.delete("1.0", "end")
        self.stats_box.insert("1.0", "\n".join(lines))
        self.stats_box.configure(state="disabled")

    # ---------------- tools ----------------
    def _page_tools(self, p):
        p.grid_rowconfigure(1, weight=1); p.grid_columnconfigure(0, weight=1)
        self._header(p, "Tools & Settings",
                     "Backup, restore, categories and database health")
        body = ctk.CTkFrame(p, fg_color="transparent")
        body.grid(row=1, column=0, sticky="nsew", padx=18, pady=5)
        body.grid_columnconfigure(0, weight=1); body.grid_columnconfigure(1, weight=1)

        backup = self._card(body, 0, 0)
        ctk.CTkLabel(backup, text="Backup & Restore", font=("Segoe UI", 16, "bold"),
                     text_color=TEXT).pack(anchor="w", padx=18, pady=(18, 6))
        ctk.CTkButton(backup, text="Create Backup", height=42,
                      command=self._backup).pack(fill="x", padx=18, pady=6)
        ctk.CTkButton(backup, text="Restore Backup", height=42,
                      command=self._restore).pack(fill="x", padx=18, pady=6)
        ctk.CTkLabel(backup, text=f"Automatic backups: {BACKUPS_DIR}",
                     font=("Segoe UI", 9), text_color=MUTED,
                     wraplength=480, justify="left").pack(anchor="w", padx=18, pady=10)

        cats = self._card(body, 0, 1)
        ctk.CTkLabel(cats, text="Categories", font=("Segoe UI", 16, "bold"),
                     text_color=TEXT).pack(anchor="w", padx=18, pady=(18, 6))
        ctk.CTkButton(cats, text="Manage Categories", height=42,
                      command=self._manage_categories).pack(fill="x", padx=18, pady=6)
        ctk.CTkButton(cats, text="Database Health Check", height=42,
                      command=self._health_check).pack(fill="x", padx=18, pady=6)

        loc = self._card(body, 1, 0, colspan=2)
        ctk.CTkLabel(loc, text="Data Location", font=("Segoe UI", 16, "bold"),
                     text_color=TEXT).pack(anchor="w", padx=18, pady=(18, 6))
        ctk.CTkLabel(loc,
            text=f"Database: {DB_PATH}\nImages:   {IMAGES_DIR}\n"
                 f"Backups:  {BACKUPS_DIR}\nLogs:     {LOGS_DIR}",
            font=("Consolas", 10), text_color=MUTED, justify="left"
            ).pack(anchor="w", padx=18, pady=(0, 18))

    def _manage_categories(self):
        win = ctk.CTkToplevel(self); win.title("Manage Categories")
        win.geometry("520x520"); win.minsize(420, 420)
        win.transient(self); win.grab_set()
        win.grid_rowconfigure(1, weight=1); win.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(win, text="Categories", font=("Segoe UI", 18, "bold"),
                     text_color=TEXT).grid(row=0, column=0, sticky="w", padx=18, pady=18)
        lb = ctk.CTkScrollableFrame(win)
        lb.grid(row=1, column=0, sticky="nsew", padx=18, pady=6)
        lb.grid_columnconfigure(0, weight=1)
        entry = ctk.CTkEntry(win, height=40, placeholder_text="New category")
        entry.grid(row=2, column=0, sticky="ew", padx=18, pady=8)

        def reload():
            for w in lb.winfo_children(): w.destroy()
            with connect() as conn:
                cats = [r[0] for r in conn.execute("SELECT name FROM categories ORDER BY name")]
            for i, name in enumerate(cats):
                row = ctk.CTkFrame(lb, corner_radius=9, fg_color="#F8FAFC")
                row.grid(row=i, column=0, sticky="ew", padx=4, pady=4)
                row.grid_columnconfigure(0, weight=1)
                ctk.CTkLabel(row, text=name, font=("Segoe UI", 11, "bold")
                             ).grid(row=0, column=0, sticky="w", padx=10, pady=8)
                ctk.CTkButton(row, text="Rename", width=80, height=30,
                              command=lambda n=name: rename(n)
                              ).grid(row=0, column=1, padx=4)
                ctk.CTkButton(row, text="Delete", width=70, height=30,
                              fg_color="#FEE2E2", hover_color="#FECACA",
                              text_color="#991B1B",
                              command=lambda n=name: delete(n)
                              ).grid(row=0, column=2, padx=8)

        def add():
            name = entry.get().strip()
            if not name: return
            with connect() as conn:
                conn.execute("INSERT OR IGNORE INTO categories(name) VALUES(?)", (name,))
            entry.delete(0, "end"); reload(); self._refresh_categories()

        def rename(old):
            new = simpledialog.askstring("Rename", f"Rename '{old}' to:", parent=win)
            if not new or not new.strip(): return
            with connect() as conn:
                conn.execute("UPDATE categories SET name=? WHERE name=?", (new.strip(), old))
                conn.execute("UPDATE prescriptions SET category=? WHERE category=?",
                             (new.strip(), old))
            reload(); self._refresh_categories()

        def delete(name):
            if not messagebox.askyesno("Confirm", f"Delete category '{name}'?", parent=win):
                return
            with connect() as conn:
                conn.execute("DELETE FROM categories WHERE name=?", (name,))
                conn.execute("UPDATE prescriptions SET category='General' WHERE category=?",
                             (name,))
            reload(); self._refresh_categories()

        ctk.CTkButton(win, text="Add Category", height=40,
                      command=add).grid(row=3, column=0, sticky="ew", padx=18, pady=8)
        reload()

    def _health_check(self):
        ok, msg = integrity_check()
        with connect() as conn:
            orphan = conn.execute(
                "SELECT COUNT(*) FROM prescription_items pi "
                "LEFT JOIN prescriptions p ON p.id=pi.prescription_id "
                "WHERE p.id IS NULL").fetchone()[0]
            missing = 0
            for (path,) in conn.execute("SELECT image_path FROM prescriptions "
                                         "WHERE image_path IS NOT NULL"):
                if not safe_path(path) or not os.path.exists(safe_path(path)):
                    missing += 1
        messagebox.showinfo("Database Health",
            f"Integrity: {'OK' if ok else 'FAILED'}\n{msg}\n\n"
            f"Orphan items: {orphan}\nMissing images: {missing}")

    # ---------------- backup / restore (WAL-safe) ----------------
    def _backup(self, auto=False):
        if auto:
            target = os.path.join(BACKUPS_DIR,
                f"auto_backup_{datetime.now():%Y%m%d_%H%M%S}.zip")
        else:
            target = filedialog.asksaveasfilename(
                title="Save Backup As", defaultextension=".zip",
                initialfile=f"PrescriptionBackup_{datetime.now():%Y-%m-%d_%H%M%S}.zip",
                filetypes=[("ZIP archive", "*.zip")])
            if not target: return

        ok, msg = integrity_check()
        if not ok and not auto:
            messagebox.showerror("Backup",
                "Database integrity check failed:\n" + msg); return
        try:
            # FIX: flush WAL into the main file so a file-copy is complete.
            checkpoint_wal()

            with zipfile.ZipFile(target, "w", zipfile.ZIP_DEFLATED) as z:
                if os.path.exists(DB_PATH):
                    z.write(DB_PATH, "data/prescriptions.db")
                manifest = {"app_version": APP_VERSION, "schema_version": SCHEMA_VERSION,
                            "created_at": datetime.now().isoformat()}
                z.writestr("manifest.json", json.dumps(manifest, indent=2))
                for root, _, files in os.walk(IMAGES_DIR):
                    for f in files:
                        z.write(os.path.join(root, f),
                                os.path.relpath(os.path.join(root, f), BASE_DIR))
            if auto:
                self._prune_backups()
            else:
                messagebox.showinfo("Backup", f"Backup created successfully.\n\n{target}")
        except Exception as exc:
            messagebox.showerror("Backup Error", str(exc))
            LOGGER.exception("Backup failed")

    def _prune_backups(self):
        files = sorted(Path(BACKUPS_DIR).glob("auto_backup_*.zip"))
        while len(files) > AUTO_BACKUP_KEEP:
            try: files.pop(0).unlink()
            except OSError: pass

    def _remove_wal_side_files(self, db_path):
        """Remove -wal/-shm side files so a fresh DB can be installed cleanly."""
        for suffix in ("-wal", "-shm"):
            side = db_path + suffix
            if os.path.exists(side):
                try:
                    os.remove(side)
                except OSError:
                    pass

    def _restore(self):
        path = filedialog.askopenfilename(title="Choose backup",
                                          filetypes=[("ZIP archive", "*.zip")])
        if not path: return
        if not messagebox.askyesno("Confirm",
            "Restore will replace the current database and images. "
            "A safety backup will be created first. Continue?"): return
        self._backup(auto=True)
        try:
            with tempfile.TemporaryDirectory() as tmp:
                with zipfile.ZipFile(path, "r") as z:
                    for info in z.infolist():
                        dest = Path(tmp) / info.filename
                        if not str(dest.resolve()).startswith(str(Path(tmp).resolve())):
                            raise ValueError("Unsafe backup path")
                    z.extractall(tmp)
                db_src = Path(tmp) / "data" / "prescriptions.db"
                if not db_src.exists():
                    raise ValueError("Invalid backup: missing database")
                ok, msg = integrity_check(str(db_src))
                if not ok:
                    raise ValueError("Backup database failed integrity check: " + msg)

                # FIX: remove WAL/shm before swapping the DB.
                if os.path.exists(DB_PATH):
                    os.remove(DB_PATH)
                self._remove_wal_side_files(DB_PATH)
                shutil.copy2(db_src, DB_PATH)

                img_src = Path(tmp) / "data" / "images"
                if img_src.exists():
                    for f in Path(IMAGES_DIR).glob("*"):
                        if f.is_file():
                            try: f.unlink()
                            except OSError: pass
                    for f in img_src.iterdir():
                        if f.is_file():
                            shutil.copy2(f, Path(IMAGES_DIR) / f.name)

            init_db(); self._refresh_all(); self._clear_form()
            messagebox.showinfo("Restore", "Backup restored successfully.")
        except Exception as exc:
            messagebox.showerror("Restore Error", str(exc))
            LOGGER.exception("Restore failed")

    # ---------------- shared ----------------
    def _refresh_categories(self):
        with connect() as conn:
            cats = [r[0] for r in conn.execute("SELECT name FROM categories ORDER BY name")]
        if hasattr(self, "p_category"):
            self.p_category.configure(values=cats)
            current = self.p_category.get()
            if current not in cats:
                self.p_category.set(cats[0] if cats else "General")
        if hasattr(self, "s_category"):
            self.s_category.configure(values=["Any"] + cats)

    def _refresh_all(self):
        self._refresh_categories(); self._refresh_dashboard()
        self._refresh_search(); self._refresh_trash(); self._refresh_stats()

    def _bind_shortcuts(self):
        self.bind("<Control-s>", lambda e: self._save())
        self.bind("<Control-n>", lambda e: self._clear_form())
        self.bind("<Control-f>", lambda e: self._show_page("search"))
        self.bind("<Escape>", lambda e: self._clear_form())

    def _on_close(self):
        # Avoid overlapping with an in-flight save.
        if self._save_in_progress:
            if not messagebox.askyesno("Save in progress",
                "A save is still running. Quit anyway?"):
                return
        try:
            self._backup(auto=True)
        except Exception:
            LOGGER.exception("Auto-backup on close failed")
        self.destroy()


def main():
    app = PrescriptionApp()
    app.mainloop()


if __name__ == "__main__":
    main()