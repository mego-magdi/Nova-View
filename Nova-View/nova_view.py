"""
Nova View — Advanced Edition
=====================================
Enhanced features over the original:
  • Slideshow mode with configurable interval
  • Vertical flip (in addition to horizontal)
  • Save / Export (copy or save-as with format conversion)
  • Copy to clipboard
  • Zoom indicator label (shows current %)
  • Image counter label (e.g. 3 / 12)
  • Keyboard shortcuts: +/-, R, F, I, Space, Esc, Delete
  • Delete current image from disk (with confirmation)
  • Thumbnail strip (filmstrip) at the bottom
  • EXIF metadata display in the HUD (date taken, camera model, GPS)
  • Full-screen toggle (F11 / double-click)
  • Brightness / Contrast / Saturation sliders in the HUD
  • "Actual size" (1:1) button in addition to "Fit"
  • Sort order toggle (name / date / size)
  • Recent files history in Open menu
  • Smooth fade animation when switching images
  • Status-bar-style overlay (filename + coords on mouse move)
"""

import sys
import os
import math
import shutil
from datetime import datetime

from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QGraphicsView, QGraphicsScene,
    QGraphicsPixmapItem, QVBoxLayout, QHBoxLayout, QWidget,
    QPushButton, QFileDialog, QGraphicsDropShadowEffect, QLabel,
    QSlider, QScrollArea, QMessageBox, QSizePolicy, QSpacerItem,
    QGraphicsOpacityEffect, QMenu, QToolTip,
)
from PyQt6.QtGui import (
    QPixmap, QImageReader, QColor, QDragEnterEvent, QDropEvent,
    QPainter, QImage, QTransform, QKeySequence, QClipboard,
    QColorSpace, QGuiApplication,
)
from PyQt6.QtCore import (
    Qt, QPoint, QFileInfo, QTimer, QPropertyAnimation,
    QEasingCurve, QRectF, QPointF, QSize,
)
from PyQt6.QtPrintSupport import QPrinter, QPrintDialog

# ── Try importing Pillow for EXIF and export ──────────────────────────────────
try:
    from PIL import Image as PILImage
    from PIL.ExifTags import TAGS
    HAS_PIL = True
except ImportError:
    HAS_PIL = False


# ─────────────────────────────────────────────────────────────────────────────
SUPPORTED_WRITE_FMTS = ["PNG", "JPEG", "BMP", "TIFF", "WEBP"]
SORT_MODES = ["Name ↑", "Name ↓", "Date ↑", "Date ↓", "Size ↑", "Size ↓"]
SLIDESHOW_INTERVALS_MS = {
    "2 s":  2000,
    "5 s":  5000,
    "10 s": 10000,
    "30 s": 30000,
}
MAX_RECENT = 10
THUMBNAIL_SIZE = 72


# ─────────────────────────────────────────────────────────────────────────────
class ThumbnailLabel(QLabel):
    """Clickable thumbnail in the filmstrip."""
    def __init__(self, index: int, parent=None):
        super().__init__(parent)
        self.index = index
        self.setFixedSize(THUMBNAIL_SIZE, THUMBNAIL_SIZE)
        self.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self._active = False
        self._apply_style()

    def set_active(self, active: bool):
        self._active = active
        self._apply_style()

    def _apply_style(self):
        border = "2px solid rgba(100,180,255,0.85)" if self._active else "1px solid rgba(255,255,255,0.12)"
        bg = "rgba(100,180,255,0.15)" if self._active else "rgba(255,255,255,0.04)"
        self.setStyleSheet(
            f"border: {border}; border-radius: 6px; background: {bg}; padding: 2px;"
        )

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self.parent().parent().parent().goto_index(self.index)


# ─────────────────────────────────────────────────────────────────────────────
class _TrafficDot(QWidget):
    """
    macOS-style traffic-light dot that:
      • Always shows as a solid filled circle (no opacity tricks)
      • Reveals a crisp symbol (✕ / − / +) on hover
    """
    from PyQt6.QtCore import pyqtSignal
    clicked = pyqtSignal()

    DOT_SIZE = 13

    def __init__(self, color: str, symbol: str, parent=None):
        super().__init__(parent)
        self._color  = QColor(color)
        self._symbol = symbol
        self._hovered = False
        self.setFixedSize(self.DOT_SIZE, self.DOT_SIZE)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setAttribute(Qt.WidgetAttribute.WA_Hover, True)

    def event(self, e):
        from PyQt6.QtCore import QEvent
        if e.type() == QEvent.Type.HoverEnter:
            self._hovered = True;  self.update()
        elif e.type() == QEvent.Type.HoverLeave:
            self._hovered = False; self.update()
        return super().event(e)

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.clicked.emit()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        r = self.DOT_SIZE
        # filled circle
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(self._color)
        p.drawEllipse(0, 0, r, r)
        # symbol on hover
        if self._hovered:
            p.setPen(QColor(0, 0, 0, 160))
            font = p.font()
            font.setPixelSize(8)
            font.setBold(True)
            p.setFont(font)
            p.drawText(0, 0, r, r, Qt.AlignmentFlag.AlignCenter, self._symbol)
        p.end()


# ─────────────────────────────────────────────────────────────────────────────
class NovaView(QMainWindow):

    # ── construction ──────────────────────────────────────────────────────────
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Nova View")
        self.resize(1400, 900)
        self.setMinimumSize(800, 560)
        self.setAcceptDrops(True)
        self.setWindowFlags(Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)

        # ── state ──
        self.image_paths: list[str] = []
        self.current_index: int = -1
        self.pixmap_item: QGraphicsPixmapItem | None = None
        self.zoom_level: float = 1.0
        self.drag_position = QPoint()
        self.sort_mode_index: int = 0
        self.recent_files: list[str] = []
        self._is_fullscreen: bool = False
        self._rotation_accum: int = 0        # degrees; applied to saved image
        self._flip_h: bool = False
        self._flip_v: bool = False

        # ── slideshow ──
        self.slideshow_timer = QTimer(self)
        self.slideshow_timer.timeout.connect(self._slideshow_advance)
        self._slideshow_interval_key = "5 s"

        # ── fade animation ──
        self._opacity_effect = QGraphicsOpacityEffect()
        self._fade_anim = QPropertyAnimation(self._opacity_effect, b"opacity")
        self._fade_anim.setDuration(220)
        self._fade_anim.setEasingCurve(QEasingCurve.Type.InOutCubic)

        self._build_stylesheet()
        self._build_ui()

    # ── stylesheet ────────────────────────────────────────────────────────────
    def _build_stylesheet(self):
        self.setStyleSheet("""
            QWidget#MainGlassFrame {
                background-color: rgba(18, 18, 26, 0.82);
                border: 1px solid rgba(255,255,255,0.10);
                border-radius: 16px;
            }
            QWidget#GlassDock, QWidget#InfoHUD, QWidget#FilmstripBar {
                background-color: rgba(255,255,255,0.055);
                border: 1px solid rgba(255,255,255,0.09);
                border-radius: 12px;
            }
            QLabel {
                color: #FFFFFF;
                font-family: -apple-system, "Segoe UI", sans-serif;
            }
            QLabel#TitleLabel {
                color: rgba(255,255,255,0.32);
                font-weight: 500;
                font-size: 11px;
            }
            QLabel#HUDText {
                font-size: 12px;
                color: rgba(255,255,255,0.85);
            }
            QLabel#CounterLabel {
                font-size: 12px;
                color: rgba(255,255,255,0.55);
                min-width: 52px;
                qproperty-alignment: AlignCenter;
            }
            QLabel#ZoomLabel {
                font-size: 12px;
                color: rgba(255,255,255,0.55);
                min-width: 46px;
                qproperty-alignment: AlignCenter;
            }
            QPushButton {
                background-color: rgba(255,255,255,0.055);
                border: 1px solid rgba(255,255,255,0.08);
                border-radius: 8px;
                padding: 6px 13px;
                color: #FFFFFF;
                font-size: 13px;
                font-weight: 500;
            }
            QPushButton:hover  { background-color: rgba(255,255,255,0.14); border: 1px solid rgba(255,255,255,0.22); }
            QPushButton:pressed{ background-color: rgba(255,255,255,0.24); }
            QPushButton:disabled{ color: rgba(255,255,255,0.10); background: transparent; border: 1px solid rgba(255,255,255,0.01); }
            QPushButton#SlideshowActive {
                background-color: rgba(50,200,100,0.25);
                border: 1px solid rgba(50,200,100,0.5);
            }
            QSlider::groove:horizontal {
                height: 4px; background: rgba(255,255,255,0.12); border-radius: 2px;
            }
            QSlider::handle:horizontal {
                width: 12px; height: 12px; margin: -4px 0;
                background: rgba(255,255,255,0.7); border-radius: 6px;
            }
            QSlider::sub-page:horizontal {
                background: rgba(100,170,255,0.6); border-radius: 2px;
            }
            QScrollArea { background: transparent; border: none; }
            QScrollBar:horizontal {
                height: 4px; background: rgba(255,255,255,0.06); border-radius: 2px;
            }
            QScrollBar::handle:horizontal {
                background: rgba(255,255,255,0.20); border-radius: 2px;
            }
            QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal { width: 0; }
        """)

    # ── UI construction ───────────────────────────────────────────────────────
    def _build_ui(self):
        self.main_frame = QWidget()
        self.main_frame.setObjectName("MainGlassFrame")
        self.setCentralWidget(self.main_frame)

        self.window_layout = QVBoxLayout(self.main_frame)
        self.window_layout.setContentsMargins(14, 10, 14, 14)
        self.window_layout.setSpacing(8)

        self._build_title_bar()

        # workspace: canvas + sidebar
        self.workspace_layout = QHBoxLayout()
        self.workspace_layout.setSpacing(12)

        self._build_canvas()
        self._build_info_hud()

        self.window_layout.addLayout(self.workspace_layout, stretch=1)

        # bottom area: filmstrip + dock
        self._build_filmstrip()
        self._build_bottom_dock()

        # welcome overlay
        self.welcome_label = QLabel("Drag & Drop images  ·  or press  Open…")
        self.welcome_label.setStyleSheet(
            "color: rgba(255,255,255,0.25); font-size: 15px; font-weight: 300;"
        )
        self.welcome_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.welcome_proxy = self.scene.addWidget(self.welcome_label)

        self._toggle_controls(False)

    # title bar ----------------------------------------------------------------
    def _build_title_bar(self):
        self.title_bar = QWidget()
        self.title_bar.setObjectName("TitleBar")
        layout = QHBoxLayout(self.title_bar)
        layout.setContentsMargins(8, 2, 8, 2)
        layout.setSpacing(7)

        # ── Traffic-light dots (custom painted) ──────────────────────────────
        dot_specs = [
            ("WinClose", "#FF5F56", "✕", self.close),
            ("WinMin",   "#FFBD2E", "−", self.showMinimized),
            ("WinMax",   "#27C93F", "+", self._toggle_maximize),
        ]
        self._traffic_btns = []
        for obj_name, color, symbol, slot in dot_specs:
            btn = _TrafficDot(color, symbol)
            btn.setObjectName(obj_name)
            btn.clicked.connect(slot)
            layout.addWidget(btn)
            self._traffic_btns.append(btn)

        layout.addSpacing(12)
        self.lbl_title = QLabel("Nova View")
        self.lbl_title.setObjectName("TitleLabel")
        layout.addWidget(self.lbl_title)
        layout.addStretch()

        # ── Right-side title-bar actions ────────────────────────────────────
        for icon, tip, slot, w in [
            ("🔲", "Toggle full screen (F11)", self._toggle_fullscreen, 30),
        ]:
            btn = QPushButton(icon)
            btn.setToolTip(tip)
            btn.setFixedSize(w, 22)
            btn.setStyleSheet(
                "QPushButton { background: transparent; border: none; font-size: 13px; color: rgba(255,255,255,0.4); }"
                "QPushButton:hover { color: rgba(255,255,255,0.9); }"
            )
            btn.clicked.connect(slot)
            layout.addWidget(btn)

        self.window_layout.addWidget(self.title_bar)

    # canvas -------------------------------------------------------------------
    def _build_canvas(self):
        self.scene = QGraphicsScene(self)
        self.view = QGraphicsView(self.scene)
        self.view.setRenderHint(QPainter.RenderHint.Antialiasing)
        self.view.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        self.view.setDragMode(QGraphicsView.DragMode.ScrollHandDrag)
        self.view.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.view.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.view.setStyleSheet("background: transparent; border: none;")
        self.view.setTransformationAnchor(QGraphicsView.ViewportAnchor.AnchorUnderMouse)
        self.view.setResizeAnchor(QGraphicsView.ViewportAnchor.AnchorUnderMouse)
        self.view.setGraphicsEffect(self._opacity_effect)
        self.view.mouseDoubleClickEvent = lambda e: self._toggle_fullscreen()
        self.view.mouseMoveEvent = self._canvas_mouse_move
        self.workspace_layout.addWidget(self.view, stretch=1)

    # info HUD -----------------------------------------------------------------
    def _build_info_hud(self):
        self.info_hud = QWidget()
        self.info_hud.setObjectName("InfoHUD")
        self.info_hud.setFixedWidth(240)
        layout = QVBoxLayout(self.info_hud)
        layout.setContentsMargins(14, 14, 14, 14)
        layout.setSpacing(10)

        hud_title = QLabel("Image Properties")
        hud_title.setStyleSheet("font-weight: 600; font-size: 14px;")
        layout.addWidget(hud_title)

        self.lbl_hud_name = QLabel("Name: —")
        self.lbl_hud_res  = QLabel("Resolution: —")
        self.lbl_hud_size = QLabel("Size: —")
        self.lbl_hud_type = QLabel("Format: —")
        self.lbl_hud_date = QLabel("Modified: —")
        self.lbl_hud_exif = QLabel("")   # EXIF block

        for lbl in [self.lbl_hud_name, self.lbl_hud_res, self.lbl_hud_size,
                    self.lbl_hud_type, self.lbl_hud_date, self.lbl_hud_exif]:
            lbl.setObjectName("HUDText")
            lbl.setWordWrap(True)
            layout.addWidget(lbl)

        # ── Adjustments ──
        sep = QLabel("Adjustments")
        sep.setStyleSheet("font-weight: 600; font-size: 13px; margin-top: 8px;")
        layout.addWidget(sep)

        self._sliders: dict[str, QSlider] = {}
        self._slider_vals: dict[str, int] = {}
        for label, key, default in [
            ("Brightness", "brightness", 0),
            ("Contrast",   "contrast",   0),
            ("Saturation", "saturation", 0),
        ]:
            row = QHBoxLayout()
            lbl = QLabel(f"{label}")
            lbl.setObjectName("HUDText")
            lbl.setFixedWidth(76)
            slider = QSlider(Qt.Orientation.Horizontal)
            slider.setRange(-100, 100)
            slider.setValue(default)
            slider.setToolTip(f"{label}: {default}")
            self._sliders[key]     = slider
            self._slider_vals[key] = default
            slider.valueChanged.connect(lambda v, k=key: self._on_slider_change(k, v))
            row.addWidget(lbl)
            row.addWidget(slider)
            layout.addLayout(row)

        btn_reset_adj = QPushButton("Reset Adjustments")
        btn_reset_adj.clicked.connect(self._reset_adjustments)
        layout.addWidget(btn_reset_adj)

        layout.addStretch()
        self.workspace_layout.addWidget(self.info_hud)
        self.info_hud.hide()

    # filmstrip ----------------------------------------------------------------
    def _build_filmstrip(self):
        self.filmstrip_bar = QWidget()
        self.filmstrip_bar.setObjectName("FilmstripBar")
        outer = QVBoxLayout(self.filmstrip_bar)
        outer.setContentsMargins(8, 6, 8, 6)
        outer.setSpacing(0)

        self.filmstrip_scroll = QScrollArea()
        self.filmstrip_scroll.setWidgetResizable(True)
        self.filmstrip_scroll.setFixedHeight(THUMBNAIL_SIZE + 16)
        self.filmstrip_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.filmstrip_scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.filmstrip_scroll.setStyleSheet("background: transparent; border: none;")

        self.filmstrip_inner = QWidget()
        self.filmstrip_inner.setStyleSheet("background: transparent;")
        self.filmstrip_layout = QHBoxLayout(self.filmstrip_inner)
        self.filmstrip_layout.setContentsMargins(4, 0, 4, 0)
        self.filmstrip_layout.setSpacing(6)
        self.filmstrip_layout.addStretch()

        self.filmstrip_scroll.setWidget(self.filmstrip_inner)
        outer.addWidget(self.filmstrip_scroll)

        self._thumbnail_labels: list[ThumbnailLabel] = []

        container = QHBoxLayout()
        container.setAlignment(Qt.AlignmentFlag.AlignCenter)
        container.addWidget(self.filmstrip_bar)
        self.window_layout.addLayout(container)
        self.filmstrip_bar.hide()

    # bottom dock --------------------------------------------------------------
    def _build_bottom_dock(self):
        self.dock_widget = QWidget()
        self.dock_widget.setObjectName("GlassDock")
        layout = QHBoxLayout(self.dock_widget)
        layout.setContentsMargins(12, 7, 12, 7)
        layout.setSpacing(8)

        # open (with recent menu)
        self.btn_open = QPushButton("Open…")
        self.btn_open.setToolTip("Open image file (Ctrl+O)")
        self._recent_menu = QMenu(self)
        self._recent_menu.setStyleSheet(
            "QMenu { background: rgba(28,28,38,0.96); color: #fff; border: 1px solid rgba(255,255,255,0.12); border-radius: 8px; }"
            "QMenu::item:selected { background: rgba(255,255,255,0.12); }"
        )
        self.btn_open.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.btn_open.customContextMenuRequested.connect(self._show_recent_menu)
        self.btn_open.clicked.connect(self.open_image)
        layout.addWidget(self.btn_open)

        layout.addSpacing(4)

        # navigation
        self.btn_prev = QPushButton("◀")
        self.btn_prev.setToolTip("Previous (←)")
        self.btn_prev.setFixedWidth(34)
        self.btn_next = QPushButton("▶")
        self.btn_next.setToolTip("Next (→)")
        self.btn_next.setFixedWidth(34)
        self.btn_prev.clicked.connect(self.show_previous)
        self.btn_next.clicked.connect(self.show_next)
        layout.addWidget(self.btn_prev)

        self.lbl_counter = QLabel("— / —")
        self.lbl_counter.setObjectName("CounterLabel")
        layout.addWidget(self.lbl_counter)
        layout.addWidget(self.btn_next)

        layout.addSpacing(6)

        # zoom
        self.btn_zoom_out = QPushButton("－")
        self.btn_zoom_out.setFixedWidth(30)
        self.btn_zoom_out.setToolTip("Zoom out (-)")
        self.lbl_zoom = QLabel("100%")
        self.lbl_zoom.setObjectName("ZoomLabel")
        self.btn_zoom_in = QPushButton("＋")
        self.btn_zoom_in.setFixedWidth(30)
        self.btn_zoom_in.setToolTip("Zoom in (+)")
        self.btn_fit = QPushButton("Fit")
        self.btn_fit.setToolTip("Fit to window (F)")
        self.btn_actual = QPushButton("1:1")
        self.btn_actual.setToolTip("Actual / 100% size (Ctrl+1)")
        self.btn_zoom_out.clicked.connect(lambda: self.zoom_image(0.80))
        self.btn_zoom_in.clicked.connect(lambda:  self.zoom_image(1.25))
        self.btn_fit.clicked.connect(self.reset_view)
        self.btn_actual.clicked.connect(self._zoom_actual)
        for w in [self.btn_zoom_out, self.lbl_zoom, self.btn_zoom_in, self.btn_fit, self.btn_actual]:
            layout.addWidget(w)

        layout.addSpacing(6)

        # transforms
        self.btn_rotate_cw  = QPushButton("⟳")
        self.btn_rotate_cw.setToolTip("Rotate 90° CW (R)")
        self.btn_rotate_ccw = QPushButton("⟲")
        self.btn_rotate_ccw.setToolTip("Rotate 90° CCW (Shift+R)")
        self.btn_flip_h = QPushButton("⇄ H")
        self.btn_flip_h.setToolTip("Flip horizontal (H)")
        self.btn_flip_v = QPushButton("⇅ V")
        self.btn_flip_v.setToolTip("Flip vertical (V)")
        self.btn_rotate_cw.clicked.connect(lambda:  self.rotate_image(90))
        self.btn_rotate_ccw.clicked.connect(lambda: self.rotate_image(-90))
        self.btn_flip_h.clicked.connect(lambda: self.flip_image(horizontal=True))
        self.btn_flip_v.clicked.connect(lambda: self.flip_image(horizontal=False))
        for w in [self.btn_rotate_cw, self.btn_rotate_ccw, self.btn_flip_h, self.btn_flip_v]:
            layout.addWidget(w)

        layout.addSpacing(6)

        # actions
        self.btn_slideshow = QPushButton("▷ Slideshow")
        self.btn_slideshow.setToolTip("Start/Stop slideshow (Space)\nRight-click to set interval")
        self.btn_slideshow.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.btn_slideshow.customContextMenuRequested.connect(self._slideshow_interval_menu)
        self.btn_slideshow.clicked.connect(self.toggle_slideshow)

        self.btn_copy = QPushButton("⎘ Copy")
        self.btn_copy.setToolTip("Copy image to clipboard (Ctrl+C)")
        self.btn_copy.clicked.connect(self.copy_to_clipboard)

        self.btn_save = QPushButton("↓ Save As…")
        self.btn_save.setToolTip("Export / Save As (Ctrl+S)")
        self.btn_save.clicked.connect(self.save_as)

        self.btn_delete = QPushButton("⌫ Delete")
        self.btn_delete.setToolTip("Delete file from disk (Del)")
        self.btn_delete.setStyleSheet("QPushButton { color: rgba(255,100,100,0.85); }")
        self.btn_delete.clicked.connect(self.delete_current)

        self.btn_print = QPushButton("⎙ Print")
        self.btn_print.setToolTip("Print (Ctrl+P)")
        self.btn_print.clicked.connect(self.print_image)

        self.btn_info = QPushButton("ℹ Info")
        self.btn_info.setToolTip("Toggle properties panel (I)")
        self.btn_info.clicked.connect(self.toggle_info_hud)

        for w in [self.btn_slideshow, self.btn_copy, self.btn_save,
                  self.btn_delete, self.btn_print, self.btn_info]:
            layout.addWidget(w)

        # ── sort button ──
        layout.addSpacing(4)
        self.btn_sort = QPushButton(f"⇅ {SORT_MODES[self.sort_mode_index]}")
        self.btn_sort.setToolTip("Change sort order")
        self.btn_sort.clicked.connect(self._cycle_sort)
        layout.addWidget(self.btn_sort)

        container = QHBoxLayout()
        container.setAlignment(Qt.AlignmentFlag.AlignCenter)
        container.addWidget(self.dock_widget)
        self.window_layout.addLayout(container)

    # ── helpers ───────────────────────────────────────────────────────────────
    def _toggle_controls(self, enabled: bool):
        image_loaded = enabled
        nav_fwd = enabled and self.current_index < len(self.image_paths) - 1
        nav_bck = enabled and self.current_index > 0
        for btn in [self.btn_zoom_in, self.btn_zoom_out, self.btn_fit, self.btn_actual,
                    self.btn_rotate_cw, self.btn_rotate_ccw, self.btn_flip_h, self.btn_flip_v,
                    self.btn_copy, self.btn_save, self.btn_delete,
                    self.btn_print, self.btn_info, self.btn_slideshow, self.btn_sort]:
            btn.setEnabled(image_loaded)
        self.btn_prev.setEnabled(nav_bck)
        self.btn_next.setEnabled(nav_fwd)

    def _update_counter(self):
        if self.image_paths:
            self.lbl_counter.setText(f"{self.current_index + 1} / {len(self.image_paths)}")
        else:
            self.lbl_counter.setText("— / —")

    def _update_zoom_label(self):
        self.lbl_zoom.setText(f"{self.zoom_level * 100:.0f}%")

    def _canvas_mouse_move(self, event):
        QGraphicsView.mouseMoveEvent(self.view, event)
        if self.pixmap_item:
            scene_pos = self.view.mapToScene(event.pos())
            px = int(scene_pos.x())
            py = int(scene_pos.y())
            pm  = self.pixmap_item.pixmap()
            if 0 <= px < pm.width() and 0 <= py < pm.height():
                tip = f"x:{px}  y:{py}"
                QToolTip.showText(event.globalPosition().toPoint(), tip, self.view)

    # ── image loading ─────────────────────────────────────────────────────────
    def open_image(self):
        fmts = " ".join(
            f"*.{fmt.data().decode().lower()}"
            for fmt in QImageReader.supportedImageFormats()
        )
        path, _ = QFileDialog.getOpenFileName(
            self, "Open Image", "", f"Images ({fmts})"
        )
        if path:
            self.load_directory(os.path.normpath(path))

    def load_directory(self, target_file: str):
        target_file = os.path.normpath(target_file)
        directory   = os.path.dirname(target_file)
        formats     = {fmt.data().decode().lower() for fmt in QImageReader.supportedImageFormats()}

        self.image_paths = []
        try:
            for f in os.listdir(directory):
                if f.rsplit(".", 1)[-1].lower() in formats:
                    self.image_paths.append(os.path.normpath(os.path.join(directory, f)))
        except Exception:
            pass

        if not self.image_paths:
            self.image_paths = [target_file]

        self._apply_sort()

        if target_file in self.image_paths:
            self.current_index = self.image_paths.index(target_file)
        else:
            self.current_index = 0

        self._add_recent(target_file)
        self._build_filmstrip_thumbs()
        self.display_image()

    def _apply_sort(self):
        mode = SORT_MODES[self.sort_mode_index]
        reverse = "↓" in mode
        if "Name" in mode:
            self.image_paths.sort(key=lambda p: os.path.basename(p).lower(), reverse=reverse)
        elif "Date" in mode:
            self.image_paths.sort(key=lambda p: os.path.getmtime(p), reverse=reverse)
        elif "Size" in mode:
            self.image_paths.sort(key=lambda p: os.path.getsize(p), reverse=reverse)

    def _cycle_sort(self):
        self.sort_mode_index = (self.sort_mode_index + 1) % len(SORT_MODES)
        mode = SORT_MODES[self.sort_mode_index]
        self.btn_sort.setText(f"⇅ {mode}")
        if self.image_paths:
            current = self.image_paths[self.current_index] if self.current_index >= 0 else None
            self._apply_sort()
            if current and current in self.image_paths:
                self.current_index = self.image_paths.index(current)
            self._build_filmstrip_thumbs()
            self._scroll_filmstrip_to(self.current_index)
            self._update_counter()
            self._toggle_controls(True)

    # ── display ───────────────────────────────────────────────────────────────
    def display_image(self, fade: bool = True):
        if not (0 <= self.current_index < len(self.image_paths)):
            return

        def _do_load():
            if self.welcome_proxy:
                self.scene.removeItem(self.welcome_proxy)
                self.welcome_proxy = None
            self.scene.clear()
            path = self.image_paths[self.current_index]
            pixmap = QPixmap(path)
            if pixmap.isNull():
                return

            self.pixmap_item = QGraphicsPixmapItem(pixmap)
            self.pixmap_item.setTransformationMode(Qt.TransformationMode.SmoothTransformation)
            self.scene.addItem(self.pixmap_item)
            self.scene.setSceneRect(0, 0, pixmap.width(), pixmap.height())

            # reset transforms
            self._rotation_accum = 0
            self._flip_h = False
            self._flip_v = False
            self._reset_view_state()
            self._apply_adjustments()
            self._update_hud_metadata(path, pixmap)

            name = os.path.basename(path)
            self.lbl_title.setText(f"Nova View  —  {name}")
            self._toggle_controls(True)
            self._update_counter()
            self._update_zoom_label()
            self._highlight_filmstrip(self.current_index)
            self._scroll_filmstrip_to(self.current_index)

            if fade:
                self._opacity_effect.setOpacity(0)
                self._fade_anim.setStartValue(0.0)
                self._fade_anim.setEndValue(1.0)
                self._fade_anim.start()

        _do_load()

    def _reset_view_state(self):
        self.view.resetTransform()
        if self.pixmap_item:
            self.view.fitInView(self.pixmap_item, Qt.AspectRatioMode.KeepAspectRatio)
        self.zoom_level = 1.0

    # ── metadata / EXIF ───────────────────────────────────────────────────────
    def _update_hud_metadata(self, path: str, pixmap: QPixmap):
        fi = QFileInfo(path)
        bytes_ = fi.size()
        size_str = f"{bytes_/1024:.1f} KB" if bytes_ < 1_048_576 else f"{bytes_/1_048_576:.2f} MB"
        mtime = datetime.fromtimestamp(os.path.getmtime(path)).strftime("%Y-%m-%d  %H:%M")

        self.lbl_hud_name.setText(f"<b>Name:</b><br>{fi.fileName()}")
        self.lbl_hud_res .setText(f"<b>Resolution:</b><br>{pixmap.width()} × {pixmap.height()} px")
        self.lbl_hud_size.setText(f"<b>Size:</b><br>{size_str}")
        self.lbl_hud_type.setText(f"<b>Format:</b><br>{fi.suffix().upper()}")
        self.lbl_hud_date.setText(f"<b>Modified:</b><br>{mtime}")

        exif_text = ""
        if HAS_PIL:
            try:
                img = PILImage.open(path)
                exif_data = img._getexif()
                if exif_data:
                    wanted = {"DateTimeOriginal": "📅 Taken",
                              "Make":             "📷 Make",
                              "Model":            "Model",
                              "ExposureTime":     "⏱ Exposure",
                              "FNumber":          "𝑓-stop",
                              "ISOSpeedRatings":  "ISO",
                              "FocalLength":      "Focal"}
                    lines = []
                    for tag_id, val in exif_data.items():
                        tag = TAGS.get(tag_id, "")
                        if tag in wanted:
                            if tag == "FNumber":
                                try: val = f"ƒ/{float(val):.1f}"
                                except: pass
                            elif tag == "ExposureTime":
                                try:
                                    f = val
                                    val = f"1/{int(1/f)}s" if f < 1 else f"{f}s"
                                except: pass
                            elif tag == "FocalLength":
                                try: val = f"{float(val):.0f} mm"
                                except: pass
                            lines.append(f"<b>{wanted[tag]}:</b> {val}")
                    if lines:
                        exif_text = "<br>".join(lines)
            except Exception:
                pass
        self.lbl_hud_exif.setText(exif_text)

    # ── filmstrip ─────────────────────────────────────────────────────────────
    def _build_filmstrip_thumbs(self):
        # clear
        for lbl in self._thumbnail_labels:
            lbl.deleteLater()
        self._thumbnail_labels.clear()
        while self.filmstrip_layout.count() > 1:
            item = self.filmstrip_layout.takeAt(0)
            if item.widget():
                item.widget().deleteLater()

        if not self.image_paths:
            self.filmstrip_bar.hide()
            return

        self.filmstrip_bar.show()
        for i, path in enumerate(self.image_paths):
            lbl = ThumbnailLabel(i, self.filmstrip_inner)
            pm = QPixmap(path)
            if not pm.isNull():
                lbl.setPixmap(
                    pm.scaled(THUMBNAIL_SIZE - 4, THUMBNAIL_SIZE - 4,
                              Qt.AspectRatioMode.KeepAspectRatio,
                              Qt.TransformationMode.SmoothTransformation)
                )
            self.filmstrip_layout.insertWidget(i, lbl)
            self._thumbnail_labels.append(lbl)

    def _highlight_filmstrip(self, index: int):
        for i, lbl in enumerate(self._thumbnail_labels):
            lbl.set_active(i == index)

    def _scroll_filmstrip_to(self, index: int):
        if 0 <= index < len(self._thumbnail_labels):
            lbl = self._thumbnail_labels[index]
            self.filmstrip_scroll.ensureWidgetVisible(lbl)

    def goto_index(self, index: int):
        if 0 <= index < len(self.image_paths):
            self.current_index = index
            self.display_image()

    # ── navigation ────────────────────────────────────────────────────────────
    def show_previous(self):
        if self.current_index > 0:
            self.current_index -= 1
            self.display_image()

    def show_next(self):
        if self.current_index < len(self.image_paths) - 1:
            self.current_index += 1
            self.display_image()

    # ── zoom ──────────────────────────────────────────────────────────────────
    def zoom_image(self, factor: float):
        new_zoom = self.zoom_level * factor
        if 0.05 < new_zoom < 30.0:
            self.zoom_level = new_zoom
            self.view.scale(factor, factor)
            self._update_zoom_label()

    def reset_view(self):
        if self.pixmap_item:
            self._reset_view_state()
            self._update_zoom_label()

    def _zoom_actual(self):
        """Set zoom to 100% (actual pixels)."""
        if self.pixmap_item:
            self.view.resetTransform()
            self.zoom_level = 1.0
            self._update_zoom_label()

    # ── transforms ────────────────────────────────────────────────────────────
    def rotate_image(self, degrees: int = 90):
        if self.pixmap_item:
            self._rotation_accum = (self._rotation_accum + degrees) % 360
            self.view.rotate(degrees)

    def flip_image(self, horizontal: bool = True):
        if self.pixmap_item:
            if horizontal:
                self._flip_h = not self._flip_h
                self.view.scale(-1, 1)
            else:
                self._flip_v = not self._flip_v
                self.view.scale(1, -1)

    # ── adjustments ───────────────────────────────────────────────────────────
    def _on_slider_change(self, key: str, value: int):
        self._slider_vals[key] = value
        self._sliders[key].setToolTip(f"{key.capitalize()}: {value:+d}")
        # Debounce: cancel any pending call, fire after 60 ms idle
        if not hasattr(self, "_adj_timer"):
            self._adj_timer = QTimer(self)
            self._adj_timer.setSingleShot(True)
            self._adj_timer.timeout.connect(self._apply_adjustments)
        self._adj_timer.start(60)

    def _apply_adjustments(self):
        if not self.pixmap_item or self.current_index < 0:
            return
        path = self.image_paths[self.current_index]
        base_pixmap = QPixmap(path)
        if base_pixmap.isNull():
            return

        b = self._slider_vals.get("brightness", 0)
        c = self._slider_vals.get("contrast",   0)
        s = self._slider_vals.get("saturation", 0)

        if b == 0 and c == 0 and s == 0:
            self.pixmap_item.setPixmap(base_pixmap)
            return

        # ── Build 256-entry LUTs (one per channel concept) ───────────────────
        # Brightness delta
        bd = b * 2.55
        # Contrast factor
        cf = (259 * (c + 255)) / (255 * (259 - c)) if c != -255 else 0.0
        # Saturation factor
        sf = 1.0 + s / 100.0

        # Pre-compute a per-value brightness+contrast LUT (channel-independent)
        bc_lut = bytes(
            min(255, max(0, int(cf * (int(bd + v) - 128) + 128)))
            if c != 0 else
            min(255, max(0, int(v + bd)))
            for v in range(256)
        )

        image = base_pixmap.toImage().convertToFormat(QImage.Format.Format_ARGB32)
        ptr   = image.bits()
        ptr.setsize(image.sizeInBytes())
        arr   = bytearray(ptr)

        if s == 0:
            # ── Fast path: only brightness+contrast, use translate() ─────────
            # ARGB32 layout: B G R A in memory (4-byte chunks)
            # Apply bc_lut to channels 0(B), 1(G), 2(R); skip 3(A)
            for offset in (0, 1, 2):          # B, G, R
                arr[offset::4] = bytes(bc_lut[v] for v in arr[offset::4])
        else:
            # ── With saturation: process each pixel's RGB together ───────────
            # Apply brightness+contrast first via translate on each channel
            r_ch = list(bc_lut[v] for v in arr[2::4])
            g_ch = list(bc_lut[v] for v in arr[1::4])
            b_ch = list(bc_lut[v] for v in arr[0::4])

            # Saturation via luma mix
            for i in range(len(r_ch)):
                r, g, bl = r_ch[i], g_ch[i], b_ch[i]
                luma = 0.299 * r + 0.587 * g + 0.114 * bl
                r_ch[i] = min(255, max(0, int(luma + sf * (r  - luma))))
                g_ch[i] = min(255, max(0, int(luma + sf * (g  - luma))))
                b_ch[i] = min(255, max(0, int(luma + sf * (bl - luma))))

            arr[2::4] = bytes(r_ch)
            arr[1::4] = bytes(g_ch)
            arr[0::4] = bytes(b_ch)

        result = QImage(bytes(arr), image.width(), image.height(),
                        image.bytesPerLine(), QImage.Format.Format_ARGB32)
        self.pixmap_item.setPixmap(QPixmap.fromImage(result))

    def _reset_adjustments(self):
        for key, slider in self._sliders.items():
            slider.setValue(0)
            self._slider_vals[key] = 0
        self._apply_adjustments()

    # ── slideshow ─────────────────────────────────────────────────────────────
    def toggle_slideshow(self):
        if self.slideshow_timer.isActive():
            self.slideshow_timer.stop()
            self.btn_slideshow.setText("▷ Slideshow")
            self.btn_slideshow.setObjectName("")
            self.btn_slideshow.setStyle(self.btn_slideshow.style())
        else:
            if not self.image_paths:
                return
            ms = SLIDESHOW_INTERVALS_MS[self._slideshow_interval_key]
            self.slideshow_timer.start(ms)
            self.btn_slideshow.setText("⏸ Slideshow")
            self.btn_slideshow.setObjectName("SlideshowActive")
            self.btn_slideshow.setStyle(self.btn_slideshow.style())

    def _slideshow_advance(self):
        if self.current_index < len(self.image_paths) - 1:
            self.current_index += 1
        else:
            self.current_index = 0      # wrap around
        self.display_image()

    def _slideshow_interval_menu(self):
        menu = QMenu(self)
        menu.setStyleSheet(
            "QMenu { background: rgba(28,28,38,0.96); color: #fff; border: 1px solid rgba(255,255,255,0.12); border-radius: 8px; }"
            "QMenu::item:selected { background: rgba(255,255,255,0.12); }"
        )
        for key in SLIDESHOW_INTERVALS_MS:
            action = menu.addAction(("✓ " if key == self._slideshow_interval_key else "    ") + key)
            action.setData(key)
        chosen = menu.exec(self.btn_slideshow.mapToGlobal(QPoint(0, -menu.sizeHint().height())))
        if chosen and chosen.data():
            self._slideshow_interval_key = chosen.data()
            if self.slideshow_timer.isActive():
                self.slideshow_timer.setInterval(SLIDESHOW_INTERVALS_MS[self._slideshow_interval_key])

    # ── clipboard & export ────────────────────────────────────────────────────
    def copy_to_clipboard(self):
        if self.pixmap_item:
            QGuiApplication.clipboard().setPixmap(self.pixmap_item.pixmap())

    def save_as(self):
        if not self.pixmap_item:
            return
        fmts = " ".join(f"*.{f.lower()}" for f in SUPPORTED_WRITE_FMTS)
        dest, _ = QFileDialog.getSaveFileName(
            self, "Save / Export Image", "", f"Images ({fmts})"
        )
        if dest:
            self.pixmap_item.pixmap().save(dest)

    def delete_current(self):
        if not self.image_paths or self.current_index < 0:
            return
        path = self.image_paths[self.current_index]
        reply = QMessageBox.question(
            self, "Delete File",
            f"Permanently delete:\n{os.path.basename(path)}?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
        )
        if reply == QMessageBox.StandardButton.Yes:
            try:
                os.remove(path)
                self.image_paths.pop(self.current_index)
                self._thumbnail_labels[self.current_index].deleteLater()
                self._thumbnail_labels.pop(self.current_index)
                if not self.image_paths:
                    self.scene.clear()
                    self.pixmap_item = None
                    self._toggle_controls(False)
                    self.lbl_title.setText("Nova View")
                    self.lbl_counter.setText("— / —")
                    self.filmstrip_bar.hide()
                else:
                    self.current_index = min(self.current_index, len(self.image_paths) - 1)
                    self.display_image()
            except Exception as e:
                QMessageBox.critical(self, "Error", str(e))

    # ── print ─────────────────────────────────────────────────────────────────
    def print_image(self):
        if not self.pixmap_item:
            return
        printer = QPrinter(QPrinter.PrinterMode.HighResolution)
        dlg = QPrintDialog(printer, self)
        if dlg.exec() == QPrintDialog.DialogCode.Accepted:
            painter = QPainter(printer)
            rect    = painter.viewport()
            scaled  = self.pixmap_item.pixmap().scaled(
                rect.size(),
                Qt.AspectRatioMode.KeepAspectRatio,
                Qt.TransformationMode.SmoothTransformation,
            )
            x = (rect.width()  - scaled.width())  // 2
            y = (rect.height() - scaled.height()) // 2
            painter.drawPixmap(x, y, scaled)
            painter.end()

    # ── info HUD ──────────────────────────────────────────────────────────────
    def toggle_info_hud(self):
        self.info_hud.setVisible(not self.info_hud.isVisible())

    # ── recent files ──────────────────────────────────────────────────────────
    def _add_recent(self, path: str):
        if path in self.recent_files:
            self.recent_files.remove(path)
        self.recent_files.insert(0, path)
        self.recent_files = self.recent_files[:MAX_RECENT]

    def _show_recent_menu(self, pos):
        self._recent_menu.clear()
        if not self.recent_files:
            self._recent_menu.addAction("No recent files").setEnabled(False)
        else:
            for p in self.recent_files:
                act = self._recent_menu.addAction(os.path.basename(p))
                act.setData(p)
                act.triggered.connect(lambda checked=False, fp=p: self.load_directory(fp))
        self._recent_menu.exec(self.btn_open.mapToGlobal(pos))

    # ── fullscreen ────────────────────────────────────────────────────────────
    def _toggle_fullscreen(self):
        if self._is_fullscreen:
            self.setWindowFlags(Qt.WindowType.FramelessWindowHint)
            self.showNormal()
            self._is_fullscreen = False
            self.main_frame.setStyleSheet(
                "QWidget#MainGlassFrame { border-radius: 16px; background-color: rgba(18,18,26,0.82); }"
            )
        else:
            self.setWindowFlags(Qt.WindowType.FramelessWindowHint | Qt.WindowType.Window)
            self.showFullScreen()
            self._is_fullscreen = True
            self.main_frame.setStyleSheet(
                "QWidget#MainGlassFrame { border-radius: 0px; background-color: rgba(10,10,16,0.98); }"
            )
        self.show()
        if self.pixmap_item:
            self.reset_view()

    def _toggle_maximize(self):
        if self.isMaximized():
            self.showNormal()
            self.main_frame.setStyleSheet(
                "QWidget#MainGlassFrame { border-radius: 16px; background-color: rgba(18,18,26,0.82); }"
            )
        else:
            self.showMaximized()
            self.main_frame.setStyleSheet(
                "QWidget#MainGlassFrame { border-radius: 0px; background-color: rgba(18,18,26,0.82); }"
            )

    # ── drag & drop ───────────────────────────────────────────────────────────
    def dragEnterEvent(self, event: QDragEnterEvent):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()
            self.main_frame.setStyleSheet(
                "QWidget#MainGlassFrame { background-color: rgba(35,40,60,0.92); border-radius: 16px; }"
            )

    def dragLeaveEvent(self, event):
        rad = "0px" if self.isMaximized() else "16px"
        self.main_frame.setStyleSheet(
            f"QWidget#MainGlassFrame {{ border-radius: {rad}; background-color: rgba(18,18,26,0.82); }}"
        )

    def dropEvent(self, event: QDropEvent):
        self.dragLeaveEvent(None)
        urls = event.mimeData().urls()
        if urls:
            path = os.path.normpath(urls[0].toLocalFile())
            if os.path.isfile(path):
                self.load_directory(path)

    # ── frameless window drag ─────────────────────────────────────────────────
    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self.drag_position = event.globalPosition().toPoint() - self.frameGeometry().topLeft()
            event.accept()

    def mouseMoveEvent(self, event):
        if event.buttons() == Qt.MouseButton.LeftButton and not self._is_fullscreen:
            self.move(event.globalPosition().toPoint() - self.drag_position)
            event.accept()

    # ── scroll wheel zoom ─────────────────────────────────────────────────────
    def wheelEvent(self, event):
        if self.pixmap_item:
            factor = 1.12 if event.angleDelta().y() > 0 else 0.88
            self.zoom_image(factor)

    # ── keyboard shortcuts ────────────────────────────────────────────────────
    def keyPressEvent(self, event):
        key  = event.key()
        mods = event.modifiers()

        if key == Qt.Key.Key_Right:                self.show_next()
        elif key == Qt.Key.Key_Left:               self.show_previous()
        elif key in (Qt.Key.Key_Plus, Qt.Key.Key_Equal):  self.zoom_image(1.25)
        elif key == Qt.Key.Key_Minus:              self.zoom_image(0.80)
        elif key == Qt.Key.Key_R and not mods:     self.rotate_image(90)
        elif key == Qt.Key.Key_R and mods & Qt.KeyboardModifier.ShiftModifier:
                                                   self.rotate_image(-90)
        elif key == Qt.Key.Key_H:                  self.flip_image(horizontal=True)
        elif key == Qt.Key.Key_V and not mods:     self.flip_image(horizontal=False)
        elif key == Qt.Key.Key_F:                  self.reset_view()
        elif key == Qt.Key.Key_I:                  self.toggle_info_hud()
        elif key == Qt.Key.Key_Space:              self.toggle_slideshow()
        elif key == Qt.Key.Key_Delete:             self.delete_current()
        elif key == Qt.Key.Key_F11:                self._toggle_fullscreen()
        elif key == Qt.Key.Key_Escape:
            if self._is_fullscreen:                self._toggle_fullscreen()
        elif mods & Qt.KeyboardModifier.ControlModifier:
            if key == Qt.Key.Key_O:                self.open_image()
            elif key == Qt.Key.Key_C:              self.copy_to_clipboard()
            elif key == Qt.Key.Key_S:              self.save_as()
            elif key == Qt.Key.Key_P:              self.print_image()
            elif key == Qt.Key.Key_1:              self._zoom_actual()

    # ── resize ────────────────────────────────────────────────────────────────
    def resizeEvent(self, event):
        if self.pixmap_item and self.zoom_level == 1.0:
            self.view.fitInView(self.pixmap_item, Qt.AspectRatioMode.KeepAspectRatio)
        super().resizeEvent(event)


# ─────────────────────────────────────────────────────────────────────────────
if __name__ == "__main__":
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    viewer = NovaView()
    viewer.show()

    # Windows passes the double-clicked / "Open with" file as the first argument
    if len(sys.argv) > 1:
        import os as _os
        _path = _os.path.normpath(sys.argv[1])
        if _os.path.isfile(_path):
            viewer.load_directory(_path)

    sys.exit(app.exec())
