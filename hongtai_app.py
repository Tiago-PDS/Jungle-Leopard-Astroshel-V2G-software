"""
Hongtai Screen - small Windows app that plays GIFs on a Hongtai / Jungle Leopard
USB screen (USB ID 33C3:xxxx) without the vendor software.

Setup (once):
    python -m pip install pyserial pillow pystray psutil
    (pystray is optional: it adds the system-tray icon. psutil is optional: it
    is only needed for the live PC stats modes.)

Run:
    python hongtai_app.py          (opens the window)
    pythonw hongtai_app.py         (same, without a console window)

Tick "Start with Windows" in the app and it will launch silently at every login,
straight into the tray, and start playing your playlist.

Only one program can use the screen at a time: close Jungle Leopard and disable
its own autostart.

Settings and the log file live in  %APPDATA%\\HongtaiScreen
"""
import argparse
import datetime
import functools
import io
import json
import logging
import os
import queue
import random
import shutil
import socket
import subprocess
import sys
import threading
import time
from logging.handlers import RotatingFileHandler

import tkinter as tk
from tkinter import filedialog, messagebox, ttk

APP_NAME = "Hongtai Screen"


def fatal(msg):
    try:
        r = tk.Tk()
        r.withdraw()
        messagebox.showerror(APP_NAME, msg)
        r.destroy()
    except Exception:
        pass
    sys.exit(msg)


try:
    import serial
    from serial.tools import list_ports
except ImportError:
    fatal("pyserial is missing.\nRun:  python -m pip install pyserial pillow pystray")
try:
    from PIL import Image, ImageDraw, ImageFont, ImageSequence
except ImportError:
    fatal("Pillow is missing.\nRun:  python -m pip install pyserial pillow pystray")
try:
    import pystray
except Exception:          # optional; the app works without a tray icon
    pystray = None
try:
    import psutil
except ImportError:        # optional; only the stats modes need it
    psutil = None
try:
    import winreg
except ImportError:        # not Windows
    winreg = None

# ------------------------------------------------------------------ constants
VID = 0x33C3
BAUD = 2_000_000                       # CDC-ACM ignores the rate
ABORT = bytes([0xFF, 0xD9, 0xFF, 0xD9, 0, 0, 0, 0])   # ends a half-sent frame
KEEPALIVE_SEC = 1.5                    # the screen leaves live mode without opcode 0x11
VARIANT = "A"                          # all four variants worked on this screen
RUN_KEY = r"Software\Microsoft\Windows\CurrentVersion\Run"
RUN_VALUE = "HongtaiScreen"
LOCK_PORT = 47653                      # only one copy of the app may run
IMAGE_EXT = (".gif", ".png", ".jpg", ".jpeg", ".bmp", ".webp")

CONFIG_DIR = os.path.join(os.environ.get("APPDATA") or os.path.expanduser("~"), "HongtaiScreen")
CONFIG_FILE = os.path.join(CONFIG_DIR, "config.json")
LOG_FILE = os.path.join(CONFIG_DIR, "app.log")

DEFAULTS = {
    "playlist": [],
    "seconds_per_gif": 30,
    "shuffle": False,
    "rotate": 0,            # set this to the value that looked upright in your test
    "fit": "contain",
    "brightness": 80,
    "max_fps": 20,
    "max_kb": 30,           # per JPEG frame; oversized frames can freeze the display
    "mode": "playlist",     # playlist | stats | clock | picture | stats_gif
    "picture": "",          # file used by the "picture" and "stats_gif" modes
}

MODE_LABELS = {
    "playlist": "Playlist",
    "stats": "Live PC stats",
    "clock": "Clock",
    "picture": "Picture / GIF",
    "stats_gif": "Stats over GIF",
}

RESAMPLE = getattr(Image, "Resampling", Image).LANCZOS
TRANSPOSE = getattr(Image, "Transpose", Image)
log = logging.getLogger("hongtai")


# ------------------------------------------------------------------ config
def load_config():
    cfg = dict(DEFAULTS)
    try:
        with open(CONFIG_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        for k, v in data.items():
            if k in DEFAULTS and type(v) is type(DEFAULTS[k]):
                cfg[k] = v
    except FileNotFoundError:
        pass
    except Exception:
        log.exception("Could not read config, using defaults")
    if cfg["mode"] not in MODE_LABELS:
        cfg["mode"] = "playlist"
    return cfg


def save_config(cfg):
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        tmp = CONFIG_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(cfg, f, indent=2, ensure_ascii=False)
        os.replace(tmp, CONFIG_FILE)
    except Exception:
        log.exception("Could not save config")


# ------------------------------------------------------------------ autostart
def autostart_command():
    if getattr(sys, "frozen", False):
        return f'"{sys.executable}" --minimized'
    exe = sys.executable
    pyw = os.path.join(os.path.dirname(exe), "pythonw.exe")
    if os.path.exists(pyw):
        exe = pyw
    return f'"{exe}" "{os.path.abspath(__file__)}" --minimized'


def autostart_enabled():
    if winreg is None:
        return False
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY) as k:
            winreg.QueryValueEx(k, RUN_VALUE)
        return True
    except OSError:
        return False


def set_autostart(on):
    with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY, 0, winreg.KEY_SET_VALUE) as k:
        if on:
            winreg.SetValueEx(k, RUN_VALUE, 0, winreg.REG_SZ, autostart_command())
        else:
            try:
                winreg.DeleteValue(k, RUN_VALUE)
            except FileNotFoundError:
                pass


# ------------------------------------------------------------------ protocol
def control_frame(key, payload=b""):
    body = bytes([0x55, 0xAA]) + (len(payload) + 7).to_bytes(2, "little") + bytes([key]) + payload
    return body + (sum(body) & 0xFFFF).to_bytes(2, "little")


def image_frame(jpeg, variant=VARIANT):
    n = len(jpeg)
    head = (n if variant in "AB" else n + 6).to_bytes(4, "little")
    total = sum(jpeg) if variant in "AC" else sum(head) + sum(jpeg)
    return head + jpeg + (total & 0xFFFF).to_bytes(2, "little")


def read_exact(ser, n, timeout):
    buf = b""
    end = time.time() + timeout
    while len(buf) < n and time.time() < end:
        buf += ser.read(n - len(buf))
    return buf


def find_port():
    for p in list_ports.comports():
        if p.vid == VID:
            return p.device
    return None


class Panel:
    def __init__(self, port):
        self.ser = serial.Serial(port, BAUD, timeout=0.2, write_timeout=3)
        self.wrapped = True
        self.failed = False
        self.lock = threading.Lock()
        self.stop_evt = threading.Event()
        self.threads = []

    def get_info(self):
        ser = self.ser
        ser.reset_input_buffer()
        ser.write(control_frame(0x06))
        ser.flush()
        head = read_exact(ser, 5, 3)
        if len(head) < 5 or head[:2] != b"\x55\xaa":
            raise RuntimeError("The screen did not answer. Unplug and replug it, "
                               "and make sure Jungle Leopard is closed.")
        total = int.from_bytes(head[2:4], "little")
        if not 7 <= total <= 8192:
            raise RuntimeError(f"Unexpected reply length {total}.")
        msg = head + read_exact(ser, total - 5, 3)
        return json.loads(msg[5:-2].decode("utf-8"))["data"]

    def _spawn(self, fn):
        t = threading.Thread(target=fn, daemon=True)
        t.start()
        self.threads.append(t)

    def _drain(self):
        while not self.stop_evt.is_set():
            try:
                self.ser.read(4096)
            except Exception:
                if not self.stop_evt.is_set():
                    self.failed = True
                break

    def _keepalive(self):
        while not self.stop_evt.wait(KEEPALIVE_SEC):
            try:
                with self.lock:
                    self.ser.write(control_frame(0x11))
            except Exception:
                self.failed = True
                break

    def reset_stream(self):
        with self.lock:
            self.ser.write(ABORT)
            self.ser.flush()
        time.sleep(0.15)
        with self.lock:
            self.ser.write(control_frame(0x11))
            self.ser.flush()
        time.sleep(0.15)

    def start(self):
        self._spawn(self._drain)
        self.reset_stream()
        self._spawn(self._keepalive)

    def set_brightness(self, value):
        with self.lock:
            self.ser.write(control_frame(0x03, bytes([max(0, min(100, int(value)))])))

    def send_frame(self, jpeg):
        data = image_frame(jpeg) if self.wrapped else jpeg
        with self.lock:
            self.ser.write(data)

    def close(self):
        self.stop_evt.set()
        for t in self.threads:
            t.join(timeout=1)
        try:
            with self.lock:
                self.ser.write(ABORT)
                self.ser.flush()
        except Exception:
            pass
        try:
            self.ser.close()
        except Exception:
            pass


# ------------------------------------------------------------------ image helpers
class Aborted(Exception):
    pass


def canvas_size(size, rotate):
    w, h = size
    return (h, w) if rotate in (90, 270) else (w, h)


def apply_rotation(img, rotate):
    if rotate == 90:
        return img.transpose(TRANSPOSE.ROTATE_270)
    if rotate == 180:
        return img.transpose(TRANSPOSE.ROTATE_180)
    if rotate == 270:
        return img.transpose(TRANSPOSE.ROTATE_90)
    return img


def fit_image(img, size, mode):
    w, h = size
    img = img.convert("RGB")
    if mode == "stretch":
        return img.resize((w, h), RESAMPLE)
    iw, ih = img.size
    scale = max(w / iw, h / ih) if mode == "cover" else min(w / iw, h / ih)
    nw, nh = max(1, round(iw * scale)), max(1, round(ih * scale))
    canvas = Image.new("RGB", (w, h), (0, 0, 0))
    canvas.paste(img.resize((nw, nh), RESAMPLE), ((w - nw) // 2, (h - nh) // 2))
    return canvas


def encode_jpeg(img, max_bytes):
    for q in range(90, 24, -5):
        buf = io.BytesIO()
        img.save(buf, "JPEG", quality=q, optimize=False, progressive=False, subsampling="4:2:0")
        data = buf.getvalue()
        if len(data) <= max_bytes:
            return data
    raise ValueError(f"a frame is bigger than {max_bytes // 1024} KB even at low quality "
                     "(use a simpler GIF or raise the frame size limit a little)")


def load_frames(path, size, mode, rotate, max_bytes, max_fps, abort_check):
    min_delay = 1.0 / max_fps
    frames = []
    with Image.open(path) as img:
        for fr in ImageSequence.Iterator(img):
            if abort_check():
                raise Aborted()
            d = fr.info.get("duration", 100)
            if d < 20:                       # browsers treat tiny GIF delays as 100 ms
                d = 100
            shown = apply_rotation(fit_image(fr, canvas_size(size, rotate), mode), rotate)
            frames.append((encode_jpeg(shown, max_bytes), max(d / 1000.0, min_delay)))
    if len(frames) == 1:
        frames = [(frames[0][0], 0.5)]       # still picture: refresh twice a second
    return frames


def orientation_pattern(size, rotate):
    w, h = canvas_size(size, rotate)
    img = Image.new("RGB", (w, h), (20, 20, 30))
    d = ImageDraw.Draw(img)
    s = max(16, min(w, h) // 6)
    d.rectangle([0, 0, s, s], fill=(255, 0, 0))
    d.rectangle([w - s, 0, w, s], fill=(0, 200, 0))
    d.rectangle([0, h - s, s, h], fill=(0, 0, 255))
    d.rectangle([w - s, h - s, w, h], fill=(255, 220, 0))
    d.rectangle([0, 0, w - 1, h - 1], outline=(255, 255, 255))
    u = min(w, h) // 8
    x0, y0 = w // 2 - 2 * u, h // 2 - 3 * u
    d.rectangle([x0, y0, x0 + u, y0 + 6 * u], fill=(255, 255, 255))
    d.rectangle([x0, y0, x0 + 4 * u, y0 + u], fill=(255, 255, 255))
    d.rectangle([x0, y0 + 2 * u, x0 + 3 * u, y0 + 3 * u], fill=(255, 255, 255))
    return apply_rotation(img, rotate)


def message_image(size, rotate, lines):
    w, h = canvas_size(size, rotate)
    img = Image.new("RGB", (w, h), (0, 0, 0))
    d = ImageDraw.Draw(img)
    try:
        font = ImageFont.load_default(size=18)
    except (TypeError, OSError):
        font = ImageFont.load_default()
    y = h // 2 - 14 * len(lines)
    for line in lines:
        box = d.textbbox((0, 0), line, font=font)
        d.text(((w - (box[2] - box[0])) // 2, y), line, fill=(255, 255, 255), font=font)
        y += 28
    return apply_rotation(img, rotate)


# ------------------------------------------------------------------ live screens (stats, clock)
@functools.lru_cache(maxsize=64)
def get_font(size):
    for name in ("segoeui.ttf", "arial.ttf", "DejaVuSans.ttf"):
        try:
            return ImageFont.truetype(name, size)
        except OSError:
            continue
    try:
        return ImageFont.load_default(size=size)
    except (TypeError, OSError):
        return ImageFont.load_default()


def text_size(d, text, font):
    box = d.textbbox((0, 0), text, font=font)
    return box[2] - box[0], box[3] - box[1], box[0], box[1]


def draw_centered(d, text, font, cx, cy, fill):
    tw, th, ox, oy = text_size(d, text, font)
    d.text((cx - tw / 2 - ox, cy - th / 2 - oy), text, font=font, fill=fill)


def fit_font(d, text, max_w, start):
    size = start
    while size > 8 and text_size(d, text, get_font(size))[0] > max_w:
        size -= 2
    return get_font(size)


NVSMI = shutil.which("nvidia-smi") or next(
    (p for p in (r"C:\Program Files\NVIDIA Corporation\NVSMI\nvidia-smi.exe",) if os.path.exists(p)), None)


def query_gpu():
    """NVIDIA only (uses nvidia-smi, which comes with the driver). Empty dict otherwise."""
    if not NVSMI:
        return {}
    try:
        out = subprocess.run(
            [NVSMI, "--query-gpu=utilization.gpu,temperature.gpu,memory.used,memory.total",
             "--format=csv,noheader,nounits"],
            capture_output=True, text=True, timeout=3,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0)).stdout.strip().splitlines()[0]
        util, temp, used, total = [float(x) for x in out.split(",")]
        return {"gpu": util, "gpu_temp": temp, "vram_used": used, "vram_total": total}
    except Exception:
        return {}


def read_cpu_temp():
    """psutil only reports CPU temperature on Linux/macOS; on Windows this returns None."""
    if psutil is None:
        return None
    try:
        temps = psutil.sensors_temperatures()
    except Exception:
        return None
    for name in ("coretemp", "k10temp", "cpu_thermal", "zenpower"):
        if temps.get(name):
            return temps[name][0].current
    for entries in temps.values():
        if entries:
            return entries[0].current
    return None


class StatsSampler(threading.Thread):
    """Samples CPU / RAM / GPU once a second, but only while a stats mode is on screen."""

    def __init__(self):
        super().__init__(daemon=True)
        self.data = {}
        self.active_until = 0.0
        self.stop_evt = threading.Event()

    def want(self):
        self.active_until = time.monotonic() + 5

    def sample(self):
        d = {}
        if psutil:
            d["cpu"] = psutil.cpu_percent(None)
            d["ram"] = psutil.virtual_memory().percent
            t = read_cpu_temp()
            if t is not None:
                d["cpu_temp"] = t
        d.update(query_gpu())
        return d

    def run(self):
        if psutil:
            psutil.cpu_percent(None)
        while not self.stop_evt.wait(1.0):
            if time.monotonic() > self.active_until:
                continue
            try:
                self.data = self.sample()
            except Exception:
                log.exception("Stats sampling failed")


def stats_rows(data):
    rows = []
    if "cpu" in data:
        rows.append(("CPU", data["cpu"], f"{data['cpu']:.0f}%"))
    if "ram" in data:
        rows.append(("RAM", data["ram"], f"{data['ram']:.0f}%"))
    if "gpu" in data:
        rows.append(("GPU", data["gpu"], f"{data['gpu']:.0f}%"))
    if "gpu_temp" in data:
        rows.append(("GPU temp", data["gpu_temp"], f"{data['gpu_temp']:.0f}\u00b0C"))
    if "cpu_temp" in data:
        rows.append(("CPU temp", data["cpu_temp"], f"{data['cpu_temp']:.0f}\u00b0C"))
    if data.get("vram_total"):
        used, total = data["vram_used"], data["vram_total"]
        rows.append(("VRAM", used / total * 100, f"{used / 1024:.1f}/{total / 1024:.0f} GB"))
    return rows


def bar_color(pct):
    if pct < 60:
        return (80, 200, 120)
    if pct < 85:
        return (240, 190, 60)
    return (235, 80, 80)


def draw_stats(lsize, rows, have_psutil):
    w, h = lsize
    img = Image.new("RGB", (w, h), (12, 14, 20))
    d = ImageDraw.Draw(img)
    if not rows:
        lines = ["Collecting..."] if have_psutil else ["Install psutil:", "pip install psutil"]
        font = fit_font(d, max(lines, key=len), w - 20, 20)
        for i, line in enumerate(lines):
            draw_centered(d, line, font, w / 2, h / 2 + (i - (len(lines) - 1) / 2) * 30, (255, 255, 255))
        return img
    pad = max(6, h // 40)
    rh = (h - 2 * pad) / len(rows)
    font = get_font(max(10, min(int(rh * 0.42), w // 9)))
    for i, (label, pct, text) in enumerate(rows):
        y = pad + i * rh
        d.text((pad, y + rh * 0.05), label, font=font, fill=(200, 205, 215))
        tw = text_size(d, text, font)[0]
        d.text((w - pad - tw, y + rh * 0.05), text, font=font, fill=(255, 255, 255))
        by0, by1 = y + rh * 0.60, y + rh * 0.82
        d.rounded_rectangle([pad, by0, w - pad, by1], radius=3, fill=(40, 44, 56))
        fill_x = pad + (w - 2 * pad) * max(0.0, min(100.0, pct)) / 100
        if fill_x > pad + 2:
            d.rounded_rectangle([pad, by0, fill_x, by1], radius=3, fill=bar_color(pct))
    return img


def draw_clock(lsize):
    w, h = lsize
    img = Image.new("RGB", (w, h), (10, 12, 18))
    d = ImageDraw.Draw(img)
    now = datetime.datetime.now()
    clock = now.strftime("%H:%M:%S")
    date = now.strftime("%a %d %b %Y")
    draw_centered(d, clock, fit_font(d, clock, w * 0.92, int(h * 0.35)), w / 2, h * 0.42, (255, 255, 255))
    draw_centered(d, date, fit_font(d, date, w * 0.9, int(h * 0.11)), w / 2, h * 0.72, (150, 160, 180))
    return img


_overlay_cache = {}


def add_overlay(base, rows, have_psutil):
    """Draws a translucent stats bar along the bottom of a picture."""
    w, h = base.size
    text = "   ".join(f"{l.replace(' temp', '')} {t}" for l, _, t in rows if l != "VRAM")
    text = text or ("..." if have_psutil else "install psutil")
    key = (w, h, text)
    ov = _overlay_cache.get(key)
    if ov is None:
        ov = Image.new("RGBA", (w, h), (0, 0, 0, 0))
        d = ImageDraw.Draw(ov)
        font = fit_font(d, text, w - 12, max(12, h // 12))
        tw, th, ox, oy = text_size(d, text, font)
        bar = th + 12
        d.rectangle([0, h - bar, w, h], fill=(0, 0, 0, 160))
        d.text(((w - tw) / 2 - ox, h - bar + 6 - oy), text, font=font, fill=(255, 255, 255, 255))
        if len(_overlay_cache) > 8:
            _overlay_cache.clear()
        _overlay_cache[key] = ov
    return Image.alpha_composite(base.convert("RGBA"), ov).convert("RGB")


# ------------------------------------------------------------------ playback engine
class Engine(threading.Thread):
    """Background thread: finds the screen, reconnects if it drops, plays the playlist."""

    def __init__(self, cfg):
        super().__init__(daemon=True)
        self.cfg = dict(cfg)
        self.cfg_lock = threading.Lock()
        self.stop_evt = threading.Event()
        self.reload_evt = threading.Event()
        self.paused = False
        self.test_mode = False
        self.status = "Starting..."
        self.activity = ""
        self.cache = {}
        self.bad = {}
        self.raw_cache = {}
        self.sampler = StatsSampler()
        self.sampler.start()

    # --- called from the UI thread
    def update_config(self, cfg):
        with self.cfg_lock:
            self.cfg = dict(cfg)
        self.reload_evt.set()

    def get_config(self):
        with self.cfg_lock:
            return dict(self.cfg)

    def set_paused(self, value):
        self.paused = value
        self.reload_evt.set()

    def set_test_mode(self, value):
        self.test_mode = value
        self.reload_evt.set()

    def stop(self):
        self.stop_evt.set()
        self.sampler.stop_evt.set()
        self.reload_evt.set()
        self.join(timeout=4)

    # --- thread body
    def run(self):
        while not self.stop_evt.is_set():
            wait = 3
            try:
                port = find_port()
                if not port:
                    self.status = "Screen not found - plug it in (retrying every few seconds)"
                    self.activity = ""
                else:
                    wait = self.session(port)
            except serial.SerialException as e:
                log.warning("Serial error: %s", e)
                self.status = "Lost the connection to the screen - reconnecting..."
                self.activity = ""
            except Exception as e:
                log.exception("Engine error")
                self.status = f"Error: {e} - retrying..."
                self.activity = ""
            self.stop_evt.wait(wait)

    def session(self, port):
        panel = Panel(port)
        try:
            info = panel.get_info()
            size = (int(info["width"]), int(info["height"]))
            model = str(info.get("model", ""))
            fw = str(info.get("version", "0"))
            low = model.lower()
            if "2.99" in low or "txw813-st7789-2.8inch" in low or "qspi" in low:
                self.status = f"Unsupported model type ({model}): it needs raw RGB565 frames."
                return 30
            try:
                panel.wrapped = tuple(int(x) for x in fw.split(".")) > (2, 8)
            except ValueError:
                panel.wrapped = True
            panel.start()
            self.status = f"Connected on {port}: {model}, {size[0]}x{size[1]}, firmware {fw}"
            log.info(self.status)
            applied = None
            while not self.stop_evt.is_set():
                self.reload_evt.clear()
                cfg = self.get_config()
                if cfg["brightness"] != applied:
                    panel.set_brightness(cfg["brightness"])
                    applied = cfg["brightness"]
                self.run_once(panel, size, cfg)
                if panel.failed:
                    raise serial.SerialException("screen stopped responding")
        finally:
            panel.close()
        return 3

    def aborting(self):
        return self.stop_evt.is_set() or self.reload_evt.is_set()

    def get_frames(self, path, size, cfg):
        key = (path, os.path.getmtime(path), size, cfg["rotate"], cfg["fit"], cfg["max_kb"], cfg["max_fps"])
        if key in self.bad:
            raise ValueError(self.bad[key])
        if key in self.cache:
            return self.cache[key]
        self.activity = f"Loading {os.path.basename(path)}..."
        try:
            frames = load_frames(path, size, cfg["fit"], cfg["rotate"], cfg["max_kb"] * 1024,
                                 cfg["max_fps"], self.aborting)
        except Aborted:
            raise
        except Exception as e:
            self.bad[key] = str(e)
            raise
        while len(self.cache) >= 8:
            self.cache.pop(next(iter(self.cache)))
        self.cache[key] = frames
        return frames

    def run_once(self, panel, size, cfg):
        rotate = cfg["rotate"]
        if self.paused:
            self.activity = "Paused (the screen keeps the last picture)"
            self.reload_evt.wait(1.0)
            return
        if self.test_mode:
            self.activity = "Showing the orientation test pattern"
            jpeg = encode_jpeg(orientation_pattern(size, rotate), cfg["max_kb"] * 1024)
            self.stream(panel, [(jpeg, 0.5)], None)
            return
        mode = cfg.get("mode", "playlist")
        if mode in ("stats", "clock"):
            self.play_live(panel, size, cfg, mode)
            return
        if mode == "picture":
            self.play_picture(panel, size, cfg)
            return
        if mode == "stats_gif":
            self.play_stats_gif(panel, size, cfg)
            return
        items = [p for p in cfg["playlist"] if os.path.isfile(p)]
        if not items:
            self.activity = "Playlist is empty - add some GIFs"
            lines = ["Hongtai Screen", "Add GIFs in the app"]
            jpeg = encode_jpeg(message_image(size, rotate, lines), cfg["max_kb"] * 1024)
            self.stream(panel, [(jpeg, 0.5)], None)
            return
        if cfg["shuffle"]:
            random.shuffle(items)
        played = False
        warning = ""
        for i, path in enumerate(items, 1):
            if self.aborting():
                return
            name = os.path.basename(path)
            try:
                frames = self.get_frames(path, size, cfg)
            except Aborted:
                return
            except Exception as e:
                log.warning("Skipped %s: %s", path, e)
                warning = f"Skipped {name}: {e}"
                self.activity = warning
                continue
            played = True
            self.activity = f"Playing {name} ({i}/{len(items)})"
            deadline = time.monotonic() + cfg["seconds_per_gif"] if len(items) > 1 else None
            self.stream(panel, frames, deadline)
        if not played:
            self.activity = warning or "Nothing could be played"
            self.reload_evt.wait(2.0)

    def show_message(self, panel, size, cfg, lines):
        jpeg = encode_jpeg(message_image(size, cfg["rotate"], lines), cfg["max_kb"] * 1024)
        self.stream(panel, [(jpeg, 0.5)], None)

    def play_picture(self, panel, size, cfg):
        path = cfg.get("picture", "")
        if not path or not os.path.isfile(path):
            self.activity = "Choose a picture or GIF for this mode"
            self.show_message(panel, size, cfg, ["Hongtai Screen", "Choose a picture in the app"])
            return
        try:
            frames = self.get_frames(path, size, cfg)
        except Aborted:
            return
        except Exception as e:
            log.warning("Could not show %s: %s", path, e)
            self.activity = f"Could not show {os.path.basename(path)}: {e}"
            self.reload_evt.wait(2.0)
            return
        self.activity = f"Showing {os.path.basename(path)}"
        self.stream(panel, frames, None)

    def pace(self, next_t, period):
        """Waits until next_t + period (wakes early on any change) and returns the new schedule time."""
        next_t += period
        now = time.perf_counter()
        if next_t > now:
            self.reload_evt.wait(next_t - now)
        elif now - next_t > 0.5:
            next_t = now                      # fell behind: do not catch up
        return next_t

    def prime_stats(self):
        self.sampler.want()
        if not self.sampler.data:
            self.sampler.data = self.sampler.sample()

    def play_live(self, panel, size, cfg, kind):
        rotate = cfg["rotate"]
        lsize = canvas_size(size, rotate)
        max_bytes = cfg["max_kb"] * 1024
        if kind == "stats":
            self.prime_stats()
            self.activity = "Showing live PC stats" + ("" if psutil else " (install psutil for CPU and RAM)")
        else:
            self.activity = "Showing the clock"
        period = 0.5 if kind == "clock" else 1.0
        next_t = time.perf_counter()
        while not self.aborting():
            if kind == "stats":
                self.sampler.want()
                img = draw_stats(lsize, stats_rows(self.sampler.data), psutil is not None)
            else:
                img = draw_clock(lsize)
            panel.send_frame(encode_jpeg(apply_rotation(img, rotate), max_bytes))
            if panel.failed:
                raise serial.SerialException("screen stopped responding")
            next_t = self.pace(next_t, period)

    def raw_frames(self, path, lsize, cfg):
        """Decoded picture frames at the logical screen size (before rotation)."""
        key = (path, os.path.getmtime(path), lsize, cfg["fit"], cfg["max_fps"])
        if key in self.raw_cache:
            return self.raw_cache[key]
        self.activity = f"Loading {os.path.basename(path)}..."
        min_delay = 1.0 / cfg["max_fps"]
        frames = []
        with Image.open(path) as img:
            for fr in ImageSequence.Iterator(img):
                if self.aborting():
                    raise Aborted()
                d = fr.info.get("duration", 100)
                if d < 20:
                    d = 100
                frames.append((fit_image(fr, lsize, cfg["fit"]), max(d / 1000.0, min_delay)))
        while len(self.raw_cache) >= 2:
            self.raw_cache.pop(next(iter(self.raw_cache)))
        self.raw_cache[key] = frames
        return frames

    def play_stats_gif(self, panel, size, cfg):
        path = cfg.get("picture", "")
        if not path or not os.path.isfile(path):
            self.activity = "Choose a GIF for this mode"
            self.show_message(panel, size, cfg, ["Hongtai Screen", "Choose a GIF in the app"])
            return
        rotate = cfg["rotate"]
        lsize = canvas_size(size, rotate)
        max_bytes = cfg["max_kb"] * 1024
        try:
            frames = self.raw_frames(path, lsize, cfg)
        except Aborted:
            return
        except Exception as e:
            log.warning("Could not load %s: %s", path, e)
            self.activity = f"Could not load {os.path.basename(path)}: {e}"
            self.reload_evt.wait(2.0)
            return
        if len(frames) == 1:
            frames = [(frames[0][0], 1.0)]     # still picture: refresh the numbers every second
        self.prime_stats()
        self.activity = f"Stats over {os.path.basename(path)}"
        next_t = time.perf_counter()
        while True:
            for base, delay in frames:
                if self.aborting():
                    return
                self.sampler.want()
                img = add_overlay(base, stats_rows(self.sampler.data), psutil is not None)
                try:
                    jpeg = encode_jpeg(apply_rotation(img, rotate), max_bytes)
                except ValueError as e:
                    self.activity = f"Frame too big: {e}"
                    self.reload_evt.wait(2.0)
                    return
                panel.send_frame(jpeg)
                if panel.failed:
                    raise serial.SerialException("screen stopped responding")
                next_t = self.pace(next_t, delay)

    def stream(self, panel, frames, deadline):
        next_t = time.perf_counter()
        while True:
            for jpeg, delay in frames:
                if self.aborting():
                    return
                if deadline is not None and time.monotonic() >= deadline:
                    return
                panel.send_frame(jpeg)
                if panel.failed:
                    raise serial.SerialException("screen stopped responding")
                next_t += delay
                now = time.perf_counter()
                if next_t > now:
                    self.reload_evt.wait(next_t - now)     # wakes early on any change
                elif now - next_t > 0.5:
                    next_t = now                           # fell behind: do not catch up


# ------------------------------------------------------------------ user interface
def tray_icon_image():
    img = Image.new("RGB", (64, 64), (25, 25, 35))
    d = ImageDraw.Draw(img)
    d.rectangle([6, 14, 58, 50], outline=(255, 255, 255), width=3)
    d.rectangle([14, 22, 28, 34], fill=(255, 80, 80))
    d.rectangle([32, 22, 50, 34], fill=(80, 200, 120))
    d.rectangle([14, 38, 50, 44], fill=(90, 140, 255))
    return img


class App:
    def __init__(self, root, cfg, start_minimized):
        self.root = root
        self.cfg = cfg
        self.playlist = list(cfg["playlist"])
        self.picture = cfg["picture"]
        self.apply_job = None
        self.q = queue.Queue()
        self.tray = None
        self.engine = Engine(cfg)

        root.title(APP_NAME)
        root.minsize(680, 460)
        self.build_ui()
        self.engine.start()
        self.setup_tray()
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        if start_minimized:
            root.after(150, self.hide)
        self.poll()

    # --- layout
    def build_ui(self):
        c = self.cfg
        main = ttk.Frame(self.root, padding=10)
        main.pack(fill="both", expand=True)
        main.columnconfigure(0, weight=1)
        main.rowconfigure(2, weight=1)

        st = ttk.LabelFrame(main, text="Screen", padding=6)
        st.grid(row=0, column=0, columnspan=2, sticky="ew")
        self.lbl_status = ttk.Label(st, text="Starting...", wraplength=640)
        self.lbl_status.pack(anchor="w")
        self.lbl_activity = ttk.Label(st, text="", wraplength=640, foreground="#555")
        self.lbl_activity.pack(anchor="w")

        mf = ttk.LabelFrame(main, text="Mode", padding=6)
        mf.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(8, 0))
        mf.columnconfigure(0, weight=1)
        self.v_mode = tk.StringVar(value=c["mode"])
        rf = ttk.Frame(mf)
        rf.grid(row=0, column=0, sticky="w")
        for key, label in MODE_LABELS.items():
            ttk.Radiobutton(rf, text=label, value=key, variable=self.v_mode).pack(side="left", padx=(0, 14))
        pf = ttk.Frame(mf)
        pf.grid(row=1, column=0, sticky="ew", pady=(6, 0))
        ttk.Label(pf, text="Picture / GIF for the last two modes:").pack(side="left")
        self.v_picture = tk.StringVar(value=self.picture or "(none chosen)")
        ttk.Entry(pf, textvariable=self.v_picture, state="readonly").pack(side="left", fill="x", expand=True, padx=6)
        ttk.Button(pf, text="Choose...", command=self.choose_picture).pack(side="left")

        pl = ttk.LabelFrame(main, text="Playlist (used in Playlist mode, plays top to bottom)", padding=6)
        pl.grid(row=2, column=0, sticky="nsew", pady=8, padx=(0, 8))
        pl.columnconfigure(0, weight=1)
        pl.rowconfigure(0, weight=1)
        self.listbox = tk.Listbox(pl, selectmode="extended", activestyle="none", exportselection=False)
        sb = ttk.Scrollbar(pl, command=self.listbox.yview)
        self.listbox.configure(yscrollcommand=sb.set)
        self.listbox.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")
        btns = ttk.Frame(pl)
        btns.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(6, 0))
        for text, cmd in (("Add GIFs...", self.add_files), ("Add folder...", self.add_folder),
                          ("Remove", self.remove_selected), ("Up", lambda: self.move(-1)),
                          ("Down", lambda: self.move(1)), ("Clear", self.clear)):
            ttk.Button(btns, text=text, command=cmd, width=11 if len(text) > 5 else 6).pack(side="left", padx=(0, 4))

        sf = ttk.LabelFrame(main, text="Settings", padding=8)
        sf.grid(row=2, column=1, sticky="ns", pady=8)
        self.v_secs = tk.IntVar(value=c["seconds_per_gif"])
        self.v_shuffle = tk.BooleanVar(value=c["shuffle"])
        self.v_rotate = tk.StringVar(value=str(c["rotate"]))
        self.v_fit = tk.StringVar(value=c["fit"])
        self.v_bright = tk.IntVar(value=c["brightness"])
        self.v_fps = tk.IntVar(value=c["max_fps"])
        self.v_kb = tk.IntVar(value=c["max_kb"])

        def row(r, label, widget):
            ttk.Label(sf, text=label).grid(row=r, column=0, sticky="w", pady=3, padx=(0, 8))
            widget.grid(row=r, column=1, sticky="ew", pady=3)

        row(0, "Seconds per GIF", ttk.Spinbox(sf, from_=1, to=3600, textvariable=self.v_secs, width=7))
        row(1, "Rotation", ttk.Combobox(sf, textvariable=self.v_rotate, values=("0", "90", "180", "270"),
                                        state="readonly", width=6))
        row(2, "Fit", ttk.Combobox(sf, textvariable=self.v_fit, values=("contain", "cover", "stretch"),
                                   state="readonly", width=8))
        row(3, "Brightness", tk.Scale(sf, from_=0, to=100, orient="horizontal", variable=self.v_bright,
                                      length=130, showvalue=True))
        row(4, "Max FPS", ttk.Spinbox(sf, from_=1, to=30, textvariable=self.v_fps, width=7))
        row(5, "Max frame KB", ttk.Spinbox(sf, from_=5, to=60, textvariable=self.v_kb, width=7))
        ttk.Checkbutton(sf, text="Shuffle", variable=self.v_shuffle).grid(row=6, column=0, columnspan=2,
                                                                         sticky="w", pady=3)
        self.v_autostart = tk.BooleanVar(value=autostart_enabled())
        cb = ttk.Checkbutton(sf, text="Start with Windows", variable=self.v_autostart,
                             command=self.toggle_autostart)
        cb.grid(row=7, column=0, columnspan=2, sticky="w", pady=(10, 3))
        if winreg is None:
            cb.state(["disabled"])

        for var in (self.v_secs, self.v_shuffle, self.v_rotate, self.v_fit, self.v_bright, self.v_fps,
                    self.v_kb, self.v_mode):
            var.trace_add("write", lambda *a: self.schedule_apply())

        bottom = ttk.Frame(main)
        bottom.grid(row=3, column=0, columnspan=2, sticky="ew")
        self.btn_pause = ttk.Button(bottom, text="Pause", command=self.toggle_pause)
        self.btn_pause.pack(side="left", padx=(0, 6))
        self.btn_test = ttk.Button(bottom, text="Orientation test", command=self.toggle_test)
        self.btn_test.pack(side="left", padx=(0, 6))
        ttk.Button(bottom, text="Quit", command=self.quit).pack(side="right")
        hint = ("Closing the window sends the app to the tray; use Quit to stop it." if pystray
                else "Closing the window quits the app (install pystray for a tray icon).")
        ttk.Label(main, text=hint + "  Jungle Leopard must be closed.", foreground="#777").grid(
            row=4, column=0, columnspan=2, sticky="w", pady=(6, 0))
        self.refresh_list()

    # --- playlist
    def refresh_list(self, select=()):
        self.listbox.delete(0, "end")
        for p in self.playlist:
            self.listbox.insert("end", p)
        for i in select:
            self.listbox.selection_set(i)

    def add_files(self):
        files = filedialog.askopenfilenames(
            title="Choose GIFs or pictures",
            filetypes=[("Images", "*.gif *.png *.jpg *.jpeg *.bmp *.webp"), ("All files", "*.*")])
        if files:
            self.playlist.extend(os.path.normpath(f) for f in files)
            self.refresh_list()
            self.apply()

    def add_folder(self):
        folder = filedialog.askdirectory(title="Choose a folder with GIFs")
        if folder:
            names = sorted(n for n in os.listdir(folder) if n.lower().endswith(IMAGE_EXT))
            self.playlist.extend(os.path.normpath(os.path.join(folder, n)) for n in names)
            self.refresh_list()
            self.apply()

    def remove_selected(self):
        sel = set(self.listbox.curselection())
        if sel:
            self.playlist = [p for i, p in enumerate(self.playlist) if i not in sel]
            self.refresh_list()
            self.apply()

    def move(self, step):
        sel = list(self.listbox.curselection())
        if len(sel) != 1:
            return
        i, j = sel[0], sel[0] + step
        if 0 <= j < len(self.playlist):
            self.playlist[i], self.playlist[j] = self.playlist[j], self.playlist[i]
            self.refresh_list([j])
            self.apply()

    def clear(self):
        if self.playlist and messagebox.askyesno(APP_NAME, "Remove everything from the playlist?"):
            self.playlist = []
            self.refresh_list()
            self.apply()

    # --- settings
    def choose_picture(self):
        f = filedialog.askopenfilename(
            title="Choose a picture or GIF",
            filetypes=[("Images", "*.gif *.png *.jpg *.jpeg *.bmp *.webp"), ("All files", "*.*")])
        if f:
            self.picture = os.path.normpath(f)
            self.v_picture.set(self.picture)
            self.apply()

    def collect(self):
        try:
            return {
                "playlist": list(self.playlist),
                "seconds_per_gif": max(1, int(self.v_secs.get())),
                "shuffle": bool(self.v_shuffle.get()),
                "rotate": int(self.v_rotate.get()),
                "fit": self.v_fit.get(),
                "brightness": max(0, min(100, int(self.v_bright.get()))),
                "max_fps": max(1, min(30, int(self.v_fps.get()))),
                "max_kb": max(5, min(60, int(self.v_kb.get()))),
                "mode": self.v_mode.get(),
                "picture": self.picture,
            }
        except (tk.TclError, ValueError):
            return None            # a box is half-typed; wait for the next change

    def schedule_apply(self):
        if self.apply_job:
            self.root.after_cancel(self.apply_job)
        self.apply_job = self.root.after(500, self.apply)

    def apply(self):
        self.apply_job = None
        cfg = self.collect()
        if cfg is None:
            return
        self.cfg = cfg
        save_config(cfg)
        self.engine.update_config(cfg)

    def toggle_autostart(self):
        want = self.v_autostart.get()
        try:
            set_autostart(want)
        except Exception as e:
            log.exception("Autostart change failed")
            self.v_autostart.set(not want)
            messagebox.showerror(APP_NAME, f"Could not change the Windows startup entry:\n{e}")

    def toggle_pause(self):
        paused = not self.engine.paused
        self.engine.set_paused(paused)
        self.btn_pause.configure(text="Resume" if paused else "Pause")

    def toggle_test(self):
        on = not self.engine.test_mode
        self.engine.set_test_mode(on)
        self.btn_test.configure(text="Back to playlist" if on else "Orientation test")

    # --- tray / window
    def setup_tray(self):
        if pystray is None:
            return
        try:
            modes = pystray.Menu(*[
                pystray.MenuItem(label, self._mode_action(key), checked=self._mode_checked(key), radio=True)
                for key, label in MODE_LABELS.items()])
            menu = pystray.Menu(
                pystray.MenuItem("Open", lambda icon, item: self.q.put("show"), default=True),
                pystray.MenuItem("Mode", modes),
                pystray.MenuItem("Pause / resume", lambda icon, item: self.q.put("pause")),
                pystray.MenuItem("Quit", lambda icon, item: self.q.put("quit")))
            self.tray = pystray.Icon("HongtaiScreen", tray_icon_image(), APP_NAME, menu)
            self.tray.run_detached()
        except Exception:
            log.exception("Tray icon failed")
            self.tray = None

    def _mode_action(self, mode):
        return lambda icon, item: self.q.put(("mode", mode))

    def _mode_checked(self, mode):
        return lambda item: self.engine.get_config().get("mode") == mode

    def hide(self):
        if self.tray:
            self.root.withdraw()
        else:
            self.root.iconify()

    def show(self):
        self.root.deiconify()
        self.root.lift()
        self.root.focus_force()

    def on_close(self):
        if self.tray:
            self.root.withdraw()
        else:
            self.quit()

    def quit(self):
        if self.apply_job:
            self.apply()
        try:
            if self.tray:
                self.tray.stop()
        except Exception:
            pass
        self.engine.stop()
        self.root.destroy()

    def poll(self):
        try:
            while True:
                cmd = self.q.get_nowait()
                if isinstance(cmd, tuple):          # ("mode", name) from the tray menu
                    self.v_mode.set(cmd[1])
                    continue
                if cmd == "show":
                    self.show()
                elif cmd == "pause":
                    self.toggle_pause()
                elif cmd == "quit":
                    self.quit()
                    return
        except queue.Empty:
            pass
        self.lbl_status.configure(text=self.engine.status)
        self.lbl_activity.configure(text=self.engine.activity)
        self.root.after(300, self.poll)


# ------------------------------------------------------------------ main
_lock_socket = None


def acquire_lock():
    global _lock_socket
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        s.bind(("127.0.0.1", LOCK_PORT))
    except OSError:
        s.close()
        return False
    _lock_socket = s
    return True


def main():
    ap = argparse.ArgumentParser(description=APP_NAME)
    ap.add_argument("--minimized", action="store_true", help="start hidden (used by Start with Windows)")
    args = ap.parse_args()

    os.makedirs(CONFIG_DIR, exist_ok=True)
    handler = RotatingFileHandler(LOG_FILE, maxBytes=500_000, backupCount=2, encoding="utf-8")
    handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
    log.addHandler(handler)
    log.setLevel(logging.INFO)

    if not acquire_lock():
        if not args.minimized:
            r = tk.Tk()
            r.withdraw()
            messagebox.showinfo(APP_NAME, "The app is already running (look for its icon in the tray).")
        return

    try:                                    # sharper text on high-DPI screens
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass

    root = tk.Tk()
    App(root, load_config(), args.minimized)
    root.mainloop()


if __name__ == "__main__":
    main()
