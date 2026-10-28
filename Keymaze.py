#!/usr/bin/env python3
"""
KEYMAZE - find the key, unlock the door, escape the maze.

Pure Python 3. Uses only the standard library (tkinter ships with Python):

    python keymaze.py

Put your sprite next to this file as  player.png  (PNG with transparency
works best).  If Pillow is installed it is used for smooth scaling; without
it the game falls back to tkinter's built-in image scaling.

Controls
    Arrow keys / WASD   one tile per tap; hold briefly for 2x speed
                        (also move the cursor on the level screen)
    Esc or P            pause / resume / go back
    R                   restart the level
    F11                 toggle fullscreen
    Enter / Space       confirm
    M                   toggle sound effects
    K                   DEV CHEAT: toggle "all 9 level keys" (session only)

Progression
    Clearing a level for the first time earns that level's LEVEL KEY.
    Level N needs N-1 level keys to unlock (level 1 is always open).
"""
import json
import math
import os
import random
import struct
import tempfile
import time
import tkinter as tk
import tkinter.font as tkfont
import wave
from collections import deque
from fractions import Fraction

try:                                    # Windows' standard-library sound player
    import winsound
except ImportError:                      # pragma: no cover - other platforms
    winsound = None

try:                                    # optional: smoother sprite scaling
    from PIL import Image, ImageTk
    HAVE_PIL = True
except Exception:                       # pragma: no cover
    HAVE_PIL = False

# --------------------------------------------------------------------------
#  Look & feel / constants
# --------------------------------------------------------------------------
C = dict(
    bg="#070b16", panel="#121a30", panel2="#1a2444", edge="#2c3d70",
    text="#e8eeff", dim="#8593bd", accent="#35e0ff", accent2="#7c5cff",
    gold="#ffcc33", good="#3ddc97", bad="#ff5470", wall="#4ea8ff",
    floor="#0a1224", white="#ffffff", black="#000000", dev="#ff9a3d",
)

NUM_LEVELS = 10
PLAYER_FILE = "player.png"
SAVE_FILE = os.path.join(os.path.expanduser("~"), ".keymaze_save.json")


def mix(a, b, t):
    """Blend hex colour a towards b by t (0..1)."""
    t = max(0.0, min(1.0, t))
    ca = [int(a[i:i + 2], 16) for i in (1, 3, 5)]
    cb = [int(b[i:i + 2], 16) for i in (1, 3, 5)]
    return "#%02x%02x%02x" % tuple(int(ca[i] + (cb[i] - ca[i]) * t) for i in range(3))


def clamp(v, lo, hi):
    return max(lo, min(hi, v))


def ease(t):
    t = clamp(t, 0.0, 1.0)
    return t * t * (3 - 2 * t)


def fmt_time(t):
    m = int(t // 60)
    return "%02d:%04.1f" % (m, t - m * 60)


def keys_needed(level_no):
    """Level N needs N-1 level keys (level 1 is free)."""
    return level_no - 1


class SoundEffects:
    """Small synthesized WAV cues; uses only Python's standard library."""

    RATE = 22050
    CUES = {
        "step": ((330, 0.035),),
        "blocked": ((190, 0.07), (135, 0.09)),
        "key": ((660, 0.075), (880, 0.075), (1100, 0.12)),
        "clear": ((523, 0.08), (659, 0.08), (784, 0.08), (988, 0.08), (1175, 0.16)),
        "ui": ((720, 0.045), (960, 0.055)),
    }

    def __init__(self, root):
        self.root = root
        self.enabled = True
        self.paths = {}
        self.last_played = {}
        if winsound is not None:
            self._prepare_files()

    def _prepare_files(self):
        folder = os.path.join(tempfile.gettempdir(), "keymaze-sfx")
        try:
            os.makedirs(folder, exist_ok=True)
            for name, notes in self.CUES.items():
                path = os.path.join(folder, name + ".wav")
                if not os.path.isfile(path):
                    with wave.open(path, "wb") as out:
                        out.setnchannels(1)
                        out.setsampwidth(2)
                        out.setframerate(self.RATE)
                        for frequency, seconds in notes:
                            count = int(self.RATE * seconds)
                            samples = bytearray()
                            for i in range(count):
                                fade_in = min(1.0, i / max(1, self.RATE * 0.008))
                                fade_out = min(1.0, (count - i) / max(1, self.RATE * 0.018))
                                amp = 4200 * min(fade_in, fade_out)
                                value = int(amp * math.sin(2 * math.pi * frequency * i / self.RATE))
                                samples.extend(struct.pack("<h", value))
                            out.writeframes(samples)
                self.paths[name] = path
        except OSError:
            self.paths.clear()

    def play(self, name):
        if not self.enabled:
            return
        now = time.perf_counter()
        if name == "blocked" and now - self.last_played.get(name, 0.0) < 0.18:
            return
        self.last_played[name] = now
        path = self.paths.get(name)
        if winsound is not None and path:
            try:
                winsound.PlaySound(path, winsound.SND_FILENAME | winsound.SND_ASYNC | winsound.SND_NODEFAULT)
                return
            except RuntimeError:
                pass
        if name == "step":
            return
        # Tk's native alert is a quiet fallback when WAV playback is absent.
        try:
            self.root.bell()
        except tk.TclError:
            pass

    def toggle(self):
        self.enabled = not self.enabled
        if self.enabled:
            self.play("ui")


# --------------------------------------------------------------------------
#  Maze model
# --------------------------------------------------------------------------
UP, RT, DN, LT = 1, 2, 4, 8
DIRS = (UP, RT, DN, LT)
DX = {UP: 0, RT: 1, DN: 0, LT: -1}
DY = {UP: -1, RT: 0, DN: 1, LT: 0}
OPP = {UP: DN, RT: LT, DN: UP, LT: RT}
KEYDIR = {"up": UP, "w": UP, "down": DN, "s": DN, "left": LT, "a": LT, "right": RT, "d": RT}


def level_dims(level_no):
    """Maze size for the n-th level (1-based): grows every level."""
    cols = 9 + 2 * level_no
    rows = int(round(cols * 0.6))
    return cols, rows


class Maze:
    """Perfect maze (recursive backtracker) plus a few loops.

    w[y][x] is a bitmask of the walls that are still standing around a cell.
    The start is a random corner, the exit door sits on the outer wall far
    from the start, and the maze key is dropped somewhere random in between.
    """

    def __init__(self, cols, rows, rng, loops=0.04):
        self.cols, self.rows = cols, rows
        self.w = [[15] * cols for _ in range(rows)]
        self.start = rng.choice([(0, 0), (cols - 1, 0), (0, rows - 1), (cols - 1, rows - 1)])
        self._carve(rng)
        self._add_loops(rng, loops)

        d0 = self.bfs(self.start)
        border = [(x, y) for y in range(rows) for x in range(cols)
                  if (x in (0, cols - 1) or y in (0, rows - 1)) and (x, y) != self.start]
        border.sort(key=lambda p: -d0[p[1]][p[0]])
        self.exit = rng.choice(border[:max(4, len(border) // 6)])
        ex, ey = self.exit
        outs = []
        if ey == 0:
            outs.append(UP)
        if ey == rows - 1:
            outs.append(DN)
        if ex == 0:
            outs.append(LT)
        if ex == cols - 1:
            outs.append(RT)
        self.door = rng.choice(outs)

        far = max(max(r) for r in d0)
        de = self.bfs(self.exit)
        cells = [(x, y) for y in range(rows) for x in range(cols)
                 if (x, y) not in (self.start, self.exit)]
        good = [p for p in cells
                if d0[p[1]][p[0]] >= 0.35 * far and de[p[1]][p[0]] >= 0.25 * far]
        dead = [p for p in good if bin(self.w[p[1]][p[0]]).count("1") == 3]
        pool = dead if (dead and rng.random() < 0.7) else (good or cells)
        self.key = rng.choice(pool)
        dk = self.bfs(self.key)
        self.par_steps = d0[self.key[1]][self.key[0]] + dk[ey][ex] + 1

    def _carve(self, rng):
        seen = {self.start}
        stack = [self.start]
        while stack:
            x, y = stack[-1]
            opts = []
            for k in DIRS:
                nx, ny = x + DX[k], y + DY[k]
                if 0 <= nx < self.cols and 0 <= ny < self.rows and (nx, ny) not in seen:
                    opts.append((k, nx, ny))
            if opts:
                k, nx, ny = rng.choice(opts)
                self.w[y][x] &= ~k
                self.w[ny][nx] &= ~OPP[k]
                seen.add((nx, ny))
                stack.append((nx, ny))
            else:
                stack.pop()

    def _add_loops(self, rng, amount):
        for _ in range(int(self.cols * self.rows * amount)):
            x, y, k = rng.randrange(self.cols), rng.randrange(self.rows), rng.choice(DIRS)
            nx, ny = x + DX[k], y + DY[k]
            if 0 <= nx < self.cols and 0 <= ny < self.rows and self.w[y][x] & k:
                self.w[y][x] &= ~k
                self.w[ny][nx] &= ~OPP[k]

    def bfs(self, src):
        d = [[-1] * self.cols for _ in range(self.rows)]
        d[src[1]][src[0]] = 0
        q = deque([src])
        while q:
            x, y = q.popleft()
            for k in DIRS:
                if self.w[y][x] & k:
                    continue
                nx, ny = x + DX[k], y + DY[k]
                if 0 <= nx < self.cols and 0 <= ny < self.rows and d[ny][nx] < 0:
                    d[ny][nx] = d[y][x] + 1
                    q.append((nx, ny))
        return d


# --------------------------------------------------------------------------
#  Application
# --------------------------------------------------------------------------
GAME_STATES = ("intro", "playing", "paused", "levelclear")
BLOBS = ((C["accent2"], 0.15, 0.20, 0.0), (C["accent"], 0.88, 0.80, 2.1), (C["accent2"], 0.70, 0.12, 4.2))


class App:
    MOVE_SPEED = 3.0  # maze cells per second while a direction is held
    HOLD_ACCEL_DELAY = 0.18  # seconds before held movement doubles in speed
    HOLD_ACCEL_MULTIPLIER = 2.0
    INTRO = 1.5      # seconds of the "LEVEL n" banner

    def __init__(self):
        self.root = tk.Tk()
        self.root.title("KEYMAZE")
        self.root.geometry("1180x760")
        self.root.minsize(760, 520)
        self.root.configure(bg=C["bg"])
        self.sfx = SoundEffects(self.root)
        self.cv = tk.Canvas(self.root, bg=C["bg"], highlightthickness=0, bd=0)
        self.cv.pack(fill="both", expand=True)

        fams = set(tkfont.families(self.root))
        self.fam = next((f for f in ("Segoe UI", "SF Pro Display", "Helvetica Neue", "Inter", "Ubuntu",
                                     "Cantarell", "DejaVu Sans", "Arial") if f in fams), "Helvetica")
        self.mono = next((f for f in ("Consolas", "Menlo", "DejaVu Sans Mono", "Liberation Mono",
                                      "Courier New") if f in fams), "Courier")
        self.fonts = {}

        self.W, self.H, self.ui = 1180, 760, 1.0
        self.t = 0.0
        self.last = time.perf_counter()
        self.mouse = (-1, -1)
        self.mouse_moved = False
        self.buttons = []
        self.hover = False
        self.cursor = ""
        self.fullscreen = False
        self.state = "menu"
        self.rng = random.Random()

        # progression / persistence
        self.earned = set()          # level keys really earned (saved)
        self.best = {}               # "level" -> {"time", "score", "stars"} (saved)
        self.has_save = False        # a prior playthrough with saved progress exists
        self.cheat = False           # dev cheat, session only, never saved
        self.load_save()
        self.sel = 0                 # highlighted tile on the level screen

        # level state
        self.idx = 0
        self.maze = None
        self.has_static = False
        self.needs_layout = True
        self.pad = 34
        self.cs = 20
        self.ox = self.oy = 0
        self.held, self.rel = [], {}
        self.key_down_at = {}
        self.fxs = []
        self.toast = ("", C["text"])
        self.toast_t = 0.0
        self.flash = 0.0
        self.lc_t = self.intro_t = 0.0
        self.got_key, self.unlock_msg, self.last_newbest = False, "", False

        self.player_src = self.player_pil = None
        self.pcache = {}
        self.load_player()

        self.parts = [[random.random(), random.random(), random.uniform(-0.01, 0.01),
                       random.uniform(-0.03, -0.006), random.uniform(1.2, 3.2),
                       random.uniform(0, 6.28)] for _ in range(46)]

        r = self.root
        r.bind("<KeyPress>", self.on_key)
        r.bind("<KeyRelease>", self.on_key_up)
        self.cv.bind("<Button-1>", self.on_click)
        self.cv.bind("<Motion>", self.on_motion)
        self.cv.bind("<Leave>", lambda e: setattr(self, "mouse", (-1, -1)))
        self.cv.bind("<Configure>", self.on_resize)
        r.after(16, self.tick)

    def run(self):
        self.root.mainloop()

    # ------------------------------------------------------------ save data
    def load_save(self):
        self.earned.clear()
        self.best.clear()
        self.has_save = False
        try:
            with open(SAVE_FILE, "r", encoding="utf-8") as f:
                d = json.load(f)
            if not isinstance(d, dict):
                return
            self.earned = {int(k) for k in d.get("keys", []) if 1 <= int(k) <= NUM_LEVELS}
            for k, v in (d.get("best") or {}).items():
                if 1 <= int(k) <= NUM_LEVELS and isinstance(v, dict):
                    self.best[str(int(k))] = {"time": float(v["time"]), "score": int(v["score"]),
                                              "stars": int(v["stars"])}
            self.has_save = bool(self.earned or self.best)
        except Exception:
            pass

    def save_data(self):
        try:
            with open(SAVE_FILE, "w", encoding="utf-8") as f:
                json.dump({"keys": sorted(self.earned), "best": self.best}, f)
            self.has_save = bool(self.earned or self.best)
        except Exception:
            pass

    # level keys ---------------------------------------------------------
    def keyset(self):
        """Keys currently in effect. The dev cheat adds keys 1-9 on top."""
        return (set(range(1, NUM_LEVELS)) | self.earned) if self.cheat else set(self.earned)

    def is_unlocked(self, level_no):
        return len(self.keyset()) >= keys_needed(level_no)

    # ------------------------------------------------------------ player art
    def load_player(self):
        here = os.path.dirname(os.path.abspath(__file__))
        for base in (here, os.getcwd()):
            p = os.path.join(base, PLAYER_FILE)
            if not os.path.isfile(p):
                continue
            try:
                if HAVE_PIL:
                    self.player_pil = Image.open(p).convert("RGBA")
                else:
                    self.player_src = tk.PhotoImage(file=p)
                return
            except Exception as e:
                print("[keymaze] could not load %s: %s" % (p, e))
        print("[keymaze] %s not found next to keymaze.py - showing a placeholder marker." % PLAYER_FILE)

    @property
    def has_player_art(self):
        return self.player_pil is not None or self.player_src is not None

    def player_image(self, target):
        """Player sprite scaled so its longest side is ~target pixels (cached)."""
        target = max(8, int(target))
        img = self.pcache.get(target)
        if img is not None:
            return img
        if len(self.pcache) > 24:
            self.pcache.clear()
        if self.player_pil is not None:
            w, h = self.player_pil.size
            s = target / float(max(w, h))
            im = self.player_pil.resize((max(1, int(w * s)), max(1, int(h * s))), Image.LANCZOS)
            img = ImageTk.PhotoImage(im)
        else:
            src = self.player_src
            sub = max(1, max(src.width(), src.height()) // target)
            img = src.subsample(sub, sub) if sub > 1 else src
            f = Fraction(target, max(img.width(), img.height())).limit_denominator(8)
            if f.numerator > 1:
                img = img.zoom(f.numerator, f.numerator)
            if f.denominator > 1:
                img = img.subsample(f.denominator, f.denominator)
        self.pcache[target] = img
        return img

    # ----------------------------------------------------------------- misc
    def font(self, px, bold=False, mono=False):
        px = max(8, int(px * self.ui))
        key = (mono, px, bold)
        if key not in self.fonts:
            self.fonts[key] = tkfont.Font(family=self.mono if mono else self.fam, size=-px,
                                          weight="bold" if bold else "normal")
        return self.fonts[key]

    def on_motion(self, e):
        self.mouse = (e.x, e.y)
        self.mouse_moved = True

    def on_resize(self, e):
        if (e.width, e.height) != (self.W, self.H) and e.width > 50:
            self.W, self.H = e.width, e.height
            self.ui = clamp(min(self.W / 1100.0, self.H / 700.0), 0.75, 2.4)
            self.needs_layout = True

    def toggle_fs(self):
        self.fullscreen = not self.fullscreen
        try:
            self.root.attributes("-fullscreen", self.fullscreen)
        except tk.TclError:
            pass

    # ------------------------------------------------------------ game flow
    def to_menu(self):
        self.state = "menu"
        self.held.clear()
        self.key_down_at.clear()

    def load_game(self):
        """Restore the last saved progression and open level select."""
        self.cheat = False
        self.load_save()
        self.to_select()

    def new_game(self):
        """Start a clean run with no earned keys or level records."""
        self.earned.clear()
        self.best.clear()
        self.cheat = False
        self.save_data()
        self.to_select(0)

    def request_new_game(self):
        if self.has_save:
            self.state = "newgame_confirm"
        else:
            self.new_game()

    def cancel_new_game(self):
        self.state = "menu"

    def to_select(self, sel=None):
        self.state = "select"
        self.held.clear()
        self.key_down_at.clear()
        if sel is None:
            sel = next((i for i in range(NUM_LEVELS)
                        if self.is_unlocked(i + 1) and (i + 1) not in self.earned), 0)
        self.sel = int(clamp(sel, 0, NUM_LEVELS - 1))

    def try_select(self, i):
        lvl = i + 1
        if self.is_unlocked(lvl):
            self.start_level(i)
        else:
            need, have = keys_needed(lvl), len(self.keyset())
            self.show_toast("Level %d needs %d level key%s - you have %d."
                            % (lvl, need, "" if need == 1 else "s", have), C["bad"])

    def start_level(self, i, new=True):
        self.idx = i
        if new or self.maze is None:
            self.maze = Maze(*level_dims(i + 1), self.rng, loops=0.03 + 0.004 * (i + 1))
        m = self.maze
        self.cell = m.start
        self.fx, self.fy = m.start
        self.target = m.start
        self.moving = self.exiting = False
        self.move_progress = 0.0
        self.has_key = self.door_open = False
        self.elapsed = 0.0
        self.held.clear()
        self.key_down_at.clear()
        self.fxs, self.toast_t, self.flash = [], 0.0, 0.0
        self.par_time = m.par_steps / self.MOVE_SPEED * 1.4
        self.state = "intro"
        self.intro_t = 0.0
        self.needs_layout = True

    def restart_level(self):
        if self.maze:
            self.start_level(self.idx, new=False)      # same maze, same key spot

    def toggle_pause(self):
        if self.state == "playing":
            self.state = "paused"
        elif self.state == "paused":
            self.state = "playing"

    def score_for(self, t):
        base = 1000 + 100 * self.idx
        return int(round(base * clamp(self.par_time / max(t, 1e-6), 0.05, 1.0)))

    def stars_for(self, t):
        r = self.par_time / max(t, 1e-6)
        return 3 if r >= 0.75 else (2 if r >= 0.45 else 1)

    def level_complete(self):
        self.sfx.play("clear")
        lvl = self.idx + 1
        gain = self.score_for(self.elapsed)
        stars = self.stars_for(self.elapsed)
        self.last_gain, self.last_stars, self.last_time = gain, stars, self.elapsed

        before = len(self.keyset())
        self.got_key = lvl not in self.earned
        if self.got_key:
            self.earned.add(lvl)
        after = len(self.keyset())
        newly = [L for L in range(2, NUM_LEVELS + 1) if before < keys_needed(L) <= after]
        self.unlock_msg = ""
        if newly:
            self.unlock_msg = ("Level %d unlocked!" % newly[0]) if len(newly) == 1 else \
                ("Levels %s unlocked!" % ", ".join(str(n) for n in newly))

        prev = self.best.get(str(lvl))
        self.last_newbest = prev is not None and gain > prev["score"]
        if prev is None or gain > prev["score"]:
            self.best[str(lvl)] = {"time": round(self.elapsed, 2), "score": gain, "stars": stars}
        self.save_data()

        self.state = "levelclear"
        self.lc_t = 0.0
        for _ in range(46):
            a = random.uniform(0, 6.283)
            sp = random.uniform(1.5, 4.5)
            self.fxs.append([self.fx, self.fy, math.cos(a) * sp, math.sin(a) * sp,
                             random.uniform(0.6, 1.2),
                             random.choice([C["gold"], C["accent"], C["good"], C["white"], C["accent2"]])])

    def has_next(self):
        return self.idx + 1 < NUM_LEVELS and self.is_unlocked(self.idx + 2)

    def clear_primary(self):
        if self.has_next():
            self.start_level(self.idx + 1)
        else:
            self.start_level(self.idx)              # play again: brand-new maze

    def clear_to_select(self):
        self.to_select(self.idx + 1 if self.has_next() else self.idx)

    def pickup(self):
        self.sfx.play("key")
        self.has_key = self.door_open = True
        kx, ky = self.cell
        for _ in range(32):
            a = random.uniform(0, 6.283)
            sp = random.uniform(1.0, 3.2)
            self.fxs.append([kx, ky, math.cos(a) * sp, math.sin(a) * sp, random.uniform(0.5, 0.9),
                             random.choice([C["gold"], C["white"], C["accent"]])])
        self.flash = 1.0
        self.show_toast("Key found! The exit door is unlocked.", C["good"])

    def show_toast(self, s, col):
        self.toast, self.toast_t = (s, col), 1.8

    def toggle_cheat(self):
        self.cheat = not self.cheat
        self.sfx.play("ui")
        if self.cheat:
            self.show_toast("DEV: all 9 level keys granted - every level unlocked", C["dev"])
        else:
            self.show_toast("DEV: cheat off - back to your real keys", C["dev"])

    # ---------------------------------------------------------------- input
    def on_key(self, e):
        k = e.keysym.lower()
        nav = {"left": -1, "a": -1, "right": 1, "d": 1, "up": -5, "w": -5, "down": 5, "s": 5}
        if k == "k":
            self.toggle_cheat()
        elif k == "m":
            self.sfx.toggle()
            self.show_toast("Sound on" if self.sfx.enabled else "Sound off", C["accent"])
        elif self.state == "select" and k in nav:
            self.sel = int(clamp(self.sel + nav[k], 0, NUM_LEVELS - 1))
        elif k in KEYDIR:
            if k in self.rel:
                self.root.after_cancel(self.rel.pop(k))
            self.key_down_at.setdefault(k, time.perf_counter())
            if k in self.held:
                self.held.remove(k)
            self.held.append(k)
            if self.state == "intro":
                self.intro_t = self.INTRO
        elif k in ("escape", "p"):
            self.on_escape()
        elif k == "f11":
            self.toggle_fs()
        elif k in ("return", "space", "kp_enter"):
            self.on_confirm()
        elif k == "r" and self.state in ("playing", "paused"):
            self.restart_level()

    def on_key_up(self, e):
        k = e.keysym.lower()
        if k in KEYDIR:
            # X11 auto-repeat sends release+press pairs; debounce the release.
            self.rel[k] = self.root.after(18, lambda k=k: self.drop(k))

    def drop(self, k):
        self.rel.pop(k, None)
        self.key_down_at.pop(k, None)
        if k in self.held:
            self.held.remove(k)

    def on_escape(self):
        s = self.state
        if s == "newgame_confirm":
            self.cancel_new_game()
        elif s in ("playing", "paused"):
            self.toggle_pause()
        elif s in ("select", "howto"):
            self.to_menu()
        elif s == "levelclear":
            self.clear_to_select()

    def on_confirm(self):
        self.sfx.play("ui")
        s = self.state
        if s == "menu":
            if self.has_save:
                self.load_game()
            else:
                self.request_new_game()
        elif s == "newgame_confirm":
            self.new_game()
        elif s == "select":
            self.try_select(self.sel)
        elif s == "paused":
            self.toggle_pause()
        elif s == "levelclear":
            self.clear_primary()
        elif s == "intro":
            self.intro_t = self.INTRO

    def on_click(self, e):
        for x1, y1, x2, y2, fn in reversed(self.buttons):
            if x1 <= e.x <= x2 and y1 <= e.y <= y2:
                self.sfx.play("ui")
                fn()
                return
        if self.state == "intro":
            self.intro_t = self.INTRO

    # --------------------------------------------------------------- update
    def tick(self):
        now = time.perf_counter()
        dt = min(0.05, now - self.last)
        self.last = now
        self.t += dt
        try:
            self.update(dt)
            self.draw()
        finally:
            self.root.after(10, self.tick)

    def update(self, dt):
        s = self.state
        if s == "intro":
            self.intro_t += dt
            if self.intro_t >= self.INTRO:
                self.state = "playing"
        elif s == "playing":
            self.update_game(dt)
        elif s == "levelclear":
            self.lc_t += dt
        for p in self.fxs:
            p[0] += p[2] * dt
            p[1] += p[3] * dt
            p[3] += 3.0 * dt
            p[4] -= dt
        self.fxs = [p for p in self.fxs if p[4] > 0]
        self.toast_t = max(0.0, self.toast_t - dt)
        self.flash = max(0.0, self.flash - dt * 1.4)

    def update_game(self, dt):
        self.elapsed += dt
        if self.moving:
            speed = self.MOVE_SPEED
            pressed_at = self.key_down_at.get(self.move_key)
            if self.move_key in self.held and pressed_at is not None and \
                    time.perf_counter() - pressed_at >= self.HOLD_ACCEL_DELAY:
                speed *= self.HOLD_ACCEL_MULTIPLIER
            self.move_progress = min(1.0, self.move_progress + dt * speed)
            start_x, start_y = self.cell
            end_x, end_y = self.target
            self.fx = start_x + (end_x - start_x) * self.move_progress
            self.fy = start_y + (end_y - start_y) * self.move_progress
            if self.move_progress >= 1.0:
                self.cell = self.target
                self.fx, self.fy = self.cell
                self.moving = False
                if self.exiting:
                    self.level_complete()
                    return
                if self.cell == self.maze.key and not self.has_key:
                    self.pickup()

        if not self.moving and self.held:
            self.try_begin(KEYDIR[self.held[-1]])

    def try_begin(self, d):
        """Start exactly one smooth cell-to-cell move when the passage is open."""
        x, y = self.cell
        m = self.maze
        if m.w[y][x] & d:
            if (x, y) == m.exit and d == m.door:
                if self.door_open:
                    self.begin(d, exiting=True)
                elif self.toast_t <= 0:
                    self.sfx.play("blocked")
                    self.show_toast("Locked! Find the key first.", C["bad"])
            else:
                self.sfx.play("blocked")
            return
        self.begin(d)

    def begin(self, d, exiting=False):
        self.sfx.play("step")
        x, y = self.cell
        self.target = (x + DX[d], y + DY[d])
        self.move_progress = 0.0
        self.moving = True
        self.exiting = exiting
        self.move_key = self.held[-1] if self.held else None

    # ------------------------------------------------------ drawing helpers
    def text(self, x, y, s, px, col, bold=False, anchor="center", mono=False):
        return self.cv.create_text(x, y, text=s, fill=col, font=self.font(px, bold, mono),
                                   anchor=anchor, tags="frame")

    def rrect(self, x1, y1, x2, y2, r, fill, outline="", width=1, tag="frame"):
        r = max(1, min(r, (x2 - x1) / 2, (y2 - y1) / 2))
        pts = [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2, x2 - r, y2,
               x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]
        return self.cv.create_polygon(pts, smooth=True, fill=fill, outline=outline,
                                      width=width, tags=tag)

    def scrim(self):
        self.cv.create_rectangle(0, 0, self.W, self.H, fill=C["bg"], outline="",
                                 stipple="gray50", tags="frame")
        self.buttons = []   # overlays are modal: lower layers stop receiving clicks

    def panel(self, cx, cy, w, h):
        u = self.ui
        x1, y1, x2, y2 = cx - w / 2, cy - h / 2, cx + w / 2, cy + h / 2
        self.rrect(x1, y1 + 12 * u, x2, y2 + 12 * u, 24 * u, mix(C["bg"], C["black"], 0.65))
        self.rrect(x1, y1, x2, y2, 24 * u, C["panel"], C["edge"], 2)
        self.cv.create_line(x1 + 40 * u, y1 + 3, x2 - 40 * u, y1 + 3, fill=C["accent"],
                            width=3, capstyle="round", tags="frame")
        return x1, y1, x2, y2

    def button(self, cx, cy, w, h, label, action, primary=False, px=21, enabled=True):
        u = self.ui
        x1, y1, x2, y2 = cx - w / 2, cy - h / 2, cx + w / 2, cy + h / 2
        mx, my = self.mouse
        hov = enabled and x1 <= mx <= x2 and y1 <= my <= y2
        if hov:
            self.hover = True
        self.rrect(x1, y1 + 5 * u, x2, y2 + 5 * u, h * 0.3, mix(C["bg"], C["black"], 0.6))
        if not enabled:
            fill, out, tc = C["panel"], C["edge"], C["dim"]
        elif primary:
            fill = mix(C["accent"], C["white"], 0.25) if hov else C["accent"]
            out, tc = "", "#04101c"
        else:
            fill = mix(C["panel2"], C["accent"], 0.18) if hov else C["panel2"]
            out, tc = (C["accent"] if hov else C["edge"]), C["text"]
        self.rrect(x1, y1, x2, y2, h * 0.3, fill, out, 2)
        self.text(cx, cy, label, px, tc, True)
        if enabled:
            self.buttons.append((x1, y1, x2, y2, action))

    def icon_button(self, cx, cy, size, icon, action, enabled=True):
        u = self.ui
        x1, y1, x2, y2 = cx - size / 2, cy - size / 2, cx + size / 2, cy + size / 2
        mx, my = self.mouse
        hov = enabled and x1 <= mx <= x2 and y1 <= my <= y2
        if hov:
            self.hover = True
        fill = mix(C["panel2"], C["accent"], 0.25) if hov else C["panel2"]
        self.rrect(x1, y1, x2, y2, size * 0.3, fill, C["accent"] if hov else C["edge"], 2)
        col = C["text"] if enabled else C["dim"]
        s = size * 0.5
        cv = self.cv
        if icon == "pause":
            for dx in (-0.2, 0.2):
                cv.create_rectangle(cx + dx * s * 1.3 - s * 0.15, cy - s * 0.5, cx + dx * s * 1.3 + s * 0.15,
                                    cy + s * 0.5, fill=col, outline="", tags="frame")
        elif icon == "play":
            cv.create_polygon(cx - s * 0.32, cy - s * 0.5, cx - s * 0.32, cy + s * 0.5, cx + s * 0.5, cy,
                              fill=col, outline="", tags="frame")
        elif icon == "full":
            a, b = s * 0.55, s * 0.25
            for sx in (-1, 1):
                for sy in (-1, 1):
                    cv.create_line(cx + sx * a, cy + sy * b, cx + sx * a, cy + sy * a, cx + sx * b, cy + sy * a,
                                   fill=col, width=max(2, 2.5 * u), capstyle="round", joinstyle="round",
                                   tags="frame")
        if enabled:
            self.buttons.append((x1, y1, x2, y2, action))

    def draw_key(self, cx, cy, s, col):
        cv = self.cv
        w = max(2, s * 0.09)
        cv.create_oval(cx - 0.40 * s, cy - 0.17 * s, cx - 0.06 * s, cy + 0.17 * s,
                       outline=col, width=w, tags="frame")
        cv.create_line(cx - 0.06 * s, cy, cx + 0.40 * s, cy, fill=col, width=w, capstyle="round", tags="frame")
        cv.create_line(cx + 0.24 * s, cy, cx + 0.24 * s, cy + 0.15 * s, fill=col, width=w,
                       capstyle="round", tags="frame")
        cv.create_line(cx + 0.38 * s, cy, cx + 0.38 * s, cy + 0.20 * s, fill=col, width=w,
                       capstyle="round", tags="frame")

    def draw_lock(self, cx, cy, s, col):
        """Padlock centred on (cx, cy), about s pixels wide."""
        self.rrect(cx - s / 2, cy - s * 0.12, cx + s / 2, cy + s * 0.55, s * 0.18, col)
        self.cv.create_arc(cx - s * 0.3, cy - s * 0.68, cx + s * 0.3, cy + s * 0.08, start=0, extent=180,
                           style="arc", outline=col, width=max(2, s * 0.14), tags="frame")

    def star(self, cx, cy, r, fill, outline=""):
        pts = []
        for i in range(10):
            a = -math.pi / 2 + i * math.pi / 5
            rr = r if i % 2 == 0 else r * 0.45
            pts += [cx + math.cos(a) * rr, cy + math.sin(a) * rr]
        self.cv.create_polygon(pts, fill=fill, outline=outline, width=2, tags="frame")

    # ----------------------------------------------------------------- draw
    def draw(self):
        cv = self.cv
        cv.delete("frame")
        self.buttons = []
        self.hover = False
        s = self.state
        if s in GAME_STATES and self.maze:
            if self.needs_layout or not self.has_static:
                self.build_static()
        elif self.has_static:
            cv.delete("static")
            self.has_static = False

        self.draw_bg()
        if s == "menu":
            self.draw_menu()
        elif s == "newgame_confirm":
            self.draw_menu()
            self.draw_newgame_confirm()
        elif s == "select":
            self.draw_select()
        elif s == "howto":
            self.draw_howto()
        elif s in GAME_STATES:
            self.draw_game()
            self.draw_hud()
            if s == "intro":
                self.draw_intro()
            elif s == "paused":
                self.draw_pause()
            elif s == "levelclear":
                self.draw_clear()
        self.draw_toast()
        cv.tag_lower("bg")
        cur = "hand2" if self.hover else ""
        if cur != self.cursor:
            cv.configure(cursor=cur)
            self.cursor = cur

    def draw_toast(self):
        if self.toast_t <= 0:
            return
        u = self.ui
        s, col = self.toast
        f = self.font(17, True)
        w = min(f.measure(s) + 44 * u, self.W - 20)
        ty = self.H - 34 * u * 0.55
        self.rrect(self.W / 2 - w / 2, ty - 17 * u, self.W / 2 + w / 2, ty + 17 * u, 17 * u,
                   C["panel"], col, 2)
        self.cv.create_text(self.W / 2, ty, text=s, fill=col, font=f, tags="frame")

    def draw_bg(self):
        cv, W, H, t = self.cv, self.W, self.H, self.t
        k = 0.55 if self.state in GAME_STATES else 1.0
        cv.create_rectangle(0, 0, W, H, fill=C["bg"], outline="", tags=("frame", "bg"))
        r = min(W, H) * 0.6
        for col, fx, fy, ph in BLOBS:
            cx = W * (fx + 0.05 * math.sin(t * 0.3 + ph))
            cy = H * (fy + 0.05 * math.cos(t * 0.25 + ph))
            cv.create_oval(cx - r, cy - r, cx + r, cy + r, fill=mix(C["bg"], col, 0.07 * k),
                           outline="", tags=("frame", "bg"))
            r2 = r * 0.55
            cv.create_oval(cx - r2, cy - r2, cx + r2, cy + r2, fill=mix(C["bg"], col, 0.12 * k),
                           outline="", tags=("frame", "bg"))
        for p in self.parts:
            p[0] = (p[0] + p[2] * 0.016) % 1.0
            p[1] = (p[1] + p[3] * 0.016) % 1.0
            x, y = p[0] * W, p[1] * H
            rad = p[4] * self.ui * (0.8 + 0.2 * math.sin(t * 2 + p[5]))
            cv.create_oval(x - rad, y - rad, x + rad, y + rad,
                           fill=mix(C["bg"], C["accent"], 0.14 + 0.07 * p[4] * k),
                           outline="", tags=("frame", "bg"))

    # -------------------------------------------------------------- menu UI
    def draw_menu(self):
        W, H, u = self.W, self.H, self.ui
        cx = W / 2
        ky = H * 0.14 + math.sin(self.t * 2) * 4 * u
        for rad, kk in ((64, 0.07), (46, 0.13)):
            self.cv.create_oval(cx - rad * u, ky - rad * u, cx + rad * u, ky + rad * u,
                                fill=mix(C["bg"], C["gold"], kk), outline="", tags="frame")
        self.draw_key(cx, ky, 84 * u, C["gold"])

        f = self.font(96, True)
        wk, wm = f.measure("KEY"), f.measure("MAZE")
        x0 = cx - (wk + wm) / 2
        ty = H * 0.30
        sh = mix(C["bg"], C["accent2"], 0.55)
        for off, c1, c2 in ((5 * u, sh, sh), (0, C["text"], C["accent"])):
            self.cv.create_text(x0 + off, ty + off, text="KEY", fill=c1, font=f, anchor="w", tags="frame")
            self.cv.create_text(x0 + wk + off, ty + off, text="MAZE", fill=c2, font=f, anchor="w", tags="frame")
        self.text(cx, H * 0.425, "Find the key.  Unlock the door.  Beat the clock.", 21, C["dim"])

        bw, bh, gap = 360 * u, 54 * u, 59 * u
        y0 = H * 0.49
        self.button(cx, y0, bw, bh, "NEW GAME", self.request_new_game, primary=True, px=22)
        self.button(cx, y0 + gap, bw, bh, "LOAD GAME", self.load_game,
                    enabled=self.has_save, px=21)
        self.button(cx, y0 + 2 * gap, bw, bh, "HOW TO PLAY", lambda: setattr(self, "state", "howto"))
        self.button(cx, y0 + 3 * gap, bw, bh, "FULLSCREEN: " + ("ON" if self.fullscreen else "OFF"), self.toggle_fs)
        self.button(cx, y0 + 4 * gap, bw, bh, "QUIT", self.root.destroy)
        self.text(cx, H - 24 * u, "Arrows / WASD move   |   M sound   |   Esc pause   |   F11 fullscreen", 14, C["dim"])

    def draw_newgame_confirm(self):
        self.scrim()
        self.buttons = []
        W, H, u = self.W, self.H, self.ui
        pw, ph = min(W - 40, 520 * u), min(H - 40, 250 * u)
        x1, y1, x2, y2 = self.panel(W / 2, H / 2, pw, ph)
        self.text(W / 2, y1 + ph * 0.25, "START A NEW GAME?", 30, C["text"], True)
        self.text(W / 2, y1 + ph * 0.46, "This resets saved keys and best scores.", 16, C["dim"])
        by = y1 + ph * 0.76
        bw, bh = pw * 0.38, 52 * u
        self.button(W / 2 - pw * 0.22, by, bw, bh, "CANCEL", self.cancel_new_game, px=18)
        self.button(W / 2 + pw * 0.22, by, bw, bh, "START FRESH", self.new_game,
                    primary=True, px=18)

    def draw_howto(self):
        W, H, u = self.W, self.H, self.ui
        pw, ph = min(W - 40, 820 * u), min(H - 40, 540 * u)
        x1, y1, x2, y2 = self.panel(W / 2, H / 2, pw, ph)
        self.text(W / 2, y1 + ph * 0.10, "HOW TO PLAY", 38, C["text"], True)
        lines = [
            "Tap arrows or WASD for one tile; hold briefly for 2x movement speed.",
            "Find the glowing golden key hidden somewhere in the maze.",
            "Grabbing it unlocks the red door on the maze's outer wall - walk out to win.",
            "Faster is better: the less time you take, the higher your score.",
            "Clearing a level for the first time earns that level's LEVEL KEY.",
            "Level N needs N-1 level keys to unlock. Every attempt is a brand-new maze.",
        ]
        top = y1 + ph * 0.23
        step = ph * 0.105
        for i, s in enumerate(lines):
            y = top + i * step
            r = 15 * u
            self.cv.create_oval(x1 + 52 * u - r, y - r, x1 + 52 * u + r, y + r, fill=C["accent"],
                                outline="", tags="frame")
            self.text(x1 + 52 * u, y, str(i + 1), 16, "#04101c", True)
            self.text(x1 + 88 * u, y, s, 17, C["text"], False, "w")
        self.text(W / 2, y1 + ph * 0.83, "M sound   |   Esc / P pause   |   R restart   |   F11 fullscreen", 15, C["dim"])
        self.button(W / 2, y1 + ph * 0.92, 250 * u, 54 * u, "BACK", self.to_menu, primary=True)

    # ---------------------------------------------------------- level select
    def draw_select(self):
        W, H, u = self.W, self.H, self.ui
        cx = W / 2
        self.button(24 * u + 58 * u, 44 * u, 116 * u, 44 * u, "BACK", self.to_menu, px=16)
        self.text(cx, 44 * u, "SELECT LEVEL", 36, C["text"], True)
        if self.cheat:
            bw = 170 * u
            self.rrect(W - 24 * u - bw, 44 * u - 17 * u, W - 24 * u, 44 * u + 17 * u, 17 * u,
                       C["panel"], C["dev"], 2)
            self.text(W - 24 * u - bw / 2, 44 * u, "DEV: ALL KEYS", 14, C["dev"], True)

        # --- level key wallet
        have = self.keyset()
        pw_, ph_, py = 570 * u, 46 * u, 104 * u
        self.rrect(cx - pw_ / 2, py - ph_ / 2, cx + pw_ / 2, py + ph_ / 2, ph_ / 2, C["panel"], C["edge"], 2)
        self.text(cx - pw_ / 2 + 26 * u, py, "LEVEL KEYS", 13, C["dim"], True, "w")
        sx0 = cx - pw_ / 2 + 150 * u
        for i in range(1, NUM_LEVELS + 1):
            if i in self.earned:
                col = C["gold"]
            elif i in have:
                col = C["dev"]
            else:
                col = mix(C["panel"], C["dim"], 0.35)
            self.draw_key(sx0 + (i - 1) * 31 * u + 12 * u, py, 26 * u, col)
        self.text(cx + pw_ / 2 - 24 * u, py, "%d / %d" % (len(have), NUM_LEVELS), 18, C["gold"], True, "e")

        # --- 5 x 2 grid of level tiles
        gm, gap = 36 * u, 16 * u
        top, bottom = 140 * u, H - 40 * u
        tw = min((W - 2 * gm - 4 * gap) / 5.0, 230 * u)
        th = min((bottom - top - gap) / 2.0, 270 * u, tw * 1.25)
        gw, gh = 5 * tw + 4 * gap, 2 * th + gap
        x0 = (W - gw) / 2
        y0 = top + ((bottom - top) - gh) / 2
        k = min(tw, th) / (220.0 * u)          # content scale for this tile size
        mx, my = self.mouse
        for i in range(NUM_LEVELS):
            lvl = i + 1
            col_, row_ = i % 5, i // 5
            x1 = x0 + col_ * (tw + gap)
            y1 = y0 + row_ * (th + gap)
            x2, y2 = x1 + tw, y1 + th
            if x1 <= mx <= x2 and y1 <= my <= y2:
                self.hover = True
                if self.mouse_moved:
                    self.sel = i
            unlocked = self.is_unlocked(lvl)
            hl = (i == self.sel)
            lift = 6 * u if (hl and unlocked) else 0
            y1 -= lift
            y2 -= lift
            done = lvl in self.earned
            best = self.best.get(str(lvl))
            mid = (x1 + x2) / 2
            h = y2 - y1

            self.rrect(x1, y1 + 8 * u, x2, y2 + 8 * u, 18 * u, mix(C["bg"], C["black"], 0.6))
            if unlocked:
                fill = mix(C["panel2"], C["accent"], 0.14) if hl else C["panel2"]
                out = C["accent"] if hl else C["edge"]
            else:
                fill = mix(C["panel"], C["bg"], 0.45)
                out = C["bad"] if hl else mix(C["edge"], C["bg"], 0.5)
            self.rrect(x1, y1, x2, y2, 18 * u, fill, out, 3 if hl else 2)
            if unlocked:     # accent strip, colour ramps with difficulty
                self.cv.create_line(x1 + 22 * u, y1 + 3, x2 - 22 * u, y1 + 3, capstyle="round", width=4,
                                    fill=mix(C["accent2"], C["accent"], i / 9.0), tags="frame")

            self.text(mid, y1 + h * 0.15, "LEVEL", 13 * k, C["dim"], True)
            self.text(mid, y1 + h * 0.38, str(lvl), 60 * k, C["text"] if unlocked else C["dim"], True)
            if done:
                self.draw_key(x2 - 30 * k * u, y1 + 30 * k * u, 28 * k * u, C["gold"])
            if unlocked:
                cols, rows = level_dims(lvl)
                self.text(mid, y1 + h * 0.60, "%d x %d maze" % (cols, rows), 14 * k, C["dim"])
                if best:
                    for j in range(3):
                        self.star(mid + (j - 1) * 30 * k * u, y1 + h * 0.77, 11 * k * u,
                                  C["gold"] if j < best["stars"] else C["edge"])
                    self.text(mid, y1 + h * 0.91, "BEST %s" % format(best["score"], ","), 12 * k, C["dim"], True)
                else:
                    self.text(mid, y1 + h * 0.80, "READY", 16 * k, C["accent"], True)
            else:
                need = keys_needed(lvl)
                self.draw_lock(mid, y1 + h * 0.60, 34 * k * u, C["dim"])
                self.text(mid, y1 + h * 0.86, "NEEDS %d KEY%s" % (need, "" if need == 1 else "S"),
                          14 * k, C["gold"], True)
            self.buttons.append((x1, y1 + lift, x2, y2 + lift, lambda i=i: self.try_select(i)))
        self.mouse_moved = False
        if self.toast_t <= 0:
            self.text(cx, H - 18 * u, "Clear a level to earn its key.  Level N needs N-1 keys.  "
                      "Arrows + Enter also work.", 13, C["dim"])

    # ------------------------------------------------------------ game view
    def build_static(self):
        cv = self.cv
        cv.delete("static")
        m, u = self.maze, self.ui
        W, H = self.W, self.H
        hud_h = 92 * u
        self.pad = 34 * u
        aw = W - 2 * self.pad
        ah = H - hud_h - 2 * self.pad
        c = max(8, int(min(aw / m.cols, ah / m.rows)))
        self.cs = c
        self.ox = (W - c * m.cols) / 2
        self.oy = hud_h + self.pad + (ah - c * m.rows) / 2
        ox, oy = self.ox, self.oy

        self.rrect(ox - 10, oy - 10, ox + c * m.cols + 10, oy + c * m.rows + 10, 16,
                   C["floor"], mix(C["edge"], C["bg"], 0.35), 2, tag="static")
        sx, sy = m.start
        cv.create_rectangle(ox + sx * c + 3, oy + sy * c + 3, ox + (sx + 1) * c - 3, oy + (sy + 1) * c - 3,
                            fill=mix(C["floor"], C["accent"], 0.10), outline="", tags="static")

        hw = [[False] * m.cols for _ in range(m.rows + 1)]
        vw = [[False] * m.rows for _ in range(m.cols + 1)]
        for y in range(m.rows):
            for x in range(m.cols):
                w = m.w[y][x]
                if w & UP:
                    hw[y][x] = True
                if w & DN:
                    hw[y + 1][x] = True
                if w & LT:
                    vw[x][y] = True
                if w & RT:
                    vw[x + 1][y] = True
        ex, ey = m.exit
        if m.door == UP:
            hw[ey][ex] = False
        elif m.door == DN:
            hw[ey + 1][ex] = False
        elif m.door == LT:
            vw[ex][ey] = False
        else:
            vw[ex + 1][ey] = False

        segs = []
        for y in range(m.rows + 1):
            x = 0
            while x < m.cols:
                if hw[y][x]:
                    s = x
                    while x < m.cols and hw[y][x]:
                        x += 1
                    segs.append((ox + s * c, oy + y * c, ox + x * c, oy + y * c))
                else:
                    x += 1
        for x in range(m.cols + 1):
            y = 0
            while y < m.rows:
                if vw[x][y]:
                    s = y
                    while y < m.rows and vw[x][y]:
                        y += 1
                    segs.append((ox + x * c, oy + s * c, ox + x * c, oy + y * c))
                else:
                    y += 1
        lw = max(2.0, c * 0.12)
        glow = mix(C["floor"], C["wall"], 0.30)
        for sg in segs:
            cv.create_line(*sg, fill=glow, width=lw * 2.6, capstyle="round", tags="static")
        for sg in segs:
            cv.create_line(*sg, fill=C["wall"], width=lw, capstyle="round", tags="static")
        self.has_static = True
        self.needs_layout = False

    def draw_game(self):
        cv, m, c, t = self.cv, self.maze, self.cs, self.t
        ox, oy = self.ox, self.oy

        def cp(fx, fy):
            return ox + (fx + 0.5) * c, oy + (fy + 0.5) * c

        self.draw_door()
        if not self.has_key:
            kx, ky = cp(*m.key)
            ky += math.sin(t * 3) * c * 0.06
            r = c * (0.40 + 0.05 * math.sin(t * 4))
            cv.create_oval(kx - r, ky - r, kx + r, ky + r, fill=mix(C["floor"], C["gold"], 0.12),
                           outline=mix(C["floor"], C["gold"], 0.45), width=2, tags="frame")
            self.draw_key(kx, ky, c * 0.78, C["gold"])

        # --- player: the player.png sprite (soft shadow underneath)
        px, py = cp(self.fx, self.fy)
        shw = c * 0.28
        cv.create_oval(px - shw, py + c * 0.28 - shw * 0.32, px + shw, py + c * 0.28 + shw * 0.32,
                       fill=mix(C["floor"], C["black"], 0.55), outline="", tags="frame")
        if self.has_player_art:
            cv.create_image(px, py, image=self.player_image(c * 0.92), tags="frame")
        else:                                   # only when player.png is missing
            r = c * 0.28
            cv.create_oval(px - r, py - r, px + r, py + r, fill=C["dim"], outline=C["white"], width=2,
                           tags="frame")

        for p in self.fxs:
            x, y = cp(p[0], p[1])
            rad = max(1.5, c * 0.08 * min(1.0, p[4] * 1.6))
            cv.create_oval(x - rad, y - rad, x + rad, y + rad, fill=p[5], outline="", tags="frame")

    def draw_door(self):
        cv, m, c, t = self.cv, self.maze, self.cs, self.t
        ex, ey = m.exit
        d = m.door
        px, py = self.ox + ex * c, self.oy + ey * c
        if d == UP:
            a, b = (px, py), (px + c, py)
        elif d == DN:
            a, b = (px, py + c), (px + c, py + c)
        elif d == LT:
            a, b = (px, py), (px, py + c)
        else:
            a, b = (px + c, py), (px + c, py + c)
        mx, my = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
        nx, ny = DX[d], DY[d]
        lw = max(3.0, c * 0.14)
        if not self.door_open:
            cv.create_line(*a, *b, fill=mix(C["floor"], C["bad"], 0.40), width=lw * 2.6,
                           capstyle="round", tags="frame")
            cv.create_line(*a, *b, fill=C["bad"], width=lw * 1.5, capstyle="round", tags="frame")
            self.draw_lock(mx, my, c * 0.36, C["gold"])
        else:
            pulse = 0.5 + 0.5 * math.sin(t * 5)
            for e in (a, b):
                ox_, oy_ = mx - e[0], my - e[1]
                cv.create_line(e[0], e[1], e[0] + ox_ * 0.4, e[1] + oy_ * 0.4, fill=C["good"],
                               width=lw * 1.5, capstyle="round", tags="frame")
            rg = c * (0.34 + 0.07 * pulse)
            cv.create_oval(mx - rg, my - rg, mx + rg, my + rg, fill=mix(C["floor"], C["good"], 0.16),
                           outline="", tags="frame")
            al = min(0.42 * c, 0.7 * self.pad)
            bob = pulse * c * 0.08
            bx, by = mx + nx * (al * 0.35 + bob), my + ny * (al * 0.35 + bob)
            tx, ty = -ny, nx
            cv.create_polygon(bx + nx * al, by + ny * al, bx + tx * al * 0.6, by + ty * al * 0.6,
                              bx - tx * al * 0.6, by - ty * al * 0.6, fill=C["good"], outline="",
                              tags="frame")
        if self.flash > 0:
            r = c * (0.4 + (1 - self.flash) * 1.6)
            cv.create_oval(mx - r, my - r, mx + r, my + r, outline=mix(C["floor"], C["good"], self.flash),
                           width=3, tags="frame")

    # ------------------------------------------------------------------ HUD
    def draw_hud(self):
        W, u = self.W, self.ui
        pad, h, y1 = 24 * u, 64 * u, 14 * u
        x1, x2 = pad, W - pad
        cy = y1 + h / 2
        self.rrect(x1, y1, x2, y1 + h, 18 * u, C["panel"], C["edge"], 2)
        self.text(x1 + 22 * u, y1 + h * 0.31, "LEVEL %d / %d" % (self.idx + 1, NUM_LEVELS), 13, C["dim"], True, "w")
        best = self.best.get(str(self.idx + 1))
        self.text(x1 + 22 * u, y1 + h * 0.68, ("BEST %s" % format(best["score"], ",")) if best else "NO BEST YET",
                  19, C["text"] if best else C["dim"], True, "w")
        self.text(W / 2, y1 + h * 0.40, fmt_time(self.elapsed), 30, C["text"], True, "center", True)
        self.text(W / 2, y1 + h * 0.80, "+%s this level" % format(self.score_for(self.elapsed), ","),
                  13, C["accent"], True)

        b = 42 * u
        r = x2 - 16 * u
        self.icon_button(r - b / 2, cy, b, "full", self.toggle_fs)
        self.icon_button(r - b * 1.5 - 10 * u, cy, b, "play" if self.state == "paused" else "pause",
                         self.toggle_pause, enabled=self.state in ("playing", "paused"))
        kx = r - b * 2.5 - 20 * u - 32 * u
        self.rrect(kx - 32 * u, cy - b / 2, kx + 32 * u, cy + b / 2, b * 0.3, C["panel2"],
                   C["gold"] if self.has_key else C["edge"], 2)
        self.draw_key(kx, cy, 34 * u, C["gold"] if self.has_key else C["dim"])
        self.text(kx - 44 * u, cy, "MAZE KEY OK" if self.has_key else "MAZE KEY", 12,
                  C["gold"] if self.has_key else C["dim"], True, "e")

    # -------------------------------------------------------------- overlays
    def draw_intro(self):
        W, H, u = self.W, self.H, self.ui
        it = self.intro_t
        off = 0.0
        if it < 0.3:
            off = -(1 - ease(it / 0.3)) * W
        elif it > self.INTRO - 0.3:
            off = ease((it - (self.INTRO - 0.3)) / 0.3) * W
        cy = H * 0.5
        hh = 80 * u
        self.rrect(off - 20, cy - hh, off + W + 20, cy + hh, 4, mix(C["bg"], C["panel"], 0.9), C["accent"], 3)
        self.text(W / 2 + off, cy - 18 * u, "LEVEL %d" % (self.idx + 1), 64, C["text"], True)
        m = self.maze
        self.text(W / 2 + off, cy + 40 * u, "%dx%d maze  -  find the key, unlock the door, get out!"
                  % (m.cols, m.rows), 18, C["accent"], True)

    def draw_pause(self):
        self.scrim()
        W, H, u = self.W, self.H, self.ui
        pw, ph = min(W - 40, 470 * u), min(H - 40, 450 * u)
        x1, y1, x2, y2 = self.panel(W / 2, H / 2, pw, ph)
        self.text(W / 2, y1 + ph * 0.14, "PAUSED", 46, C["text"], True)
        self.text(W / 2, y1 + ph * 0.255, "Timer stopped at " + fmt_time(self.elapsed), 16, C["dim"])
        bw, bh = pw * 0.78, 54 * u
        by = y1 + ph * 0.43
        gap = ph * 0.165
        self.button(W / 2, by, bw, bh, "RESUME", self.toggle_pause, primary=True, px=22)
        self.button(W / 2, by + gap, bw, bh, "RESTART LEVEL", self.restart_level)
        self.button(W / 2, by + 2 * gap, bw, bh, "LEVEL SELECT", self.to_select)
        self.text(W / 2, y2 - 20 * u, "Esc / P to resume", 13, C["dim"])

    def draw_clear(self):
        self.scrim()
        W, H, u = self.W, self.H, self.ui
        pw, ph = min(W - 40, 560 * u), min(H - 40, 610 * u)
        x1, y1, x2, y2 = self.panel(W / 2, H / 2, pw, ph)
        cx = W / 2
        self.text(cx, y1 + ph * 0.08, "LEVEL CLEARED!", 40, C["good"], True)
        self.text(cx, y1 + ph * 0.145, "Level %d of %d" % (self.idx + 1, NUM_LEVELS), 16, C["dim"])
        for i in range(3):
            sx = cx + (i - 1) * 96 * u
            sy = y1 + ph * 0.25
            appear = 0.35 + 0.3 * i
            if i < self.last_stars and self.lc_t > appear:
                k = ease((self.lc_t - appear) / 0.25)
                self.star(sx, sy, 38 * u * (0.55 + 0.45 * k), C["gold"], mix(C["gold"], C["white"], 0.5))
            else:
                self.star(sx, sy, 32 * u, C["panel2"], C["edge"])
        shown = int(self.last_gain * ease(self.lc_t / 1.1))
        lx, rx = cx - pw * 0.2, cx + pw * 0.2
        self.text(lx, y1 + ph * 0.385, "TIME", 14, C["dim"], True)
        self.text(lx, y1 + ph * 0.45, fmt_time(self.last_time), 34, C["text"], True, "center", True)
        self.text(rx, y1 + ph * 0.385, "SCORE", 14, C["dim"], True)
        self.text(rx, y1 + ph * 0.45, "+" + format(shown, ","), 34, C["accent"], True)
        if self.last_newbest and self.lc_t > 1.1:
            self.text(rx, y1 + ph * 0.52, "NEW BEST!", 14, C["gold"], True)

        ky = y1 + ph * 0.64
        if self.got_key:
            if self.lc_t > 1.0:
                k = ease((self.lc_t - 1.0) / 0.4)
                rad = 34 * u * k
                self.cv.create_oval(cx - 96 * u - rad, ky - rad, cx - 96 * u + rad, ky + rad,
                                    fill=mix(C["panel"], C["gold"], 0.18), outline="", tags="frame")
                self.draw_key(cx - 96 * u, ky, 60 * u * (0.4 + 0.6 * k), C["gold"])
                self.text(cx - 52 * u, ky, "+1 LEVEL KEY", 26, C["gold"], True, "w")
        else:
            self.text(cx, ky, "Level key already collected", 16, C["dim"])
        if self.lc_t > 1.3:
            if self.unlock_msg:
                self.text(cx, y1 + ph * 0.74, self.unlock_msg, 20, C["good"], True)
            self.text(cx, y1 + ph * 0.80, "LEVEL KEYS  %d / %d" % (len(self.keyset()), NUM_LEVELS),
                      14, C["dim"], True)
        by = y1 + ph * 0.91
        bw, bh = pw * 0.42, 56 * u
        self.button(cx - pw * 0.23, by, bw, bh, "LEVEL SELECT", self.clear_to_select, px=18)
        self.button(cx + pw * 0.23, by, bw, bh, "NEXT LEVEL" if self.has_next() else "PLAY AGAIN",
                    self.clear_primary, primary=True, px=18)


if __name__ == "__main__":
    App().run()
