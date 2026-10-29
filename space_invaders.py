import array
from contextlib import contextmanager
from datetime import datetime, timezone
from functools import wraps
import hashlib
import json
import os
from pathlib import Path
import math
import random
import sys

# Let SDL request a native-resolution window on Windows HiDPI monitors instead
# of allowing desktop bitmap scaling to blur the entire game.
os.environ.setdefault("SDL_WINDOWS_DPI_AWARENESS", "permonitorv2")
import pygame 

# Screen Setup Constants
SCREEN_WIDTH = 1600
SCREEN_HEIGHT = 900
WORLD_SIZE = (1600, 900)
GUI_SCALE_STEPS = (0.75, 0.875, 1.0, 1.125, 1.25, 1.375, 1.5)
DISPLAY_SETTINGS_FILE = Path.home() / ".neon_frontier" / "display_settings.json"
_UI_LAYOUT_SIZE = None
_UI_POINTER_POS = None
_UI_DIMENSION_DEPTH = 0


def current_ui_size():
    if _UI_DIMENSION_DEPTH:
        return (SCREEN_WIDTH, SCREEN_HEIGHT)
    return _UI_LAYOUT_SIZE or (SCREEN_WIDTH, SCREEN_HEIGHT)


@contextmanager
def ui_dimensions(size=None):
    """Temporarily provide GUI geometry without changing the simulated arena."""
    global SCREEN_WIDTH, SCREEN_HEIGHT, _UI_DIMENSION_DEPTH
    previous = (SCREEN_WIDTH, SCREEN_HEIGHT)
    SCREEN_WIDTH, SCREEN_HEIGHT = size or current_ui_size()
    _UI_DIMENSION_DEPTH += 1
    try:
        yield (SCREEN_WIDTH, SCREEN_HEIGHT)
    finally:
        _UI_DIMENSION_DEPTH -= 1
        SCREEN_WIDTH, SCREEN_HEIGHT = previous


def ui_layout(function):
    @wraps(function)
    def wrapped(*args, **kwargs):
        with ui_dimensions():
            return function(*args, **kwargs)
    return wrapped


def ui_scene(function):
    @wraps(function)
    def wrapped(screen, *args, **kwargs):
        with ui_dimensions(screen.get_size()):
            return function(screen, *args, **kwargs)
    return wrapped


def get_ui_mouse_pos():
    return pygame.mouse.get_pos() if _UI_POINTER_POS is None else _UI_POINTER_POS


def display_preferences_path():
    save_file = globals().get("SAVE_FILE")
    return (save_file.parent / "display_settings.json") if save_file is not None else DISPLAY_SETTINGS_FILE


def load_display_preferences(filename=None):
    defaults = {"gui_scale": 1.0, "fullscreen": False, "window_size": [1280, 720]}
    filename = display_preferences_path() if filename is None else Path(filename)
    try:
        if not filename.exists() or filename.stat().st_size > 4096:
            return defaults
        data = json.loads(filename.read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            return defaults
        scale = data.get("gui_scale", 1.0)
        fullscreen = data.get("fullscreen", False)
        size = data.get("window_size", [1280, 720])
        if (type(scale) not in (int, float) or scale not in GUI_SCALE_STEPS
                or type(fullscreen) is not bool or not isinstance(size, list)
                or len(size) != 2 or any(type(value) is not int for value in size)
                or not 320 <= size[0] <= 7680 or not 240 <= size[1] <= 4320):
            return defaults
        return {"gui_scale": float(scale), "fullscreen": fullscreen, "window_size": size}
    except (OSError, ValueError, TypeError, RecursionError):
        return defaults


def save_display_preferences(preferences, filename=None):
    """Display preferences live separately from run saves and replace atomically."""
    from tempfile import NamedTemporaryFile
    filename = display_preferences_path() if filename is None else Path(filename)
    temporary = None
    try:
        filename.parent.mkdir(parents=True, exist_ok=True)
        with NamedTemporaryFile(mode="w", encoding="utf-8", dir=filename.parent,
                                prefix=".display-", suffix=".tmp", delete=False) as handle:
            temporary = Path(handle.name)
            json.dump(preferences, handle)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, filename)
        return True
    except (OSError, ValueError, TypeError):
        if temporary is not None:
            try:
                temporary.unlink(missing_ok=True)
            except OSError:
                pass
        return False


class DisplayManager:
    """A stable arena presented in a resizable window, with independently sized GUI."""

    def __init__(self, preferences=None, settings_file=None):
        self.settings_file = display_preferences_path() if settings_file is None else Path(settings_file)
        self.preferences = dict(preferences or load_display_preferences(self.settings_file))
        self.preferences["window_size"] = list(self.preferences["window_size"])
        self.display = None
        self.world_surface = pygame.Surface(WORLD_SIZE)
        self.ui_surface = None
        self._ui_key = None
        self._presentation = None
        self._presentation_size = None
        self._layer_targets = {}
        self._display_size = None
        self.mode_epoch = 0
        self.settings_error = None
        self._preferences_changed_at = None

    def open(self):
        flags = pygame.FULLSCREEN if self.preferences["fullscreen"] else pygame.RESIZABLE
        size = (0, 0) if self.preferences["fullscreen"] else tuple(self.preferences["window_size"])
        self.display = pygame.display.set_mode(size, flags)
        self._display_size = self.display.get_size()
        self.mode_epoch += 1
        self._invalidate()
        return self.display

    def _sync_display_surface(self):
        """Use SDL's current drawable after a mode, monitor or DPI change."""
        current = pygame.display.get_surface()
        if current is None:
            return False
        self.display = current
        size = current.get_size()
        if size == self._display_size:
            return False
        self._display_size = size
        self._invalidate()
        return True

    def _invalidate(self):
        self._ui_key = None
        self._presentation = None
        self._presentation_size = None
        self._layer_targets.clear()

    @property
    def viewport(self):
        # Map both simulation axes to the window. Aspect-fit margins used to
        # reserve unreachable strips above/below the arena on 16:10 and 4:3
        # displays. All four world edges now reach the corresponding screen edge.
        return self.display.get_rect()

    @property
    def effective_gui_zoom(self):
        return self.preferences["gui_scale"]

    def ui_size(self, arena=False):
        self._sync_display_surface()
        width, height = self.display.get_size()
        # Auto uses one GUI pixel per display pixel. Manual zoom receives one
        # antialiased presentation pass, rather than a trip through world pixels.
        factor = min(self.effective_gui_zoom, width / 640, height / 360)
        return (max(640, round(width / factor)), max(360, round(height / factor)))

    def activate(self, arena=False):
        global _UI_LAYOUT_SIZE, _UI_POINTER_POS
        size = self.ui_size(arena)
        if self._ui_key != size:
            self.ui_surface = pygame.Surface(size, pygame.SRCALPHA)
            self._ui_key = size
        _UI_LAYOUT_SIZE = size
        _UI_POINTER_POS = self.map_pointer(pygame.mouse.get_pos(), arena)
        return self.ui_surface

    def map_pointer(self, position, arena=False):
        width, height = self.ui_size(arena)
        region = self.viewport if arena else self.display.get_rect()
        if arena and not region.collidepoint(position):
            return (-10000, -10000)
        return (int((position[0] - region.x) * width / region.width),
                int((position[1] - region.y) * height / region.height))

    def map_event(self, event, arena=False):
        if not hasattr(event, "pos"):
            return event
        values = dict(event.dict)
        values["pos"] = self.map_pointer(event.pos, arena)
        return pygame.event.Event(event.type, values)

    def _save(self):
        self.settings_error = None if save_display_preferences(self.preferences, self.settings_file) else "Display changes apply now; preferences could not be saved."
        self._preferences_changed_at = None

    def flush_preferences(self, force=False):
        if (self._preferences_changed_at is not None
                and (force or pygame.time.get_ticks() - self._preferences_changed_at >= 300)):
            self._save()

    def resize(self, size, *, from_event=False):
        # SDL can deliver notifications from the previous fullscreen/windowed
        # mode after a toggle. They describe history, not the current drawable.
        # SDL2 already resizes display surfaces for genuine window changes.
        changed = self._sync_display_surface() if from_event else False
        if self.preferences["fullscreen"]:
            return changed
        if from_event:
            size = self.display.get_size()
        size = (max(320, min(7680, int(size[0]))), max(240, min(4320, int(size[1]))))
        if (from_event and size == tuple(self.preferences["window_size"])
                and not changed):
            return False
        self.preferences["window_size"] = list(size)
        if self.display.get_size() != size:
            self.display = pygame.display.set_mode(size, pygame.RESIZABLE)
        self._display_size = self.display.get_size()
        self._invalidate()
        self._preferences_changed_at = pygame.time.get_ticks()
        return True

    def toggle_fullscreen(self):
        if not self.preferences["fullscreen"]:
            self.preferences["window_size"] = list(self.display.get_size())
        self.preferences["fullscreen"] = not self.preferences["fullscreen"]
        self.open()
        self._save()

    def adjust_gui_scale(self, direction):
        index = min(range(len(GUI_SCALE_STEPS)),
                    key=lambda i: abs(GUI_SCALE_STEPS[i] - self.preferences["gui_scale"]))
        new_scale = GUI_SCALE_STEPS[max(0, min(len(GUI_SCALE_STEPS) - 1, index + direction))]
        if new_scale == self.preferences["gui_scale"]:
            return False
        self.preferences["gui_scale"] = new_scale
        self._invalidate()
        self._save()
        return True

    def reset_gui_scale(self):
        self.preferences["gui_scale"] = 1.0
        self._invalidate()
        self._save()

    def _present_layer(self, surface, region, name):
        if surface is None:
            return
        if surface.get_size() == region.size:
            self.display.blit(surface, region)
            return
        target = self._layer_targets.get(name)
        if target is None or target.get_size() != region.size:
            target = pygame.Surface(region.size, pygame.SRCALPHA)
            self._layer_targets[name] = target
        pygame.transform.smoothscale(surface, region.size, target)
        self.display.blit(target, region)

    def present(self, surface, arena=False, ui_underlay=None, ui_overlay=None,
                threat_surface=None):
        region = self.viewport if arena else self.display.get_rect()
        self.display.fill((3, 7, 20))
        if surface.get_size() == region.size:
            self.display.blit(surface, region)
        else:
            if self._presentation_size != region.size:
                self._presentation = pygame.Surface(region.size)
                self._presentation_size = region.size
            pygame.transform.smoothscale(surface, region.size, self._presentation)
            self.display.blit(self._presentation, region)
        self._present_layer(ui_underlay, region, "underlay")
        self._present_layer(threat_surface, region, "threats")
        self._present_layer(ui_overlay, region, "overlay")
        pygame.display.flip()


@ui_layout
def gameplay_display_button_rect(pause_button, exit_button=None, paused=False):
    """Keep display controls in the clear central channel of compact HUDs."""
    button = pygame.Rect(0, 0, 48 if SCREEN_WIDTH < 700 else 104, 28)
    button.midbottom = (pause_button.centerx, pause_button.top - 8)
    return button


@ui_layout
def display_settings_layout():
    panel = pygame.Rect(0, 0, min(580, SCREEN_WIDTH - 36), min(360, SCREEN_HEIGHT - 24))
    panel.center = (SCREEN_WIDTH // 2, SCREEN_HEIGHT // 2)
    gap = 12
    button_width = (panel.width - 64) // 3
    y = panel.y + round(panel.height * .37)
    controls = [pygame.Rect(panel.x + 20 + i * (button_width + gap), y, button_width, 42)
                for i in range(3)]
    mode = pygame.Rect(panel.x + 20, y + 56, panel.width - 40, 42)
    close = pygame.Rect(0, 0, (panel.width - 52) // 2, 42)
    close.bottomright = (panel.right - 20, panel.bottom - 18)
    keyboard = close.copy()
    keyboard.bottomleft = (panel.left + 20, panel.bottom - 18)
    return {"panel": panel, "smaller": controls[0], "auto": controls[1],
            "larger": controls[2], "mode": mode, "close": close, "keyboard": keyboard}


@ui_scene
def draw_display_settings(screen, manager, font, small_font):
    overlay = pygame.Surface(screen.get_size(), pygame.SRCALPHA)
    overlay.fill((2, 4, 15, 215))
    screen.blit(overlay, (0, 0))
    layout = display_settings_layout()
    panel = layout["panel"]
    draw_neon_panel(screen, panel, UI_CYAN)
    title = font.render("DISPLAY & GUI", True, UI_CYAN)
    screen.blit(title, title.get_rect(midtop=(panel.centerx, panel.y + 16)))
    scale = round(manager.preferences["gui_scale"] * 100)
    label = small_font.render(f"GUI SIZE  {scale}%  /  AUTO FIT", True, UI_TEXT)
    screen.blit(label, label.get_rect(midtop=(panel.centerx, panel.y + 58)))
    for key, text in (("smaller", "SMALLER"), ("auto", "AUTO"), ("larger", "LARGER")):
        draw_neon_button(screen, layout[key], text, small_font, UI_GOLD)
    mode = "WINDOWED" if manager.preferences["fullscreen"] else "FULLSCREEN"
    draw_neon_button(screen, layout["mode"], f"SWITCH TO {mode}", small_font, UI_VIOLET)
    hint = small_font.render("F6 smaller / F7 larger / F8 auto / F11 display", True, UI_MUTED)
    if hint.get_width() > panel.width - 36:
        hint = pygame.transform.smoothscale(hint, (panel.width - 36, max(1, round(hint.get_height() * (panel.width - 36) / hint.get_width()))))
    hint_rect = hint.get_rect(midtop=(panel.centerx, layout["mode"].bottom + 12))
    screen.blit(hint, hint_rect)
    wheel_hint = small_font.render("Ctrl + wheel: GUI size / F9: keyboard controls", True, UI_MUTED)
    screen.blit(wheel_hint, wheel_hint.get_rect(midtop=(panel.centerx, hint_rect.bottom + 3)))
    if manager.settings_error:
        warning = pygame.font.SysFont(None, 17).render("Settings apply; preference file could not be saved.", True, UI_CORAL)
        screen.blit(warning, warning.get_rect(midbottom=(panel.centerx, layout["close"].top - 5)))
    draw_neon_button(screen, layout["close"], "DONE", small_font, UI_MINT)
    draw_neon_button(screen, layout["keyboard"], "KEYBOARD", small_font, UI_CYAN)

# Colors
BLACK = (0, 0, 0)
GREEN = (90, 245, 181)
RED = (255, 107, 112)
BLUE = (95, 155, 255)
WHITE = (230, 243, 255)
GRAY = (105, 124, 159)
DARK_GRAY = (36, 47, 74)
DARK_BLUE = (19, 34, 70)
DARKER_BLUE = (12, 23, 52)
LIGHT_BLUE = (143, 208, 255)
YELLOW = (255, 209, 104)
PURPLE = (177, 112, 255)
VIOLET = (159, 123, 255)
LAVENDER = (217, 186, 255)
CYAN = (74, 232, 255)
ORANGE = (255, 166, 92)
PINK = (255, 93, 195)
PLAYER_BLUE = (95, 155, 255)

# Shared colors keep the flight HUD, menus, and journal in the same universe.
UI_BG = (6, 8, 24)
UI_CYAN = (74, 232, 255)
UI_PINK = (255, 93, 195)
UI_GOLD = (255, 209, 104)
UI_VIOLET = (159, 123, 255)
UI_MINT = (90, 245, 181)
UI_CORAL = (255, 107, 112)
UI_TEXT = (230, 243, 255)
UI_MUTED = (140, 161, 194)
SECTOR_COLORS = (UI_CYAN, UI_VIOLET, UI_PINK, UI_MINT, UI_GOLD)
_SPACE_BACKGROUNDS = {}
_GLOW_SPRITES = {}
_BUTTON_ANIMATIONS = {}
_UI_RIPPLES = []
_UI_PRESS = None
_UI_FRAME = 0
_SHIP_ANIMATIONS = {}

# Enemy Fleet Configuration Constants
ROWS = 5
COLS = 11
ENEMY_WIDTH = 35
ENEMY_HEIGHT = 25
PADDING = 15
# Status docks no longer reserve a strip of the arena. Start the fleet closer
# to the real top edge so the front rank leaves enough room to react to fire.
OFFSET_Y = 70
MARGIN = 50
GAMEPLAY_TOP = 0  # The whole screen is playable; HUD elements are transparent overlays.
HUD_TOP_HEIGHT = 108  # Keeps edge status docks clear of the score readouts.
ENEMY_DESCENT_STEP = 2  # Reveal incoming ships a few pixels at a time.
# When no enemies remain visible, hurry hidden stragglers into view.
HIDDEN_ENEMY_CATCHUP_SPEED = 7  # Pixels per frame; preserves partial reveals.
# Restrict projectile crowding, particularly from multi-shot enemy types.
BASE_ENEMY_BULLET_CAP = 22
ENEMY_BULLET_CAP_PER_EXTRA_PLAYER = 6
BOSS_BULLET_CAP_BONUS = 6
MAX_ENEMY_SCALE = 1.3
ENEMY_SPEED_START = 0.75
ENEMY_SPEED_PER_ROUND = 0.05
ENEMY_SPEED_CAP = 1.25
ENEMY_SPEED_CAP_ROUND = 11
ENEMY_HEALTH_MULTIPLIER = 0.75
SPLITTER_FRAGMENT_COUNT = 2
SPLITTER_REGROW_FRAMES = 480  # Eight seconds at 60 FPS, independently per fragment.
SPLITTER_REGROW_STAGGER_FRAMES = 24
SPLITTER_SHARD_SPEED_MULTIPLIER = 1.15
# Checkpoints and combat pacing do not add health. Ordinary enemies receive
# only one health-tier bonus, starting after wave 50, including infinite mode.
WAVES_PER_SECTOR = 5
ENEMY_HEALTH_INCREASE_WAVE = 51
WAVES_PER_COMBAT_TIER = 20
# Fast, fragile foes remain fragile throughout the run. Armored mutations can
# still add their own armor, but the single health-tier increase skips these.
HEALTH_SCALING_EXEMPT_TYPES = frozenset((
    "speedy", "scout", "swarmer", "shardling", "blink", "phantom",
))
SAVE_FILE = Path.home() / ".neon_frontier" / "savegame.json"
SAVE_FORMAT_VERSION = 1
SAVE_SLOT_COUNT = 3
MAX_RUN_RETRIES = 3
BOSS_AIM_MAX_LEAD_PX = 135
BOSS_LATE_EXTRA_BULLET_CAP = 12
BOSS_LASER_WARNING_FRAMES = 90  # 1.5 seconds, including at wave 100.
BOSS_LASER_ACTIVE_FRAMES = 22
BOSS_ENCOUNTER_RECOVERY_FRAMES = 48

# Player Configuration Constants
PLAYER_WIDTH = 30
PLAYER_HEIGHT = 24
PLAYER_SPAWN_BOTTOM_MARGIN = 20
PLAYER_SPEED = 3.5
BASE_SHOT_COOLDOWN = 27
COOP_FIRE_COOLDOWN_STEP = 0.65  # A modest team boost; each pilot still fires slower than solo.
# Slightly stronger rapid fire as more pilots join, with per-player
# cooldowns still scaling against the number of *active* pilots.
# Solo: 3x; two pilots: 3.4x; three: 3.7x; four: 4x.
RAPID_FIRE_MULTIPLIERS = (3.0, 3.4, 3.7, 4.0)
RAPID_FIRE_LASER_MULTIPLIER = 1.75
MAX_DAMAGE_BONUS = 3
MAX_DURABILITY_BONUS = 3
MAX_HEALTH_BONUS = MAX_DURABILITY_BONUS  # Legacy save compatibility.
BASE_MAX_LIVES = 5
STARTING_LIVES = 3
DURABILITY_REGEN_DELAY_MS = 8000
DURABILITY_REGEN_INTERVAL_MS = 2000
DURABILITY_HIT_INVULN_MS = 450
# Eligible discharges arc to a second foe if one is in range, then roll for
# extra hops. The hop list limits the total number of additional targets.
LIGHTNING_HOP_CHANCES = (1.0, 0.85, 0.65, 0.45, 0.25)
BOMB_BLAST_RADIUS = 62
BULLET_TIME_RADIUS = 150
GRAVITY_FIELD_RADIUS = 150
GRAVITY_MAX_PROJECTILE_TURN = 0.65  # Total radians; a field cannot trap a shot in orbit.
BULLET_TIME_SLOWDOWN = 0.48  # Permanent movement multiplier after a shot first enters any field.
# Each distinct projectile slowed by Bullet Time grants Momentum. Frostbite
# kills build separate Shatter stacks; the stronger bonus applies, without adding.
BULLET_TIME_MAX_STACKS = 16
BULLET_TIME_SPEED_PER_STACK = 0.28  # Up to +4.48 movement/frame.
BULLET_TIME_FIRE_PER_STACK = 0.085  # Up to +136% fire rate.
SHATTER_MAX_STACKS = 6
SHATTER_SPEED_PER_STACK = 0.4  # Up to +2.4 movement/frame; below Momentum's +4.48.
SHATTER_FIRE_PER_STACK = 0.12  # Up to +72% fire rate; below Momentum's +136%.
ENEMY_AIM_LEAD_FRAMES = 4
PLAYER_COLORS = (RED, PLAYER_BLUE, CYAN, YELLOW)
PLAYER_CONTROLS = (
    (pygame.K_a, pygame.K_d, pygame.K_w, pygame.K_s, (pygame.K_SPACE, pygame.K_LSHIFT)),
    (pygame.K_LEFT, pygame.K_RIGHT, pygame.K_UP, pygame.K_DOWN, (pygame.K_RSHIFT, pygame.K_RCTRL, pygame.K_KP0, pygame.K_INSERT)),
    (pygame.K_j, pygame.K_l, pygame.K_i, pygame.K_k, (pygame.K_u, pygame.K_SEMICOLON, pygame.K_h)),
    (pygame.K_KP4, pygame.K_KP6, pygame.K_KP8, pygame.K_KP5, (pygame.K_KP_ENTER, pygame.K_KP7)),
)
DEFAULT_PLAYER_CONTROLS = PLAYER_CONTROLS
PLAYER_AUTOFIRE = (False, False, False, False)
FIRE_INPUT_BUFFER_MS = 150
EMERGENCY_WARP_SHIELD_MS = 1500
CRYO_SLOW_MS = 2000
FROSTBITE_ENEMY_SPEED_MULTIPLIER = 0.35
FROSTBITE_BOSS_SPEED_MULTIPLIER = 0.75
NOVA_COUNTDOWN_MS = 3000
NOVA_PULSE_RADIUS = 300


class HeldInput:
    """Retain reported key events, including a tap entirely between frames.

    Each pilot can hold any number of keys; there is no per-frame key limit.
    This cannot recover keys that a keyboard's hardware never reports.
    """

    def __init__(self):
        self.held = set()
        self.pressed = set()
        self.fire_deadlines = {}
        self.focused = True

    def begin_frame(self, now=None):
        self.pressed.clear()
        now = pygame.time.get_ticks() if now is None else now
        self.fire_deadlines = {key: deadline for key, deadline in self.fire_deadlines.items()
                               if deadline >= now}

    def discard_taps(self):
        """Do not carry menu/pause taps into combat; preserve physically held keys."""
        self.pressed.clear()
        self.fire_deadlines.clear()

    def clear(self):
        self.held.clear()
        self.discard_taps()

    def process_event(self, event, now=None):
        if event.type == pygame.WINDOWFOCUSLOST:
            self.clear()
            self.focused = False
        elif event.type == pygame.WINDOWFOCUSGAINED:
            self.focused = True
        elif event.type == pygame.ACTIVEEVENT and event.state & pygame.APPINPUTFOCUS:
            self.focused = bool(event.gain)
            if not self.focused:
                self.clear()
        elif event.type == pygame.KEYDOWN and self.focused:
            # Ignore OS key-repeat events, which must not queue extra shots.
            if event.key not in self.held:
                now = pygame.time.get_ticks() if now is None else now
                self.pressed.add(event.key)
                self.fire_deadlines[event.key] = now + FIRE_INPUT_BUFFER_MS
            self.held.add(event.key)
        elif event.type == pygame.KEYUP:
            self.held.discard(event.key)

    def __getitem__(self, key):
        return self.focused and (key in self.held or key in self.pressed)

    def fire_requested(self, shoot_keys, now):
        return self.focused and any(key in self.held
            or self.fire_deadlines.get(key, -1) >= now for key in shoot_keys)

    def consume_fire(self, shoot_keys):
        # Alternative fire keys belong to one action, not separate volleys.
        for key in shoot_keys:
            self.fire_deadlines.pop(key, None)


KEYBOARD_ACTIONS = ("LEFT", "RIGHT", "UP", "DOWN", "FIRE")
KEYBOARD_RESERVED_KEYS = frozenset((pygame.K_ESCAPE, pygame.K_F6, pygame.K_F7,
                                   pygame.K_F8, pygame.K_F9, pygame.K_F11))


def keyboard_preferences_path():
    return display_preferences_path().with_name("keyboard_settings.json")


def default_keyboard_preferences():
    return {"bindings": [[*row[:4], list(row[4])] for row in DEFAULT_PLAYER_CONTROLS],
            "auto_fire": [False] * 4}


def validate_keyboard_preferences(data):
    """Reject an invalid mapping as a whole; never let two pilots share a key."""
    if not isinstance(data, dict):
        return None
    rows, auto_fire = data.get("bindings"), data.get("auto_fire")
    if (not isinstance(rows, list) or len(rows) != 4
            or not isinstance(auto_fire, list) or len(auto_fire) != 4
            or any(type(value) is not bool for value in auto_fire)):
        return None
    allowed = {value for name, value in vars(pygame).items()
               if name.startswith("K_") and type(value) is int and value != pygame.K_UNKNOWN}
    seen, result = set(), []
    for row in rows:
        if (not isinstance(row, list) or len(row) != 5
                or not isinstance(row[4], list) or not 1 <= len(row[4]) <= 8):
            return None
        keys = [*row[:4], *row[4]]
        if any(type(key) is not int or key not in allowed or key in KEYBOARD_RESERVED_KEYS
               or key in seen for key in keys) or len(keys) != len(set(keys)):
            return None
        seen.update(keys)
        result.append([*row[:4], list(row[4])])
    return {"bindings": result, "auto_fire": list(auto_fire)}


def load_keyboard_preferences(filename=None):
    filename = keyboard_preferences_path() if filename is None else Path(filename)
    try:
        if filename.exists() and filename.stat().st_size <= 8192:
            validated = validate_keyboard_preferences(json.loads(filename.read_text(encoding="utf-8")))
            if validated is not None:
                return validated
    except (OSError, ValueError, TypeError, RecursionError):
        pass
    return default_keyboard_preferences()


def apply_keyboard_preferences(preferences):
    global PLAYER_CONTROLS, PLAYER_AUTOFIRE
    PLAYER_CONTROLS = tuple((*row[:4], tuple(row[4])) for row in preferences["bindings"])
    PLAYER_AUTOFIRE = tuple(preferences["auto_fire"])


def control_key_label(key):
    names = {pygame.K_LEFT: "LEFT", pygame.K_RIGHT: "RIGHT", pygame.K_UP: "UP",
             pygame.K_DOWN: "DOWN", pygame.K_LSHIFT: "L SHIFT", pygame.K_RSHIFT: "R SHIFT",
             pygame.K_LCTRL: "L CTRL", pygame.K_RCTRL: "R CTRL",
             pygame.K_KP_ENTER: "NUM ENTER", pygame.K_SEMICOLON: ";"}
    return names.get(key, pygame.key.name(key).upper().replace("[", "NUM ").replace("]", ""))


def player_control_labels(index):
    left, right, up, down, fire = PLAYER_CONTROLS[index]
    movement = " / ".join(control_key_label(key) for key in (up, left, down, right))
    firing = " / ".join(control_key_label(key) for key in fire)
    if PLAYER_AUTOFIRE[index]:
        firing = "AUTO FIRE ON"
    return movement, firing


@ui_layout
def keyboard_controls_layout():
    panel = pygame.Rect(0, 0, min(700, SCREEN_WIDTH - 24), min(400, SCREEN_HEIGHT - 24))
    panel.center = (SCREEN_WIDTH // 2, SCREEN_HEIGHT // 2)
    gap = 10
    inner = panel.width - 32
    tabs = [pygame.Rect(panel.x + 16 + index * ((inner + gap) // 4), panel.y + 43,
                        (inner - gap * 3) // 4, 28) for index in range(4)]
    width = (inner - gap) // 2
    cells = [pygame.Rect(panel.x + 16 + index % 2 * (width + gap),
                         panel.y + 84 + index // 2 * 40, width, 32) for index in range(6)]
    footer_y = panel.y + 214
    return {"panel": panel, "tabs": tabs, "actions": cells[:5], "auto_fire": cells[5],
            "reset": pygame.Rect(panel.x + 16, footer_y, width, 32),
            "done": pygame.Rect(panel.x + 16 + width + gap, footer_y, width, 32),
            "help": pygame.Rect(panel.x + 16, panel.y + 258, inner, 19),
            "status": pygame.Rect(panel.x + 16, panel.y + 280, inner, 19),
            "held": pygame.Rect(panel.x + 16, panel.y + 302, inner, 19)}


class KeyboardControls:
    """Remap received keys and test rollover; hardware omissions stay unrecoverable."""

    def __init__(self, settings_file=None):
        self.settings_file = keyboard_preferences_path() if settings_file is None else Path(settings_file)
        self.preferences = load_keyboard_preferences(self.settings_file)
        self.player = 0
        self.waiting_action = None
        self.held = set()
        self.status = "Click an action, then press a key. Escape cancels a change."
        apply_keyboard_preferences(self.preferences)

    def begin(self):
        self.held.clear()
        self.waiting_action = None
        self.status = "Click an action, then press a key. Escape cancels a change."

    def _save(self):
        apply_keyboard_preferences(self.preferences)
        # The shared atomic JSON writer does not touch any run-save files.
        if not save_display_preferences(self.preferences, self.settings_file):
            self.status = "Controls apply now; the settings file could not be saved."
            return False
        return True

    def bind(self, action, key):
        if type(action) is not int or not 0 <= action < 5:
            return False
        if key in KEYBOARD_RESERVED_KEYS:
            self.status = "That key is reserved for menus or display controls."
            return False
        candidate = {"bindings": [[*row[:4], list(row[4])] for row in self.preferences["bindings"]],
                     "auto_fire": list(self.preferences["auto_fire"])}
        for player, row in enumerate(candidate["bindings"]):
            for other_action, keys in enumerate((*[(value,) for value in row[:4]], tuple(row[4]))):
                if key in keys and (player != self.player or other_action != action):
                    self.status = f"{control_key_label(key)} is already P{player + 1} {KEYBOARD_ACTIONS[other_action]}."
                    return False
        candidate["bindings"][self.player][action] = [key] if action == 4 else key
        if validate_keyboard_preferences(candidate) is None:
            self.status = "That key cannot be used. Try a different key."
            return False
        self.preferences = candidate
        self.status = f"P{self.player + 1} {KEYBOARD_ACTIONS[action]} is now {control_key_label(key)}."
        self._save()
        return True

    def process_event(self, event):
        """Consume modal input; return True when the modal should close."""
        if event.type in (pygame.WINDOWFOCUSLOST,):
            self.held.clear()
        elif event.type == pygame.KEYUP:
            self.held.discard(event.key)
        elif event.type == pygame.KEYDOWN:
            if event.key == pygame.K_F9:
                return True
            if event.key == pygame.K_ESCAPE:
                if self.waiting_action is None:
                    return True
                self.waiting_action = None
                self.status = "Change canceled. Previous controls kept."
            else:
                self.held.add(event.key)
                if self.waiting_action is not None and not getattr(event, "repeat", False):
                    if self.bind(self.waiting_action, event.key):
                        self.waiting_action = None
        elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
            layout = keyboard_controls_layout()
            for index, tab in enumerate(layout["tabs"]):
                if tab.collidepoint(event.pos):
                    self.player, self.waiting_action = index, None
                    return False
            for index, rect in enumerate(layout["actions"]):
                if rect.collidepoint(event.pos):
                    self.waiting_action = index
                    self.status = f"Press a key for P{self.player + 1} {KEYBOARD_ACTIONS[index]}."
                    return False
            if layout["auto_fire"].collidepoint(event.pos):
                self.waiting_action = None
                self.preferences["auto_fire"][self.player] = not self.preferences["auto_fire"][self.player]
                self.status = "Auto-fire reduces the number of keys held during a fight."
                self._save()
            elif layout["reset"].collidepoint(event.pos):
                self.preferences = default_keyboard_preferences()
                self.waiting_action = None
                self.status = "Default controls restored for all four pilots."
                self._save()
            elif layout["done"].collidepoint(event.pos):
                return True
        return False

    def draw(self, screen, font, small_font):
        with ui_dimensions(screen.get_size()):
            self._draw(screen, font, small_font)

    def _draw(self, screen, font, small_font):
        overlay = pygame.Surface(screen.get_size(), pygame.SRCALPHA)
        overlay.fill((2, 4, 15, 225))
        screen.blit(overlay, (0, 0))
        layout = keyboard_controls_layout()
        panel = layout["panel"]
        color = PLAYER_COLORS[self.player]
        draw_neon_panel(screen, panel, color)
        draw_fitted_text(screen, "KEYBOARD CONTROLS / F9", font, color,
                         pygame.Rect(panel.x + 16, panel.y + 10, panel.width - 32, 25))
        for index, rect in enumerate(layout["tabs"]):
            draw_neon_button(screen, rect, f"P{index + 1}", small_font, PLAYER_COLORS[index],
                             selected=index == self.player)
        for action, rect in enumerate(layout["actions"]):
            keys = self.preferences["bindings"][self.player][action]
            label = " / ".join(control_key_label(key) for key in keys) if action == 4 else control_key_label(keys)
            if self.waiting_action == action:
                label = "PRESS A KEY..."
            draw_neon_button(screen, rect, f"{KEYBOARD_ACTIONS[action]}: {label}", small_font, color,
                             selected=self.waiting_action == action)
        auto = "ON" if self.preferences["auto_fire"][self.player] else "OFF"
        draw_neon_button(screen, layout["auto_fire"], f"AUTO-FIRE: {auto}", small_font, UI_MINT)
        draw_neon_button(screen, layout["reset"], "RESTORE ALL DEFAULTS", small_font, UI_GOLD)
        draw_neon_button(screen, layout["done"], "DONE", small_font, UI_CYAN)
        draw_fitted_text(screen, "Missing held keys? Try Auto-fire or remap. Keyboard hardware limits still apply.",
                         small_font, UI_MUTED, layout["help"])
        draw_fitted_text(screen, self.status, small_font, UI_TEXT, layout["status"])
        held = " / ".join(control_key_label(key) for key in sorted(self.held)) or "none"
        draw_fitted_text(screen, f"RECEIVED KEYS ({len(self.held)}): {held}", small_font, UI_MINT,
                         layout["held"])

# Transition Constants
TRANSITION_DURATION = 120  # 2 seconds at 60 FPS
RESPAWN_DURATION = 5000
SPAWN_SHIELD_DURATION = 5000
ENEMY_PROJECTILE_SPEED_MULTIPLIER = 0.75
STARTING_ROUND = 1
MAX_CAMPAIGN_ROUND = 100

# --- Bunker / Shield Constants ---
BLOCK_SIZE = 5
BUNKER_SHAPE = [
    "  XXXXXXX  ",
    " XXXXXXXXX ",
    "XXXXXXXXXXX",
    "XXXXXXXXXXX",
    "XXX     XXX",
    "XX       XX"
]

# --- Pixel-art templates, scaled to each ship's dimensions ---
PLAYER_ART = ["    X    ", "   XXX   ", "   XXX   ", " XXXXXXX ", "XXXXXXXXX", "XXXXXXXXX"]

# Standard Variations (3 models/colors)
STANDARD_ART_V1 = ["  X   X  ", "   X X   ", "  XXXXX  ", "XX XXX XX", "XXXXXXXXX", "X XXXXX X", "X X   X X", "   X X   "]
STANDARD_ART_V2 = ["   XXX   ", " XXXXXXX ", "XXXXXXXXX", "XX  X  XX", "XXXXXXXXX", "  XX XX  ", " XX   XX ", "XX     XX"]
STANDARD_ART_V3 = ["  XX XX  ", " XXXXXXX ", "XXXXXXXXX", "XXX X XXX", "XXXXXXXXX", " X     X ", "X X   X X", " X     X "]

# Shooter Variations (3 models/colors)
SHOOTER_ART_V1 = ["  X   X  ", "   X X   ", "  XXXXX  ", "XX XXX XX", "XXXXXXXXX", "X X   X X", "X       X", " X     X "]
SHOOTER_ART_V2 = ["X   X   X", "XX XXX XX", "XXXXXXXXX", "XX  X  XX", "XXXXXXXXX", "  XXXXX  ", "   X X   ", "   XXX   "]
SHOOTER_ART_V3 = ["   XXX   ", "  X X X  ", " XXXXXXX ", "XX XXX XX", "XXXXXXXXX", "  X X X  ", " X     X ", "X       X"]

# Speedy Variations (3 models/colors)
SPEEDY_ART_V1 = ["   XXX   ", "  XXXXX  ", " XXXXXXX ", "XX X X XX", "XXXXXXXXX", " X X X X ", "X       X", " X     X "]
SPEEDY_ART_V2 = ["    X    ", "   XXX   ", "X XXXXX X", "XXXXXXXXX", "XX XXX XX", "X   X   X", "    X    ", "   X X   "]
SPEEDY_ART_V3 = [" X     X ", "  XXXXX  ", " XXXXXXX ", "XXX X XXX", "XXXXXXXXX", " XXXXXXX ", "  X   X  ", " X     X "]
SCOUT_ART = ["   X X   ", "  XXXXX  ", " XXXXXXX ", "XX  X  XX", "  XXXXX  ", " X  X  X "]
STRIKER_ART = ["    X    ", "  X XXX X", " XXXXXXX ", "XX XXX XX", " XXXXXXX ", " X X X X ", "   X X   "]

TANK_ART = ["  XXXXX  ", " XXXXXXX ", "XX XXX XX", "XXXXXXXXX", "XX XXX XX", " XXXXXXX ", "  X   X  "]
DIVER_ART = ["    X    ", "   XXX   ", "  XXXXX  ", " XXXXXXX ", "XX XXX XX", "  X   X  "]
WEAVER_ART = ["X       X", "XX     XX", " XXXXXXX ", "XX XXX XX", "XXXXXXXXX", " X XXX X ", "  X   X  "]
SNIPER_ART = ["    X    ", "   XXX   ", "  XXXXX  ", " XXXXXXX ", "   XXX   ", "   XXX   ", "   X X   "]
BOMBER_ART = ["   XXX   ", "  XXXXX  ", " XXXXXXX ", "XX XXX XX", "XXXXXXXXX", "  XXXXX  ", "   X X   "]
SWARMER_ART = ["   X X   ", "  XXXXX  ", " XXXXXX X", "XXXXXXXXX", "  X   X  "]
LANCER_ART = ["    X    ", "   XXX   ", "  XXXXX  ", " XXXXXXX ", "XX  X  XX", "  X X X  ", " X     X ", "   X X   "]
BULWARK_ART = ["  XXXXX  ", " XXXXXXX ", "XXXXXXXXX", "XX XXX XX", "XXXXXXXXX", "XXXXXXXXX", " XXXXXXX ", " XX   XX "]
SPLITTER_ART = ["   X X   ", "  XXXXX  ", " XXXXXXX ", "XX  X  XX", "XXXXXXXXX", " X XXX X ", " X     X "]
SHARDLING_ART = ["  X X  ", " XXXXX ", "XX X XX", "  X X  "]
WARDEN_ART = ["   XXX   ", " XXXXXXX ", "XX XXX XX", "XXXXXXXXX", " X XXX X ", " X     X "]
ARTILLERY_ART = ["   XXX   ", " XXXXXXX ", "XXXXXXXXX", "XX XXX XX", " XXXXXXX ", "   XXX   ", "   X X   "]
VOLLEY_ART = [" X  X  X ", " XXXXXXX ", "XX XXX XX", "XXXXXXXXX", " X XXX X ", "  X   X  "]
MINE_LAYER_ART = ["   XXX   ", " XXXXXXX ", "XX X X XX", "XXXXXXXXX", "  XX XX  ", " X     X "]
SEEKER_ART = ["    X    ", "   XXX   ", "  XXXXX  ", " XXXXXXX ", "XX XXX XX", "   X X   "]
RICOCHET_ART = ["X       X", " XX   XX ", "  XXXXX  ", "XXXXXXXXX", "  XXXXX  ", " X     X "]
PRISM_ART = ["    X    ", "   XXX   ", " XXXXXX  ", "XXXXXXXXX", " XXXXXX  ", "  X  X   "]
PULSE_ART = ["   XXX   ", " X XXX X ", "XXXXXXXXX", "XX XXX XX", "XXXXXXXXX", " X XXX X ", "   XXX   "]
BLINK_ART = [" X     X ", "  X   X  ", " XXXXXXX ", "XX XXX XX", " XXXXXXX ", "  X   X  "]
CHARGER_ART = ["      X  ", "    XXX  ", "  XXXXXXX", "XXXXXXXXX", "  XXXXXXX", "    XXX  "]
MEDIC_ART = ["   XXX   ", " X XXXXX ", "XXXXXXXXX", "XX XXX XX", " X XXX X ", "   X X   "]
ORBIT_ART = ["X   X   X", " XX   XX ", " XXXXXXX ", "XX XXX XX", " XXXXXXX ", " XX   XX "]
SCATTERER_ART = [" X X X X ", " XXXXXXX ", "XX XXX XX", "XXXXXXXXX", " X XXX X ", "X   X   X"]
PHANTOM_ART = ["   X X   ", "  XXXXX  ", " XXXXXX X", "XXXXXXXXX", " X XXX X ", "  X   X  "]

# Boss Art Matrix
BOSS_ART = [
    "  X   X  ",
    "   XXX   ",
    " XXXXXXX ",
    "XX X X XX",
    "XXXXXXXXX",
    " X XXX X ",
    "X X   X X"
]

# Campaign landmarks have their own hulls rather than scaled regular-boss art.
# Silhouettes remain inside the single physical collision body; decorative
# rings and fins below never become invisible extra hitboxes.
MILESTONE_BOSSES = {
    25: {
        "kind": "bulwark", "name": "IRON CITADEL",
        "reward": "rapid_fire",
        "subtitle": "ARMORED QUARTER GUARDIAN", "color": UI_GOLD,
        "hp_multiplier": 1.25, "size": (126, 82),
        "art": (
            " XX             XX ",
            "XXXX  XXXXXXX  XXXX",
            "XXXXXXXXXXXXXXXXXXX",
            "XXX XX XXXXX XX XXX",
            "XXX XX XXXXX XX XXX",
            "XXXXXXXXXXXXXXXXXXX",
            " XXX  X  X  X  XXX ",
            "  XX  XXXXXXX  XX  ",
            "  XX   XXXXX   XX  ",
            "       X X X       ",
        ),
    },
    50: {
        "kind": "helix", "name": "HELIX MATRIARCH",
        "reward": "homing",
        "subtitle": "TWIN-SPIRAL QUARTER GUARDIAN", "color": UI_MINT,
        "hp_multiplier": 1.30, "size": (136, 94),
        "art": (
            "  XX           XX  ",
            " XXX   XXXXX   XXX ",
            "XXXX  XXXXXXX  XXXX",
            " XXX XXXXXXXX XXX  ",
            "  XXXXXXXXXXXXXXX  ",
            "   XXX XX XX XXX   ",
            "  XXXX XXXXX XXXX  ",
            " XXX  XXXXXXX  XXX ",
            " XX    XXXXX    XX ",
            "  X  XXX   XXX  X  ",
            "     XX     XX     ",
        ),
    },
    75: {
        "kind": "tempest", "name": "TEMPEST ARCHON",
        "reward": "bullet_time",
        "subtitle": "STORM QUARTER GUARDIAN", "color": UI_CYAN,
        "hp_multiplier": 1.35, "size": (148, 102),
        "art": (
            "X        X        X",
            "XX      XXX      XX",
            " XXX   XXXXX   XXX ",
            " XXXXX XXXXX XXXXX ",
            "  XXXXXXXXXXXXXXX  ",
            " XXXX XX XX XX XXXX",
            "XXX  XXXXXXXXX  XXX",
            "XX    XXXXXXX    XX",
            "X   XXX XXX XXX   X",
            "     XX  X  XX     ",
            "      X     X      ",
        ),
    },
    100: {
        "kind": "eclipse", "name": "ECLIPSE SOVEREIGN",
        "reward": "emergency_warp",
        "subtitle": "FINAL BOSS", "color": UI_PINK,
        "hp_multiplier": 1.50, "size": (190, 126),
        "art": (
            "   XX     XXX     XX   ",
            "  XXXX   XXXXX   XXXX  ",
            " XXX XXXXXXXXXXXXX XXX ",
            "XXX XXXXXXXXXXXXXXX XXX",
            "XX XXX   XXXXX   XXX XX",
            "XXXXX  XX XXX XX  XXXXX",
            "XXXX  XXX XXX XXX  XXXX",
            "XXXXX  XX XXX XX  XXXXX",
            "XX XXX   XXXXX   XXX XX",
            "XXX XXXXXXXXXXXXXXX XXX",
            " XXX XXXXXXXXXXXXX XXX ",
            "  XXXX  XXXXXXX  XXXX  ",
            "   XX  XXX X XXX  XX   ",
            "       XX  X  XX       ",
        ),
    },
}


def milestone_boss_profile(round_num):
    """Only the four campaign landmarks receive unique single-boss encounters."""
    return MILESTONE_BOSSES.get(round_num)

# Lookup lists for individual enemy visual randomization
STANDARD_VARIATIONS = [
    {"color": (91, 242, 169), "art": STANDARD_ART_V1},
    {"color": (182, 119, 255), "art": STANDARD_ART_V2},
    {"color": (74, 221, 255), "art": STANDARD_ART_V3},
]

SHOOTER_VARIATIONS = [
    {"color": (255, 87, 168), "art": SHOOTER_ART_V1},
    {"color": (255, 141, 74), "art": SHOOTER_ART_V2},
    {"color": (255, 211, 94), "art": SHOOTER_ART_V3},
]

SPEEDY_VARIATIONS = [
    {"color": (191, 250, 83), "art": SPEEDY_ART_V1},
    {"color": (100, 155, 255), "art": SPEEDY_ART_V2},
    {"color": (255, 105, 130), "art": SPEEDY_ART_V3},
]


def enemy_color_variants(art, *colors):
    # Body palettes are cosmetic; mutation outlines retain their own meaning.
    return [{"color": color, "art": art} for color in colors]


VISUAL_VARIATIONS = {
    "standard": STANDARD_VARIATIONS,
    "shooter": SHOOTER_VARIATIONS,
    "speedy": SPEEDY_VARIATIONS,
    "scout": enemy_color_variants(SCOUT_ART, (80, 174, 255), (76, 235, 216), (157, 140, 255)),
    "striker": enemy_color_variants(STRIKER_ART, (255, 91, 208), (255, 115, 112), (185, 122, 255)),
    "tank": enemy_color_variants(TANK_ART, (255, 210, 83), (255, 150, 91), (190, 233, 112)),
    "diver": enemy_color_variants(DIVER_ART, (255, 98, 153), (125, 176, 255), (255, 164, 96)),
    "weaver": enemy_color_variants(WEAVER_ART, (168, 239, 91), (75, 231, 185), (206, 167, 255)),
    "sniper": enemy_color_variants(SNIPER_ART, (255, 158, 69), (255, 211, 111), (247, 117, 193)),
    "bomber": enemy_color_variants(BOMBER_ART, (255, 103, 97), (255, 165, 85), (223, 121, 255)),
    "swarmer": enemy_color_variants(SWARMER_ART, (190, 243, 98), (93, 232, 183), (255, 218, 99)),
    "lancer": enemy_color_variants(LANCER_ART, (255, 109, 222), (139, 155, 255), (255, 181, 112)),
    "bulwark": enemy_color_variants(BULWARK_ART, (204, 231, 255), (193, 172, 255), (255, 221, 145)),
    "splitter": enemy_color_variants(SPLITTER_ART, (255, 111, 141), (219, 139, 255), (255, 179, 114)),
    "shardling": enemy_color_variants(SHARDLING_ART, (255, 151, 128), (227, 160, 255), (255, 207, 130)),
    "warden": enemy_color_variants(WARDEN_ART, (91, 239, 213), (114, 189, 255), (166, 241, 142)),
    "artillery": enemy_color_variants(ARTILLERY_ART, (255, 166, 77), (255, 204, 107), (255, 117, 145)),
    "volley": enemy_color_variants(VOLLEY_ART, (255, 112, 174), (194, 136, 255), (255, 184, 115)),
    "mine_layer": enemy_color_variants(MINE_LAYER_ART, (255, 167, 87), (208, 223, 100), (255, 119, 164)),
    "seeker": enemy_color_variants(SEEKER_ART, (255, 100, 130), (240, 142, 255), (255, 179, 99)),
    "ricochet": enemy_color_variants(RICOCHET_ART, (126, 205, 255), (139, 248, 219), (199, 160, 255)),
    "prism": enemy_color_variants(PRISM_ART, (217, 129, 255), (110, 218, 255), (255, 141, 209)),
    "pulse": enemy_color_variants(PULSE_ART, (255, 226, 105), (255, 150, 125), (191, 159, 255)),
    "blink": enemy_color_variants(BLINK_ART, (126, 165, 255), (188, 137, 255), (99, 232, 224)),
    "charger": enemy_color_variants(CHARGER_ART, (255, 117, 99), (255, 180, 85), (243, 132, 212)),
    "medic": enemy_color_variants(MEDIC_ART, (108, 244, 164), (104, 228, 232), (198, 233, 143)),
    "orbit": enemy_color_variants(ORBIT_ART, (137, 242, 234), (147, 181, 255), (210, 158, 255)),
    "scatterer": enemy_color_variants(SCATTERER_ART, (255, 192, 100), (255, 125, 165), (177, 222, 125)),
    "phantom": enemy_color_variants(PHANTOM_ART, (195, 171, 255), (139, 211, 255), (247, 164, 220)),
}

VISUAL_VARIATIONS.update({
    profile["name"].lower().replace(" ", "_"): [
        {"color": profile["color"], "art": profile["art"]}]
    for profile in MILESTONE_BOSSES.values()
})

ENEMY_JOURNAL = (
    ("Standard", "Basic enemy that travels with the formation."),
    ("Shooter", "Periodically fires straight downward shots."),
    ("Speedy", "Fast-moving attacker; a swift mutation can push it beyond normal speed."),
    ("Scout", "Small, nimble enemy that darts across the formation."),
    ("Striker", "Fires fast, aimed shots at a randomly chosen active pilot."),
    ("Tank", "Has extra armor and takes several hits to destroy."),
    ("Diver", "Dives vertically while sweeping across the screen."),
    ("Weaver", "Moves side to side while weaving up and down."),
    ("Sniper", "Fires a very fast, carefully aimed shot."),
    ("Bomber", "Drops a mine that bursts into a ring of projectiles."),
    ("Swarmer", "Appears in clusters and moves quickly."),
    ("Lancer", "Fires a pair of aimed bolts from either side."),
    ("Bulwark", "Heavily armored and occasionally fires straight downward shots."),
    (
        "Splitter",
        f"Splits into {SPLITTER_FRAGMENT_COUNT} slower shardlings that drift together. Each survivor regrows independently after about {SPLITTER_REGROW_FRAMES / 60:g} seconds.",
    ),
    ("Shardling", f"Fragile Splitter fragment that drifts with its sibling. Each survivor regrows after about {SPLITTER_REGROW_FRAMES / 60:g} seconds."),
    ("Warden", "At wave start, gives nearby allies one shield charge that blocks a hit."),
    ("Artillery", "Fires a large projectile aimed at an active pilot."),
    ("Volley", "Fires a three-shot fan toward a randomly chosen active pilot."),
    ("Mine Layer", "Drops two timed mines that burst into small rings of shots."),
    ("Seeker", "Launches a projectile that slowly homes in on a player."),
    ("Ricochet", "Fires aimed shots that can bounce off the left and right screen edges."),
    ("Prism", "Shoots a projectile that splits into a radial burst."),
    ("Pulse", "Releases a ring of shots in every direction."),
    ("Blink", "Periodically blinks to a new position along its row."),
    ("Charger", "Moves laterally and fires fast, aimed shots."),
    ("Medic", "Heals one nearby wounded ally at a time; cannot create shields."),
    ("Orbit", "Sweeps in broad arcs while moving across the screen."),
    ("Scatterer", "Fires a wide spread of shots to cover more space."),
    ("Phantom", "Fires a wavering projectile that sways as it travels."),
    ("Boss", "One boss appears every fifth wave. Waves 25, 50 and 75 feature stronger quarter guardians; wave 100 has a unique final boss."),
    ("Iron Citadel", "Wave 25: marked Iron Gate openings and split Hammer Fans. Defeat grants every pilot Rapid Fire automatically."),
    ("Helix Matriarch", "Wave 50: mirrored wing ribbons and rotating Prism Blooms. Defeat grants every pilot Homing Shots automatically."),
    ("Tempest Archon", "Wave 75: warned changing Storm Channels and outward Crosswind rain. Defeat grants every pilot Bullet Time automatically."),
    ("Eclipse Sovereign", "Wave 100 final boss: gates and Corona escalate into lances and Horizon rain. Defeat grants every pilot Emergency Warp automatically."),
)
ENEMY_MUTATIONS = (
    (
        "ARMORED",
        "Gives lightweight enemies one extra HP; the toughest already have their own armor.",
        LIGHT_BLUE,
    ),
    (
        "SWIFT",
        "Most ships gain faster independent movement. Weavers and Orbits weave 15% faster within the normal speed cap; Swift Speedies can exceed that cap.",
        YELLOW,
    ),
    ("VOLATILE", "Explodes into a ring of shots when destroyed.", PINK),
)

BOSS_ATTACKS = {
    "fan": (RED, 12),
    "aimed": (ORANGE, 9),
    "curtain": (PURPLE, 10),
    "spiral": (CYAN, 7),
    "crossfire": (YELLOW, 4),
    "laser": (PINK, 1),
    "double_lance": (LIGHT_BLUE, 5),
    "heavy_orb": (VIOLET, 9),
    "sweep": (VIOLET, 8),
    "minefield": (ORANGE, 5),
    "pincer": (RED, 2),
    "triple_burst": (WHITE, 5),
    "ring_burst": (CYAN, 6),
    "homing": (PINK, 1),
    "wave_shot": (YELLOW, 4),
    "scatter": (WHITE, 8),
    "splitter": (VIOLET, 5),
    "bouncer": (LIGHT_BLUE, 5),
    "mine_burst": (ORANGE, 4),
    "sniper": (RED, 3),
    "slow_fan": (LIGHT_BLUE, 9),
    "zigzag": (CYAN, 5),
    "double_wave": (YELLOW, 4),
    "cross_lanes": (PURPLE, 6),
    "bombardment": (ORANGE, 5),
    "delayed_ring": (LIGHT_BLUE, 4),
    "ricochet": (PINK, 2),
    "seeker_pair": (PINK, 1),
    "triad": (WHITE, 6),
    "pulse_burst": (VIOLET, 3),
}
MUTATION_COLORS = {
    "armored": LIGHT_BLUE,
    "swift": YELLOW,
    "volatile": PINK,
}
POWERUP_TYPES = (
    "life", "shield", "rapid_fire", "speed", "triple_shot",
    "laser", "magnet", "bomb", "bullet_time", "piercing", "damage_up", "health_up",
    "homing", "lightning", "score_boost", "cryo", "orbit_drones",
    "supply_beacon", "gravity_well", "emergency_warp", "nova_pulse",
    "missile_swarm", "reflector", "chain_reaction",
)
# Utility pickups appear more often than powerful weapons and defensive fields.
# Integer weights total 300; each permanent upgrade has weight four, or 1 in 75.
POWERUP_SPAWN_WEIGHTS = {
    "life": 12, "shield": 9, "rapid_fire": 9, "speed": 33,
    "triple_shot": 9, "laser": 6, "magnet": 36, "bomb": 12,
    "bullet_time": 6, "piercing": 15, "damage_up": 4, "health_up": 4, "homing": 12,
    "lightning": 6, "score_boost": 40, "cryo": 9, "orbit_drones": 12,
    "supply_beacon": 9, "gravity_well": 9, "emergency_warp": 9,
    "nova_pulse": 9, "missile_swarm": 9, "reflector": 12, "chain_reaction": 9,
}
RARE_POWERUP_CHANCE = POWERUP_SPAWN_WEIGHTS["damage_up"] / sum(POWERUP_SPAWN_WEIGHTS.values())
COMMON_POWERUP_TYPES = tuple(powerup_type for powerup_type in POWERUP_TYPES
                             if powerup_type not in ("damage_up", "health_up"))
POWERUP_COLORS = {
    "life": GREEN,
    "shield": CYAN,
    "rapid_fire": YELLOW,
    "speed": BLUE,
    "triple_shot": WHITE,
    "laser": ORANGE,
    "magnet": PURPLE,
    "bomb": RED,
    "bullet_time": VIOLET,
    "piercing": LIGHT_BLUE,
    "damage_up": PINK,
    "health_up": (100, 255, 170),
    "homing": LIGHT_BLUE,
    "lightning": (150, 245, 255),
    "score_boost": YELLOW,
    "cryo": (125, 235, 255),
    "orbit_drones": (255, 186, 95),
    "supply_beacon": (145, 255, 120),
    "gravity_well": (170, 125, 255),
    "emergency_warp": (60, 240, 170),
    "nova_pulse": (255, 242, 130),
    "missile_swarm": (255, 130, 95),
    "reflector": (115, 210, 255),
    "chain_reaction": (255, 125, 210),
}
POWERUP_LABELS = {
    "life": "EXTRA LIFE",
    "shield": "SHIELD",
    "rapid_fire": "RAPID FIRE",
    "speed": "SPEED BOOST",
    "triple_shot": "TRIPLE SHOT",
    "laser": "LASER SHOT",
    "magnet": "MAGNET",
    "bomb": "BOMB SHOT",
    "bullet_time": "BULLET TIME",
    "piercing": "PIERCING SHOT",
    "damage_up": "DAMAGE UP",
    "health_up": "DURABILITY",
    "homing": "HOMING SHOT",
    "lightning": "CHAIN LIGHTNING",
    "score_boost": "DOUBLE SCORE",
    "cryo": "FROSTBITE",
    "orbit_drones": "ORBIT DRONES",
    "supply_beacon": "SUPPLY BEACON",
    "gravity_well": "GRAVITY WELL",
    "emergency_warp": "EMERGENCY WARP",
    "nova_pulse": "NOVA PULSE",
    "missile_swarm": "MISSILE SWARM",
    "reflector": "REFLECTOR",
    "chain_reaction": "CHAIN REACTION",
}
POWERUP_TIMER_LABELS = {
    "shield": "SHIELD",
    "rapid_fire": "RAPID",
    "speed": "SPEED",
    "triple_shot": "TRIPLE",
    "laser": "LASER",
    "magnet": "MAGNET",
    "bomb": "BOMB",
    "bullet_time": "BULLET TIME",
    "piercing": "PIERCE",
    "homing": "HOMING",
    "lightning": "LIGHTNING",
    "score_boost": "2X SCORE",
    "cryo": "FROSTBITE",
    "orbit_drones": "DRONES",
    "gravity_well": "GRAVITY",
    "chain_reaction": "CHAIN REACTION",
}
POWERUP_DURATIONS = {
    "shield": 15000,
    "rapid_fire": 15000,
    "speed": 30000,
    "triple_shot": 15000,
    "laser": 10000,
    "magnet": 60000,
    "bomb": 15000,
    "bullet_time": 45000,
    "piercing": 15000,
    "homing": 20000,
    "lightning": 15000,
    "score_boost": 25000,
    "cryo": 15000,
    "orbit_drones": 15000,
    "gravity_well": 20000,
    "chain_reaction": 15000,
}
POWERUP_TIMER_KEYS = {
    "shield": "shield_until", "rapid_fire": "rapid_fire_until",
    "speed": "speed_boost_until", "triple_shot": "triple_shot_until",
    "laser": "laser_until", "magnet": "magnet_until", "bomb": "bomb_until",
    "bullet_time": "bullet_time_until", "piercing": "piercing_until",
    "homing": "homing_until", "lightning": "lightning_until",
    "score_boost": "score_boost_until",
    "cryo": "cryo_until", "orbit_drones": "orbit_until",
    "gravity_well": "gravity_until", "chain_reaction": "chain_reaction_until",
}
POWERUP_JOURNAL = (
    ("life", "Restores one life, up to five. A boss reward can revive an eliminated pilot with one life. Durability protects lives separately."),
    ("shield", "Blocks damage and destroys nearby enemy projectiles. Ramming destroys regular foes; bosses survive the ram."),
    ("rapid_fire", f"Normal shots and bombs fire about {RAPID_FIRE_MULTIPLIERS[0]:g}x faster solo, up to {RAPID_FIRE_MULTIPLIERS[-1]:g}x with four pilots; laser pulses are {(RAPID_FIRE_LASER_MULTIPLIER - 1):.0%} faster. Extra fire-rate bonuses add."),
    ("speed", "Boosts movement in every direction. Stacks with Bullet Time Momentum."),
    ("triple_shot", "Fires three parallel shots or piercing laser lanes. Bomb blasts do not stack on one foe; each laser pulse hits each boss once."),
    ("laser", "Hold fire for an upward piercing beam: 3 base damage per pulse. Triple Shot widens coverage; each boss takes one hit per pulse. Overrides bombs."),
    ("magnet", "Pulls dropped powerups toward your ship from anywhere on the screen."),
    ("bomb", f"Blasts one-shot unshielded regular foes within {BOMB_BLAST_RADIUS} pixels; bosses take 3 base damage. Shields block a hit. Triple-shot blasts hit each foe once."),
    ("bullet_time", f"A {BULLET_TIME_RADIUS}-pixel field keeps enemy shots at {BULLET_TIME_SLOWDOWN:.0%} speed, excluding lasers. Each distinct shot grants Momentum, max {BULLET_TIME_MAX_STACKS}. Buff expiry or life loss clears Momentum."),
    ("piercing", "Normal shots deal 2 base damage and can hit up to three different foes. Does not change bombs or lasers."),
    ("damage_up", f"Adds 1 damage to main shots and drones for this run, up to +{MAX_DAMAGE_BONUS}. Other support shots stay fixed. Extra pickups grant Double Score."),
    ("health_up", f"Adds one hit before losing a life, up to {MAX_DURABILITY_BONUS} upgrades. Repairs after {DURABILITY_REGEN_DELAY_MS // 1000}s without damage, then one hit every {DURABILITY_REGEN_INTERVAL_MS // 1000}s. Does not add lives; extras grant Double Score."),
    ("homing", "Normal shots and bombs steer toward foes; lasers add a weaker guided arc while keeping their main beam. Extends Lightning's reach."),
    ("lightning", f"Main shots, bombs and laser pulses arc for reduced damage. First hop needs a foe in range; later chances are {', '.join(f'{chance:.0%}' for chance in LIGHTNING_HOP_CHANCES[1:])}. Up to {1 + len(LIGHTNING_HOP_CHANCES)} foes total. Homing extends reach."),
    ("score_boost", "Doubles the score you earn from defeating enemies while active."),
    ("cryo", f"Hits slow regular foes 65% and bosses 25% for {CRYO_SLOW_MS // 1000}s. Kills grant Shatter: +{SHATTER_SPEED_PER_STACK:g} speed and +{SHATTER_FIRE_PER_STACK:.0%} fire per stack, max {SHATTER_MAX_STACKS}. Below full Momentum; bonuses do not add."),
    ("orbit_drones", f"Two helpers fire for {POWERUP_DURATIONS['orbit_drones'] // 1000}s. Shots match your weapon's base damage plus Damage Up, without blasts, heavy one-shot bonuses or fire-rate buffs."),
    ("supply_beacon", "Stores eight credited-kill charges. Ordinary kills get better drop odds; boss kills spend a charge too. Drop limits still apply."),
    ("gravity_well", f"A {POWERUP_DURATIONS['gravity_well'] // 1000}-second, {GRAVITY_FIELD_RADIUS}-pixel field gently bends nearby moving hostile shots away. Boss lasers stay fixed."),
    ("emergency_warp", "Stored across waves and saves. After Reflector blocks run out, a damaging hit spends the charge to warp you to a safer spot. Duplicates grant Double Score."),
    ("nova_pulse", f"After 3-2-1, every foe takes 1 damage through shields. Clears shots and mines within {NOVA_PULSE_RADIUS} pixels; boss lasers stay. Life loss cancels the charge."),
    ("missile_swarm", "Stores up to six guided missiles. Each one-shots an unshielded regular foe; bosses take 1 damage. Shields block a hit; weapon buffs do not multiply the swarm."),
    ("reflector", "Stores three blocks. Each damaging hit spends a block and returns a basic bolt toward the nearest foe."),
    ("chain_reaction", f"For {POWERUP_DURATIONS['chain_reaction'] // 1000} seconds, credited kills can send up to three shards at nearby visible foes. Support shots and Nova Pulse do not start bursts."),
)
JOURNAL_ENTRIES_PER_PAGE = 10


@ui_layout
def journal_page_count():
    per_page = journal_layout_metrics()["per_page"]
    return sum(math.ceil(len(entries) / per_page)
               for entries in (ENEMY_JOURNAL, ENEMY_MUTATIONS, POWERUP_JOURNAL))


# Limit random drops with a world-pickup cap and a shared cooldown.
NORMAL_POWERUP_DROP_CHANCE = 0.05
MUTATED_POWERUP_DROP_CHANCE = 0.10
MAX_WORLD_POWERUPS = 2
POWERUP_DROP_COOLDOWN_MS = 2700
_LAST_RANDOM_POWERUP_DROP_MS = -POWERUP_DROP_COOLDOWN_MS
ENEMY_SCORE_VALUES = {
    "standard": 100,
    "shooter": 150,
    "speedy": 140,
    "scout": 120,
    "striker": 210,
    "diver": 180,
    "weaver": 170,
    "sniper": 220,
    "bomber": 240,
    "tank": 300,
    "swarmer": 80,
    "lancer": 190,
    "bulwark": 380,
    "splitter": 210,
    "shardling": 35,
    "warden": 320,
    "artillery": 280,
    "volley": 220,
    "mine_layer": 260,
    "seeker": 230,
    "ricochet": 250,
    "prism": 270,
    "pulse": 240,
    "blink": 230,
    "charger": 250,
    "medic": 280,
    "orbit": 230,
    "scatterer": 250,
    "phantom": 260,
    "boss": 0,
}
ENEMY_TYPE_UNLOCK_ROUNDS = {
    "swarmer": 2,
    "speedy": 4,
    "scout": 6,
    "shooter": 8,
    "weaver": 12,
    "lancer": 16,
    "diver": 20,
    "striker": 26,
    "bomber": 32,
    "sniper": 40,
    "splitter": 32,
    "tank": 55,
    "warden": 58,
    "artillery": 72,
    "bulwark": 75,
    "volley": 24,
    "mine_layer": 29,
    "seeker": 34,
    "ricochet": 39,
    "prism": 44,
    "pulse": 49,
    "blink": 54,
    "charger": 59,
    "medic": 64,
    "orbit": 69,
    "scatterer": 74,
    "phantom": 79,
}
ENEMY_TYPE_SPAWN_WEIGHTS = {
    "swarmer": 6,
    "speedy": 4,
    "scout": 2,
    "shooter": 3,
    "weaver": 1.5,
    "lancer": 1.5,
    "diver": 1,
    "striker": 1.2,
    "bomber": 0.9,
    "sniper": 0.7,
    "tank": 0.8,
    "bulwark": 0.7,
    "splitter": 0.85,
    "warden": 0.7,
    "artillery": 0.7,
    "volley": 0.9,
    "mine_layer": 0.8,
    "seeker": 0.85,
    "ricochet": 0.8,
    "prism": 0.75,
    "pulse": 0.8,
    "blink": 0.85,
    "charger": 0.9,
    "medic": 0.7,
    "orbit": 0.85,
    "scatterer": 0.9,
    "phantom": 0.85,
}
ENEMY_SINGLE_SPAWN_TYPES = frozenset({
    "sniper", "tank", "bulwark", "warden", "artillery",
    "mine_layer", "prism", "pulse", "medic",
})
# Extra variety comes from different abilities, with limits on dangerous repeats.
ENEMY_WAVE_TYPE_CAPS = {
    "splitter": 2, "bomber": 2, "scatterer": 2, "seeker": 3,
    "ricochet": 3, "phantom": 3, "striker": 3, "diver": 4,
}
ENEMY_SLOW_HEALTH_RAMP_TYPES = frozenset({
    "swarmer", "speedy", "scout", "shardling",
    "volley", "mine_layer", "seeker", "ricochet", "prism", "pulse",
    "blink", "charger", "medic", "orbit", "scatterer", "phantom",
})
MUTATION_SCORE_MULTIPLIERS = {
    "armored": 1.5,
    "swift": 1.2,
    "volatile": 1.35,
}
def blend_color(first, second, amount):
    amount = max(0.0, min(1.0, amount))
    return tuple(round(a + (b - a) * amount) for a, b in zip(first, second))


def draw_soft_glow(screen, center, color, radius=18, strength=35):
    key = (tuple(color), radius, strength)
    glow = _GLOW_SPRITES.get(key)
    if glow is None:
        glow = pygame.Surface((radius * 2 + 2, radius * 2 + 2), pygame.SRCALPHA)
        for ring in range(radius, 0, -2):
            alpha = round(strength * (1 - ring / (radius + 1)) ** 1.5)
            pygame.draw.circle(glow, (*color, alpha), (radius + 1, radius + 1), ring)
        if len(_GLOW_SPRITES) > 1024:
            _GLOW_SPRITES.clear()
        _GLOW_SPRITES[key] = glow
    screen.blit(glow, (round(center[0]) - radius - 1, round(center[1]) - radius - 1))


def draw_space_background(screen, style="menu", now=None):
    """Cached nebula art plus a sparse animated star layer; no gameplay RNG."""
    width, height = screen.get_size()
    key = (width, height, style)
    entry = _SPACE_BACKGROUNDS.get(key)
    if entry is None:
        palettes = {
            "menu": ((5, 10, 29), (20, 10, 42), UI_CYAN, UI_PINK),
            "journal": ((5, 13, 31), (17, 13, 38), UI_CYAN, UI_VIOLET),
            "gameplay": ((3, 7, 20), (10, 10, 28), (39, 87, 123), (91, 48, 128)),
            "defeat": ((13, 8, 26), (33, 10, 31), UI_CORAL, UI_PINK),
            "victory": ((5, 14, 30), (15, 20, 37), UI_MINT, UI_GOLD),
        }
        top, bottom, first, second = palettes.get(style, palettes["menu"])
        background = pygame.Surface((width, height))
        for y in range(height):
            color = blend_color(top, bottom, y / max(1, height - 1))
            pygame.draw.line(background, color, (0, y), (width, y))

        nebula = pygame.Surface((128, 128), pygame.SRCALPHA)
        for color, center, size in (
            (first, (width * 0.13, height * 0.28), int(width * 0.58)),
            (second, (width * 0.88, height * 0.62), int(width * 0.70)),
        ):
            nebula.fill((0, 0, 0, 0))
            for radius in range(63, 0, -1):
                alpha = round((17 if style == "gameplay" else 28) * (1 - radius / 64) ** 1.5)
                pygame.draw.circle(nebula, (*color, alpha), (64, 64), radius)
            mist = pygame.transform.smoothscale(nebula, (size, size))
            background.blit(mist, (round(center[0] - size / 2), round(center[1] - size / 2)))

        if style != "gameplay":
            planet_center = (round(width * 0.88), round(height * 0.23))
            planet_radius = max(40, round(height * 0.13))
            pygame.draw.circle(background, blend_color(UI_BG, second, 0.07), planet_center, planet_radius)
            pygame.draw.circle(background, blend_color(UI_BG, first, 0.23), planet_center, planet_radius, 1)
            ring = pygame.Rect(0, 0, planet_radius * 3, planet_radius)
            ring.center = planet_center
            pygame.draw.ellipse(background, blend_color(UI_BG, second, 0.25), ring, 1)
            horizon = round(height * 0.80)
            grid_color = blend_color(UI_BG, first, 0.07)
            for column in range(-4, 9):
                pygame.draw.line(background, grid_color, (width // 2, horizon),
                                 (column * width // 4, height), 1)
            for fraction in (0.12, 0.28, 0.50, 0.80):
                y = round(horizon + (height - horizon) * fraction)
                pygame.draw.line(background, grid_color, (0, y), (width, y))

        rng = random.Random(2807)
        star_colors = (UI_CYAN, UI_VIOLET, UI_GOLD, UI_TEXT, UI_PINK)
        stars = tuple((rng.randrange(width), rng.randrange(height), rng.choice((1, 1, 1, 2)),
                       rng.choice(star_colors), rng.uniform(0, 6.28)) for _ in range(72))
        entry = (background, stars)
        if len(_SPACE_BACKGROUNDS) >= 12:
            _SPACE_BACKGROUNDS.clear()
        _SPACE_BACKGROUNDS[key] = entry
    background, stars = entry
    screen.blit(background, (0, 0))
    if now is None:
        now = pygame.time.get_ticks()
    for x, y, radius, color, phase in stars:
        brightness = (0.17 if style == "gameplay" else 0.25) + 0.12 * (1 + math.sin(now / 1600 + phase))
        star_color = blend_color(UI_BG, color, brightness)
        pygame.draw.circle(screen, star_color, (x, y), radius)
        if radius == 2 and style != "gameplay":
            pygame.draw.line(screen, star_color, (x - 3, y), (x + 3, y))


def draw_neon_panel(screen, rect, accent=UI_CYAN, fill=None, radius=12):
    rect = pygame.Rect(rect)
    if rect.width <= 0 or rect.height <= 0:
        return
    pygame.draw.rect(screen, blend_color(UI_BG, accent, 0.07), rect.inflate(6, 6),
                     border_radius=radius + 3)
    pygame.draw.rect(screen, fill or (10, 17, 35), rect, border_radius=radius)
    pygame.draw.rect(screen, blend_color(UI_BG, accent, 0.62), rect, 1, border_radius=radius)
    inset = min(15, rect.width // 5)
    if rect.width > inset * 2:
        pygame.draw.line(screen, accent, (rect.x + inset, rect.y),
                         (rect.x + min(rect.width - inset, max(40, rect.width // 3)), rect.y), 2)


def draw_neon_button(screen, rect, label, font, accent=UI_CYAN, enabled=True, selected=False):
    rect = pygame.Rect(rect)
    now = pygame.time.get_ticks()
    key = tuple(rect)
    state = _BUTTON_ANIMATIONS.get(key)
    if state is None:
        if len(_BUTTON_ANIMATIONS) >= 80:
            _BUTTON_ANIMATIONS.clear()
        state = {"hovered": False, "amount": 0.0, "at": now, "frame": _UI_FRAME}
        _BUTTON_ANIMATIONS[key] = state
    if state["frame"] < _UI_FRAME - 1:
        state["hovered"], state["amount"] = False, 0.0
    hovered = enabled and rect.collidepoint(get_ui_mouse_pos())
    just_clicked = _UI_PRESS is not None and now < _UI_PRESS[1] and rect.collidepoint(_UI_PRESS[0])
    if hovered and not state["hovered"] and not just_clicked and AUDIO_MANAGER is not None:
        AUDIO_MANAGER.play(AUDIO_MANAGER.ui_hover)
    elapsed = min(50, max(0, now - state["at"]))
    state["amount"] += ((1.0 if hovered else 0.0) - state["amount"]) * min(1.0, elapsed / 75)
    state["hovered"], state["at"] = hovered, now
    state["frame"] = _UI_FRAME
    amount = max(state["amount"], 0.65 if selected else 0.0) if enabled else 0.0
    pressed = enabled and just_clicked
    visual_rect = rect.move(0, 2) if pressed else rect.inflate(round(amount * 4), round(amount * 2))
    color = accent if enabled else (67, 82, 109)
    fill = blend_color((10, 19, 38), color, 0.35 if pressed else 0.07 + amount * 0.20)
    if amount > 0.05:
        draw_soft_glow(screen, visual_rect.midtop, color, radius=min(54, rect.width // 2),
                       strength=round(25 + amount * 35))
    draw_neon_panel(screen, visual_rect, color, fill=fill, radius=min(10, rect.height // 3))
    if amount > 0.1 or pressed:
        pygame.draw.rect(screen, color, visual_rect, 2, border_radius=min(10, rect.height // 3))
        sweep_width = max(8, round((rect.width - 24) * amount))
        pygame.draw.line(screen, color, (visual_rect.x + 12, visual_rect.bottom - 5),
                         (visual_rect.x + 12 + sweep_width, visual_rect.bottom - 5), 2)
    text = font.render(label, True, UI_TEXT if enabled else UI_MUTED)
    max_width, max_height = max(1, rect.width - 18), max(1, rect.height - 10)
    factor = min(1.0, max_width / max(1, text.get_width()), max_height / max(1, text.get_height()))
    if factor < 1:
        text = pygame.transform.smoothscale(text, (max(1, round(text.get_width() * factor)),
                                                   max(1, round(text.get_height() * factor))))
    screen.blit(text, text.get_rect(center=visual_rect.center))


def register_ui_click(position, accent=UI_CYAN):
    global _UI_PRESS
    now = pygame.time.get_ticks()
    _UI_PRESS = (position, now + 150)
    _UI_RIPPLES.append((position, now, accent))
    del _UI_RIPPLES[:-6]
    if AUDIO_MANAGER is not None:
        AUDIO_MANAGER.play(AUDIO_MANAGER.ui_click)


def draw_ui_feedback(screen):
    now = pygame.time.get_ticks()
    for effect in _UI_RIPPLES[:]:
        position, started, color = effect
        progress = (now - started) / 360
        if progress >= 1:
            _UI_RIPPLES.remove(effect)
            continue
        ripple = pygame.Surface((96, 96), pygame.SRCALPHA)
        alpha = round(150 * (1 - progress))
        radius = round(6 + progress * 36)
        pygame.draw.circle(ripple, (*color, alpha), (48, 48), radius, 2)
        pygame.draw.circle(ripple, (*UI_TEXT, alpha // 2), (48, 48), max(1, radius - 4), 1)
        screen.blit(ripple, (position[0] - 48, position[1] - 48))


def draw_neon_title(screen, text, font, center, accent=UI_CYAN):
    text_surface = font.render(text, True, UI_TEXT)
    max_width = screen.get_width() - 60
    if text_surface.get_width() > max_width:
        ratio = max_width / text_surface.get_width()
        text_surface = pygame.transform.smoothscale(text_surface,
            (max_width, max(1, round(text_surface.get_height() * ratio))))
    rect = text_surface.get_rect(center=center)
    shadow = text_surface.copy()
    shadow.fill((*accent, 255), special_flags=pygame.BLEND_RGBA_MULT)
    shadow.set_alpha(80)
    screen.blit(shadow, rect.move(-2, 2))
    screen.blit(shadow, rect.move(2, -1))
    screen.blit(text_surface, rect)
    line_width = min(rect.width // 2, 220)
    line_y = rect.bottom + 8
    pygame.draw.line(screen, accent, (rect.centerx - line_width, line_y), (rect.centerx - 8, line_y), 2)
    pygame.draw.line(screen, UI_PINK if accent == UI_CYAN else UI_CYAN,
                     (rect.centerx + 8, line_y), (rect.centerx + line_width, line_y), 2)


def create_tone_sound(frequency, duration_ms, volume=0.2):
    try:
        mixer_settings = pygame.mixer.get_init()
        sample_rate = mixer_settings[0] if mixer_settings else 22050
        channel_count = mixer_settings[2] if mixer_settings else 1
        total_samples = max(1, int(sample_rate * duration_ms / 1000))
        samples = array.array("h")
        for index in range(total_samples):
            t = index / sample_rate
            value = int(32767 * volume * math.sin(2 * math.pi * frequency * t))
            samples.extend([value] * channel_count)
        return pygame.mixer.Sound(buffer=samples.tobytes())
    except Exception:
        return None


def create_sweep_sound(start_frequency, end_frequency, duration_ms, volume=0.2):
    try:
        mixer_settings = pygame.mixer.get_init()
        sample_rate = mixer_settings[0] if mixer_settings else 22050
        channel_count = mixer_settings[2] if mixer_settings else 1
        duration_seconds = duration_ms / 1000
        total_samples = max(1, int(sample_rate * duration_seconds))
        samples = array.array("h")
        for index in range(total_samples):
            t = index / sample_rate
            progress = t / duration_seconds
            phase = 2 * math.pi * (
                start_frequency * t
                + (end_frequency - start_frequency) * t * t / (2 * duration_seconds)
            )
            envelope = min(1, progress * 12, (1 - progress) * 5)
            value = int(32767 * volume * envelope * math.sin(phase))
            samples.extend([value] * channel_count)
        return pygame.mixer.Sound(buffer=samples.tobytes())
    except Exception:
        return None


def create_noise_sound(duration_ms, volume=0.2):
    try:
        mixer_settings = pygame.mixer.get_init()
        sample_rate = mixer_settings[0] if mixer_settings else 22050
        channel_count = mixer_settings[2] if mixer_settings else 1
        total_samples = max(1, int(sample_rate * duration_ms / 1000))
        samples = array.array("h")
        for index in range(total_samples):
            envelope = 1 - index / total_samples
            value = int(32767 * volume * envelope * random.uniform(-1, 1))
            samples.extend([value] * channel_count)
        return pygame.mixer.Sound(buffer=samples.tobytes())
    except Exception:
        return None


INVASION_TEMPO_BPM = 160
INVASION_MUSIC_BARS = 8
INVASION_MUSIC_VOLUME = 0.44


def create_music_sound():
    """Original 160 BPM arcade assault loop: marching bass, chip riffs and drums."""
    try:
        mixer_settings = pygame.mixer.get_init()
        if mixer_settings is None:
            return None
        sample_rate, _, channel_count = mixer_settings
        samples_per_step = max(1, round(sample_rate * 60 / INVASION_TEMPO_BPM / 4))
        step_seconds = samples_per_step / sample_rate
        total_samples = samples_per_step * 16 * INVASION_MUSIC_BARS
        left = array.array("f", [0.0]) * total_samples
        right = array.array("f", [0.0]) * total_samples

        # Limited harmonics give the chips some bite without an unfiltered
        # square wave's piercing top end. No sustained ambient chord bed.
        table_size = 2048
        sine = tuple(math.sin(2 * math.pi * i / table_size) for i in range(table_size))
        waves = {
            "lead": tuple(
                (sine[i] + 0.34 * sine[(i * 3) % table_size]
                 + 0.18 * sine[(i * 5) % table_size]
                 + 0.10 * sine[(i * 7) % table_size]) / 1.62
                for i in range(table_size)
            ),
            "bass": tuple(
                (sine[i] + 0.43 * sine[(i * 3) % table_size]
                 + 0.16 * sine[(i * 5) % table_size]) / 1.59
                for i in range(table_size)
            ),
            "arp": tuple(
                (sine[i] + 0.30 * sine[(i * 2) % table_size]
                 + 0.15 * sine[(i * 4) % table_size]) / 1.45
                for i in range(table_size)
            ),
            "march": tuple((sine[i] + 0.5 * sine[(i * 2) % table_size]) / 1.5
                           for i in range(table_size)),
        }
        note_cache = {}

        def note_clip(voice, note, steps):
            key = (voice, note, steps)
            if key in note_cache:
                return note_cache[key]
            gate = steps * step_seconds
            attack, release = {
                "lead": (0.003, 0.025),
                "bass": (0.002, 0.022),
                "arp": (0.002, 0.018),
                "march": (0.002, 0.045),
            }[voice]
            frequency = 440 * 2 ** ((note - 69) / 12)
            phase_step = frequency * table_size / sample_rate
            wave = waves[voice]
            clip = array.array("f")
            for i in range(int((gate + release) * sample_rate)):
                t = i / sample_rate
                envelope = min(1.0, t / attack)
                if t > gate:
                    envelope *= max(0.0, 1 - (t - gate) / release)
                if voice in ("lead", "arp"):
                    envelope *= 0.72 + 0.28 * math.exp(-t * 16)
                if voice == "arp":
                    envelope *= math.exp(-t * 16)
                phase = i * phase_step
                value = wave[int(phase) % table_size]
                if voice == "march":
                    # Falling chirps make a four-step advancing-alien pulse.
                    value = wave[int(phase * (1.0 + 0.08 * math.exp(-t * 45))) % table_size]
                    envelope *= math.exp(-t * 13)
                clip.append(value * envelope)
            note_cache[key] = clip
            return clip

        def mix_clip(clip, start_step, gain, pan=0.0):
            start = round(start_step * samples_per_step) % total_samples
            left_gain = gain * (1 - max(0.0, pan))
            right_gain = gain * (1 + min(0.0, pan))
            # Wrap short note tails for continuous looping without a gap.
            for i, value in enumerate(clip):
                target = (start + i) % total_samples
                left[target] += value * left_gain
                right[target] += value * right_gain

        def play_note(voice, note, start, steps, gain, pan=0.0, echo=False):
            clip = note_clip(voice, note, steps)
            mix_clip(clip, start, gain, pan)
            if echo:
                mix_clip(clip, start + 2, gain * 0.14, 0.5)

        # E minor / Phrygian tension, with a chromatic B turnaround. The dry
        # repeated motif and marching quarter notes keep the battle moving.
        roots = (40, 40, 38, 38, 36, 36, 35, 35)
        chords = (
            (64, 67, 71, 76), (64, 65, 71, 76),
            (62, 65, 69, 74), (62, 65, 68, 74),
            (60, 64, 67, 72), (60, 64, 66, 72),
            (59, 63, 66, 71), (59, 63, 65, 71),
        )
        # (sixteenth-note position, MIDI pitch, held steps)
        melody = (
            ((0, 76, 1), (2, 76, 1), (3, 79, 1), (6, 77, 1), (8, 76, 1), (10, 71, 1), (12, 74, 1), (14, 75, 1)),
            ((0, 76, 1), (2, 79, 1), (4, 83, 2), (7, 82, 1), (8, 79, 1), (10, 77, 1), (12, 76, 1), (14, 71, 1)),
            ((0, 74, 1), (2, 74, 1), (3, 77, 1), (6, 76, 1), (8, 74, 1), (10, 69, 1), (12, 72, 1), (14, 73, 1)),
            ((0, 74, 1), (2, 77, 1), (4, 81, 2), (7, 80, 1), (8, 77, 1), (10, 76, 1), (12, 74, 1), (14, 69, 1)),
            ((0, 72, 1), (2, 72, 1), (3, 76, 1), (6, 75, 1), (8, 72, 1), (10, 67, 1), (12, 70, 1), (14, 71, 1)),
            ((0, 72, 1), (2, 76, 1), (4, 79, 2), (7, 78, 1), (8, 76, 1), (10, 74, 1), (12, 72, 1), (14, 67, 1)),
            ((0, 71, 1), (2, 71, 1), (3, 75, 1), (6, 74, 1), (8, 71, 1), (10, 66, 1), (12, 69, 1), (14, 70, 1)),
            ((0, 71, 1), (2, 74, 1), (4, 75, 1), (6, 78, 1), (8, 79, 1), (10, 78, 1), (12, 75, 1), (13, 74, 1), (14, 75, 1), (15, 76, 1)),
        )
        for bar, (root, chord, phrase) in enumerate(zip(roots, chords, melody)):
            start = bar * 16
            for step in range(0, 16, 2):
                offset = (0, 0, 12, 0, 0, 7, 12, 7)[step // 2]
                play_note("bass", root + offset, start + step, 1.25, 0.24)
            for beat, pitch in enumerate((root + 12, root + 10, root + 8, root + 7)):
                play_note("march", pitch, start + beat * 4, 0.9, 0.14)
            for step in (1, 3, 5, 7, 9, 11, 13, 15):
                pitch = chord[(step // 2 + bar) % 4]
                pan = -0.4 if step % 4 == 1 else 0.4
                play_note("arp", pitch, start + step, 0.45, 0.085, pan)
            for step, pitch, length in phrase:
                play_note("lead", pitch, start + step, length * 0.8, 0.16, -0.08, echo=True)

        # Use a local noise generator: building the soundtrack must not change
        # the random enemy, mutation, or powerup sequence.
        noise = random.Random(816)
        kick = array.array("f")
        for i in range(int(sample_rate * 0.19)):
            t = i / sample_rate
            phase = 2 * math.pi * (47 * t + 145 * (1 - math.exp(-t * 42)) / 42)
            envelope = min(1.0, t / 0.001) * math.exp(-t * 22)
            kick.append(math.sin(phase) * envelope)
        snare = array.array("f")
        previous_noise = 0.0
        for i in range(int(sample_rate * 0.13)):
            t = i / sample_rate
            raw = noise.uniform(-1, 1)
            air = (raw - previous_noise) * 0.5
            previous_noise = raw
            value = 0.70 * air * math.exp(-t * 35)
            value += 0.30 * math.sin(2 * math.pi * 195 * t) * math.exp(-t * 40)
            snare.append(value * min(1.0, t / 0.001))

        def hat_clip(seconds):
            clip = array.array("f")
            previous = 0.0
            for i in range(int(sample_rate * seconds)):
                t = i / sample_rate
                raw = noise.uniform(-1, 1)
                high = (raw - previous) * 0.5
                previous = raw
                envelope = min(1.0, t / 0.001) * math.exp(-t * 6 / seconds)
                clip.append(high * envelope)
            return clip

        closed_hat = hat_clip(0.035)
        open_hat = hat_clip(0.10)
        for bar in range(INVASION_MUSIC_BARS):
            start = bar * 16
            for step in (0, 4, 8, 12):
                mix_clip(kick, start + step, 0.34)
            if bar % 2:
                mix_clip(kick, start + 14, 0.20)
            for step in (4, 12):
                mix_clip(snare, start + step, 0.29, 0.08)
            for step in range(16):
                mix_clip(closed_hat, start + step,
                         0.065 if step % 2 else 0.095, -0.25)
            mix_clip(open_hat, start + 10, 0.08, 0.3)
            if bar in (3, 7):
                for step in (13, 14, 15):
                    mix_clip(snare, start + step, 0.10 + (step - 13) * 0.035, -0.15)

        peak = max(max(map(abs, left)), max(map(abs, right)), 0.001)
        # Leave headroom for sound effects; never boost a quiet mix into clipping.
        gain = min(1.0, 0.80 / peak)
        samples = array.array("h")
        for l_value, r_value in zip(left, right):
            if channel_count == 1:
                samples.append(round(32767 * (l_value + r_value) * 0.5 * gain))
            else:
                samples.extend((round(32767 * l_value * gain),
                                round(32767 * r_value * gain)))
                for _ in range(channel_count - 2):
                    samples.append(round(32767 * (l_value + r_value) * 0.5 * gain))
        return pygame.mixer.Sound(buffer=samples.tobytes())
    except Exception:
        return None

class AudioManager:
    def __init__(self):
        self.enabled = False
        self.shoot = None
        self.hit = None
        self.powerup = None
        self.ram = None
        self.explosion = None
        self.ui_hover = None
        self.ui_click = None
        self.music = None
        self.music_channel = None
        try:
            pygame.mixer.init()
            self.enabled = True
        except Exception:
            self.enabled = False

        if not self.enabled:
            return

        self.shoot = create_tone_sound(520, 45, 0.12)
        self.hit = create_tone_sound(180, 60, 0.18)
        self.powerup = create_tone_sound(740, 120, 0.15)
        self.ram = create_sweep_sound(310, 75, 150, 0.2)
        self.explosion = create_noise_sound(220, 0.16)
        self.ui_hover = create_sweep_sound(720, 980, 28, 0.055)
        self.ui_click = create_sweep_sound(1200, 620, 65, 0.10)
        self.music = create_music_sound()
        if self.music is not None:
            pygame.mixer.set_reserved(1)
            self.music_channel = pygame.mixer.Channel(0)
            self.music_channel.set_volume(INVASION_MUSIC_VOLUME)
            self.music_channel.play(self.music, loops=-1)

    def play(self, sound):
        if self.enabled and sound is not None:
            sound.play()


AUDIO_MANAGER = None


def ensure_audio_manager():
    global AUDIO_MANAGER
    if AUDIO_MANAGER is None:
        try:
            AUDIO_MANAGER = AudioManager()
        except Exception:
            AUDIO_MANAGER = None
    return AUDIO_MANAGER


def get_unlocked_boss_attacks(round_num):
    boss_wave_index = max(1, round_num // 5)
    boss_waves_after_first = boss_wave_index - 1
    unlocked_count = min(
           len(BOSS_ATTACKS),
           2 + boss_waves_after_first + (boss_waves_after_first // 2),
    )
    return tuple(BOSS_ATTACKS)[:unlocked_count]


def generate_pixel_sprite(art_matrix, color, width, height):
    rows, cols = len(art_matrix), max(len(line) for line in art_matrix)
    surf = pygame.Surface((cols, rows), pygame.SRCALPHA)
    base = tuple(color[:3])
    highlight = tuple(round(channel + (255 - channel) * 0.43) for channel in base)
    shadow = tuple(round(channel * 0.56) for channel in base)
    edge = tuple(round(channel * 0.77) for channel in base)
    core = tuple(round(channel + (255 - channel) * 0.82) for channel in base)
    for r, row in enumerate(art_matrix):
        for c, char in enumerate(row):
            if char == "X":
                above = r > 0 and c < len(art_matrix[r - 1]) and art_matrix[r - 1][c] == "X"
                if r == rows // 2 and c in (cols // 2 - 2, cols // 2 + 2):
                    pixel_color = core
                elif not above:
                    pixel_color = highlight
                elif r >= rows * 0.66:
                    pixel_color = shadow
                elif c in (0, cols - 1):
                    pixel_color = edge
                else:
                    pixel_color = base
                surf.set_at((c, r), pixel_color)
    return pygame.transform.scale(surf, (int(width), int(height)))


def generate_ship_animation(art_matrix, color, width, height, style="alien"):
    """Build shared pixel-art frames once; no external image files are needed."""
    key = (tuple(art_matrix), tuple(color), int(width), int(height), style)
    if key in _SHIP_ANIMATIONS:
        return _SHIP_ANIMATIONS[key]

    rows = len(art_matrix)
    cols = max(map(len, art_matrix))
    frames, hit_frames = [], []
    for frame_index, flex in enumerate((0, 1, 0, -1)):
        art = [list(row.ljust(cols)) for row in art_matrix]
        if style != "player":
            # Animate enemy limbs. Keep player wing tips stable instead of blinking.
            # Move antennae and legs, preserving the alien's recognizable hull.
            for row_index in (0, rows - 2, rows - 1):
                occupied = [c for c, pixel in enumerate(art[row_index]) if pixel == "X"]
                if not 1 < len(occupied) <= cols // 2:
                    continue
                art[row_index] = [" "] * cols
                for column in occupied:
                    direction = -1 if column < cols // 2 else 1 if column > cols // 2 else 0
                    target = max(0, min(cols - 1, column + direction * flex))
                    art[row_index][target] = "X"

        matrix = ["".join(row) for row in art]
        pixels = generate_pixel_sprite(matrix, color, cols, rows)
        light = blend_color(color, UI_TEXT, (0.40, 0.70, 0.95, 0.65)[frame_index])
        lights = ((cols // 2, 1), (cols // 2, 2)) if style == "player" else (
            (cols // 2 - 2, rows // 2), (cols // 2 + 2, rows // 2),
        )
        for x, y in lights:
            if 0 <= x < cols and 0 <= y < rows and art[y][x] == "X":
                pixels.set_at((x, y), light)
        frame = pygame.transform.scale(pixels, (int(width), int(height)))
        hit = frame.copy()
        hit.fill((165, 165, 165, 0), special_flags=pygame.BLEND_RGBA_ADD)
        frames.append(frame)
        hit_frames.append(hit)

    result = (tuple(frames), tuple(hit_frames))
    _SHIP_ANIMATIONS[key] = result
    return result


def attach_ship_animation(ship, art, color, width, height, style="alien"):
    ship["animation_frames"], ship["animation_hit_frames"] = generate_ship_animation(
        art, color, width, height, style,
    )
    ship["animation_style"] = style
    ship.setdefault("animation_tick", 0)
    # Deterministic phases keep the fleet lively without changing gameplay RNG.
    ship.setdefault("animation_phase", int(ship.get("x", 0) * 3 + ship.get("number", 0) * 19) % 120)
    ship.setdefault("animation_bank", 0.0)


def reset_player_animation(player):
    player["animation_bank"] = 0.0
    player["animation_fire"] = 0
    player["animation_hit"] = 0
    player["animation_spawn"] = 30
    player["move_dx"] = 0.0
    player["move_dy"] = 0.0


def animate_ship_fire(ship, offsets=(0,)):
    ship["animation_fire"] = 8
    ship["animation_muzzles"] = offsets


def update_ship_animations(players, enemies):
    """Advance only from the unpaused game loop, never from draw functions."""
    for player in players:
        if player["eliminated"] or player["respawn_until"]:
            continue
        player["animation_tick"] = player.get("animation_tick", 0) + 1
        target_bank = max(-14, min(14, -player.get("move_dx", 0) * 3))
        player["animation_bank"] += (target_bank - player["animation_bank"]) * 0.22
        for name in ("animation_fire", "animation_hit", "animation_spawn"):
            player[name] = max(0, player.get(name, 0) - 1)

    for enemy in enemies:
        enemy["animation_tick"] = enemy.get("animation_tick", 0) + 1
        center = enemy["rect"].center
        previous = enemy.get("animation_last_center", center)
        delta_x = center[0] - previous[0]
        if enemy["type"] == "blink" and abs(delta_x) > 70:
            enemy["animation_warp"] = 16
            enemy["animation_warp_origin"] = previous
            delta_x = 0
        enemy["animation_last_center"] = center
        limit = 2 if enemy["animation_style"] == "heavy" else 6
        target_bank = max(-limit, min(limit, delta_x * 1.5))
        bank = enemy.get("animation_bank", 0.0)
        enemy["animation_bank"] = bank + (target_bank - bank) * 0.18
        for name in ("animation_fire", "animation_hit", "animation_warp", "animation_support"):
            enemy[name] = max(0, enemy.get(name, 0) - 1)


def animated_ship_frame(ship, fallback):
    frames = ship.get("animation_frames")
    if not frames:
        return fallback
    style = ship.get("animation_style", "alien")
    interval = 6 if style in ("player", "fast") else 13 if style == "heavy" else 9
    index = ((ship.get("animation_tick", 0) + ship.get("animation_phase", 0)) // interval) % len(frames)
    if ship.get("animation_hit", 0) > 0:
        return ship["animation_hit_frames"][index]
    return frames[index]


def draw_animated_player(screen, player, now):
    frame = animated_ship_frame(player, player["sprite"])
    canvas = pygame.Surface((PLAYER_WIDTH + 64, PLAYER_HEIGHT + 88), pygame.SRCALPHA)
    body = frame.get_rect(center=canvas.get_rect().center)
    # The engine is an ANIMATED *central* thruster. No side flames or wing-tip
    # blinking: the side silhouette stays perfectly stable as the jet pulses.
    boosted = player["speed_boost_until"] > now
    tick = player.get("animation_tick", 0) + player.get("animation_phase", 0)
    # Two gentle harmonics give the thrust a smooth, non-repeating motion.
    pulse = (math.sin(tick * 0.37) + 0.5 * math.sin(tick * 0.71 + 0.8)) / 1.5
    flame_length = (19 if boosted else 12) + round((6 if boosted else 4) * pulse)
    flame_length = max(7, flame_length)  # Keep the jet visible every frame.
    x, y = body.centerx, body.bottom - 2
    engine_color = blend_color(player["color"], UI_CYAN, 0.45) if boosted else player["color"]
    # Outer glow, bright core, and an inner hot jet all stay on the centerline.
    pygame.draw.polygon(canvas, (*engine_color, 105), (
        (x - 5, y), (x, y + flame_length + 4), (x + 5, y),
    ))
    pygame.draw.polygon(canvas, engine_color, (
        (x - 3, y), (x, y + flame_length), (x + 3, y),
    ))
    hot_color = blend_color(engine_color, UI_TEXT, 0.74)
    pygame.draw.polygon(canvas, hot_color, (
        (x - 1, y + 1), (x, y + max(3, round(flame_length * 0.62))),
        (x + 1, y + 1),
    ))
    # One moving ember directly beneath the jet adds visible travel animation.
    ember_y = y + 3 + (tick * 2 % max(6, flame_length))
    pygame.draw.circle(canvas, engine_color, (x, ember_y), 1)

    recoil = round(2 * player.get("animation_fire", 0) / 8)
    canvas.blit(frame, body.move(0, recoil))
    if player.get("animation_fire", 0):
        flash_size = 2 + player["animation_fire"] // 2
        for offset in player.get("animation_muzzles", (0,)):
            x, y = body.centerx + offset, body.top
            pygame.draw.polygon(canvas, player["color"], (
                (x, y - flash_size * 2), (x + flash_size, y),
                (x, y + 2), (x - flash_size, y),
            ))
            pygame.draw.line(canvas, UI_TEXT, (x, y - flash_size), (x, y + 1), 2)

    spawn = player.get("animation_spawn", 0)
    if spawn:
        canvas.set_alpha(255 - spawn * 4)
        scan_y = body.top + round((1 - spawn / 30) * body.height)
        pygame.draw.line(canvas, UI_TEXT, (body.left - 4, scan_y), (body.right + 4, scan_y), 2)
    if player.get("animation_hit", 0):
        pygame.draw.circle(canvas, UI_CYAN, body.center, 23 + player["animation_hit"], 2)
    canvas = pygame.transform.rotate(canvas, round(player.get("animation_bank", 0)))
    center = (round(player["x"] + PLAYER_WIDTH / 2), round(player["y"] + PLAYER_HEIGHT / 2))
    draw_soft_glow(screen, center, player["color"], radius=24, strength=50)
    screen.blit(canvas, canvas.get_rect(center=center))
    if spawn:
        pygame.draw.circle(screen, player["color"], center, 18 + spawn, 1)


def draw_animated_enemy(screen, enemy):
    rect = enemy["rect"]
    tick = enemy.get("animation_tick", 0) + enemy.get("animation_phase", 0)
    pulse = (1 + math.sin(tick / 9)) / 2
    draw_soft_glow(screen, rect.center, enemy["color"],
                   radius=26 if enemy.get("is_boss") else 18, strength=25 + round(pulse * 3) * 5)
    frame = animated_ship_frame(enemy, enemy["surface"])
    frame = pygame.transform.rotate(frame, round(enemy.get("animation_bank", 0)))
    if enemy["type"] == "phantom":
        frame.set_alpha(130 + round(pulse * 125))
    recoil = round(2 * enemy.get("animation_fire", 0) / 8)
    screen.blit(frame, frame.get_rect(center=(rect.centerx, rect.centery - recoil)))

    if enemy.get("animation_style") == "fast":
        length = 4 + (tick // 3) % 5
        pygame.draw.line(screen, enemy["color"], (rect.centerx, rect.top),
                         (rect.centerx, rect.top - length), 2)
    if enemy.get("animation_fire", 0):
        radius = 2 + enemy["animation_fire"] // 2
        center = (rect.centerx, rect.bottom + 2)
        pygame.draw.circle(screen, enemy["color"], center, radius + 2, 1)
        pygame.draw.circle(screen, UI_TEXT, center, max(1, radius // 2))
    if enemy.get("is_boss") and not enemy.get("attack_queue"):
        charge = max(0, 1 - enemy.get("attack_cooldown", 30) / 30)
        if charge:
            radius = 3 + round(charge * rect.width / 5)
            pygame.draw.circle(screen, blend_color(enemy["color"], UI_TEXT, pulse), rect.center, radius, 2)
    support = enemy.get("animation_support", 0)
    if support:
        pygame.draw.circle(screen, enemy["color"], rect.center, 12 + (24 - support) * 3, 1)
    warp = enemy.get("animation_warp", 0)
    if warp:
        for center in (rect.center, enemy.get("animation_warp_origin", rect.center)):
            pygame.draw.circle(screen, UI_CYAN, center, 6 + (16 - warp) * 2, 2)
    if enemy.get("milestone_kind"):
        draw_milestone_boss_hull(screen, enemy, tick)


def draw_milestone_boss_hull(screen, enemy, tick):
    """Distinct landmark hulls use a bounded number of pure geometric accents."""
    rect = enemy["rect"]
    x, y = rect.center
    color = enemy["color"]
    pulse = (1 + math.sin(tick / 11)) / 2
    light = blend_color(color, UI_TEXT, .32 + pulse * .34)
    core = max(5, rect.height // 10)
    kind = enemy["milestone_kind"]
    if kind == "bulwark":
        # Four armor pylons flank a furnace aperture; no shield/invulnerability.
        for side in (-1, 1):
            for level in (-1, 1):
                anchor = (x + side * (rect.width // 2 - 6), y + level * rect.height // 4)
                end = (anchor[0] + side * 9, anchor[1] + level * 5)
                pygame.draw.line(screen, color, anchor, end, 3)
                pygame.draw.circle(screen, light, end, 3)
        aperture = pygame.Rect(x - core, y - core, core * 2, core * 2)
        pygame.draw.rect(screen, UI_BG, aperture.inflate(5, 5), border_radius=3)
        pygame.draw.rect(screen, light, aperture, 2, border_radius=2)
        pygame.draw.line(screen, light, (x - core + 3, y), (x + core - 3, y), 2)
    elif kind == "helix":
        # Two opposed, counter-rotating strands give this organic hull its name.
        ellipse = rect.inflate(16, 8)
        pygame.draw.ellipse(screen, blend_color(color, UI_BG, .35), ellipse, 1)
        for index in range(4):
            angle = tick / 38 * (1 if index % 2 == 0 else -1) + index * math.pi / 2
            node = (round(x + math.cos(angle) * ellipse.width / 2),
                    round(y + math.sin(angle) * ellipse.height / 2))
            pygame.draw.circle(screen, light if index % 2 else color, node, 3)
        pygame.draw.circle(screen, UI_BG, (x, y), core + 3)
        pygame.draw.circle(screen, light, (x, y), core, 2)
    elif kind == "tempest":
        # Angular turbine fins and short charged traces stay close to the hull.
        for side in (-1, 1):
            points = [(x + side * rect.width // 4, y - rect.height // 5),
                      (x + side * (rect.width // 2 + 8), y),
                      (x + side * (rect.width // 2 - 4), y + 5),
                      (x + side * (rect.width // 2 + 3), y + rect.height // 4)]
            pygame.draw.lines(screen, light, False, points, 2)
        diamond = ((x, y - core - 3), (x + core, y),
                   (x, y + core + 3), (x - core, y))
        pygame.draw.polygon(screen, UI_BG, diamond)
        pygame.draw.polygon(screen, light, diamond, 2)
    elif kind == "eclipse":
        # A broken orbital crown surrounds a dark, pulsating central eclipse.
        crown = pygame.Rect(0, 0, rect.width - 12, rect.height + 22)
        crown.center = rect.center
        angle = tick / 90
        for index in range(3):
            start = angle + index * math.tau / 3
            pygame.draw.arc(screen, light, crown, start, start + 1.5, 2)
            node = (round(x + math.cos(start) * crown.width / 2),
                    round(y - math.sin(start) * crown.height / 2))
            pygame.draw.circle(screen, color, node, 3)
        pygame.draw.circle(screen, UI_BG, (x, y), core + 5)
        pygame.draw.circle(screen, light, (x, y), core + 5, 2)
        pygame.draw.circle(screen, color, (x, y), core + 9, 1)


def enemy_animation_style(enemy_type):
    if enemy_type in ("tank", "bulwark", "artillery", "bomber", "boss", "pulse"):
        return "heavy"
    if enemy_type in ("speedy", "scout", "swarmer", "diver", "charger", "seeker", "shardling"):
        return "fast"
    return "alien"


def create_enemy_journal_sprites():
    journal_sprites = {}
    for name, _ in ENEMY_JOURNAL:
        enemy_type = name.lower().replace(" ", "_")
        if enemy_type == "boss":
            colors = (BOSS_ATTACKS[attack][0] for attack in ("fan", "spiral", "curtain"))
            variations = [{"color": color, "art": BOSS_ART} for color in colors]
        else:
            variations = VISUAL_VARIATIONS[enemy_type]
        journal_sprites[name] = tuple(
            generate_ship_animation(variation["art"], variation["color"], 32, 24,
                                    enemy_animation_style(enemy_type))[0]
            for variation in variations
        )
    return journal_sprites


def create_bunkers():
    bunkers = []
    num_bunkers = 4
    bunker_width = len(BUNKER_SHAPE[0]) * BLOCK_SIZE
    spacing = (SCREEN_WIDTH - (num_bunkers * bunker_width)) // (num_bunkers + 1)
    bunker_y = SCREEN_HEIGHT - 160

    for i in range(num_bunkers):
        start_x = spacing + i * (bunker_width + spacing)
        for r, row in enumerate(BUNKER_SHAPE):
            for c, char in enumerate(row):
                if char == "X":
                    block_rect = pygame.Rect(
                        start_x + c * BLOCK_SIZE,
                        bunker_y + r * BLOCK_SIZE,
                        BLOCK_SIZE,
                        BLOCK_SIZE,
                    )
                    bunkers.append(block_rect)
    return bunkers


def check_bunker_collisions(bunkers, player_bullets, enemy_bullets, enemies, particles):
    # Player bullets colliding with bunker blocks
    for bullet in player_bullets[:]:
        # Lasers pass through friendly cover without being consumed or tearing
        # the bunker apart. Otherwise the full-screen beam vanishes instantly.
        if isinstance(bullet, dict) and bullet.get("type") == "laser":
            continue
        bullet_rect = bullet["rect"] if isinstance(bullet, dict) else bullet
        for block in bunkers[:]:
            if bullet_rect.colliderect(block):
                spawn_pop_particles(
                    bullet_rect.centerx, bullet_rect.centery,
                    player_projectile_color(bullet), particles,
                )
                bunkers.remove(block)
                if isinstance(bullet, dict):
                    if bullet in player_bullets:
                        player_bullets.remove(bullet)
                elif bullet in player_bullets:
                    player_bullets.remove(bullet)
                break

    # Enemy bullets colliding with bunker blocks
    for bullet in enemy_bullets[:]:
        # Telegraphs are harmless until the beam becomes active.
        if bullet.get("laser_state") == "warning":
            continue
        bullet_rect = bullet["rect"]
        for block in bunkers[:]:
            if bullet_rect.colliderect(block):
                spawn_pop_particles(block.centerx, block.centery, bullet["color"], particles)
                bunkers.remove(block)
                if bullet in enemy_bullets:
                    enemy_bullets.remove(bullet)
                break

    # Enemies destroying bunker blocks on physical contact
    for enemy in enemies:
        for block in bunkers[:]:
            if enemy["rect"].colliderect(block):
                bunkers.remove(block)

# --- Pop Particle System ---
MAX_EFFECT_PARTICLES = 512
def player_projectile_color(bullet, player_colors=None):
    """Match impact sparks to the color used to render the player shot."""
    if not isinstance(bullet, dict):
        return UI_MINT  # Legacy pygame.Rect shots use the default mint tint.
    if bullet.get("color") is not None:
        return bullet["color"]
    owner = bullet.get("owner")
    if player_colors and owner in player_colors:
        return player_colors[owner]
    if isinstance(owner, int) and 1 <= owner <= len(PLAYER_COLORS):
        return PLAYER_COLORS[owner - 1]
    return UI_MINT


def spawn_pop_particles(x, y, color, particles):
    for _ in range(16):
        radius = random.uniform(2, 5)
        lifetime = random.randint(14, 26)
        particle = {
            "x": x,
            "y": y,
            "dx": random.uniform(-4.5, 4.5),
            "dy": random.uniform(-4.5, 4.5),
            "radius": radius,
            "color": color,
            "lifetime": lifetime,
            "max_lifetime": lifetime,
        }
        # Keep cosmetic randomness independent of the available draw budget:
        # a crowded explosion should not change subsequent gameplay rolls.
        if len(particles) < MAX_EFFECT_PARTICLES:
            particles.append(particle)
    ring = {
        "kind": "ring",
        "x": x,
        "y": y,
        "dx": 0,
        "dy": 0,
        "radius": 7,
        "color": color,
        "lifetime": 18,
        "max_lifetime": 18,
    }
    if len(particles) < MAX_EFFECT_PARTICLES:
        particles.append(ring)


def update_and_draw_particles(screen, particles, advance=True):
    if advance and len(particles) > MAX_EFFECT_PARTICLES:
        # Preserve distinctive feedback before generic impact sparks.
        important = [p for p in particles if p.get("kind") not in (None, "ring")]
        generic = [p for p in particles if p.get("kind") in (None, "ring")]
        available = max(0, MAX_EFFECT_PARTICLES - len(important))
        particles[:] = (generic[-available:] if available else []) + important[-MAX_EFFECT_PARTICLES:]
    for p in particles[:]:
        if advance:
            p["x"] += p["dx"]
            p["y"] += p["dy"]
            p["lifetime"] -= 1

        if advance and p["lifetime"] <= 0:
            particles.remove(p)
            continue
        if p.get("kind") == "lightning_arc":
            pygame.draw.lines(screen, p["color"], False, p["points"], 4)
            pygame.draw.lines(screen, UI_TEXT, False, p["points"], 1)
        elif p.get("kind") == "momentum":
            alpha = p["lifetime"] / p["max_lifetime"]
            x, y = int(p["x"]), int(p["y"])
            pygame.draw.line(screen, p["color"],
                             (x - round(p["dx"] * 0.7), y - round(p["dy"] * 0.7)),
                             (x, y), max(1, round(3 * alpha)))
            pygame.draw.circle(screen, UI_TEXT, (x, y), max(1, round(2 * alpha)))
        elif p.get("kind") in ("powerup_pickup", "shatter"):
            draw_powerup_collection_particle(screen, p)
        elif p.get("kind") == "nova_pulse":
            progress = 1 - p["lifetime"] / p["max_lifetime"]
            radius = max(1, round(p["radius"] * min(1, progress * 1.6)))
            size = int(p["radius"] * 2 + 8)
            pulse = pygame.Surface((size, size), pygame.SRCALPHA)
            center = (size // 2, size // 2)
            alpha = round(190 * (1 - progress))
            pygame.draw.circle(pulse, (*p["color"], alpha), center, radius, 3)
            pygame.draw.circle(pulse, (*UI_TEXT, alpha // 2), center, max(1, radius - 9), 1)
            screen.blit(pulse, (round(p["x"]) - center[0], round(p["y"]) - center[1]))
        elif p.get("kind") == "ring":
            progress = 1 - p["lifetime"] / p["max_lifetime"]
            ring_radius = int(p["radius"] + progress * 28)
            pygame.draw.circle(
                screen,
                p["color"],
                (int(p["x"]), int(p["y"])),
                ring_radius,
                2,
            )
        else:
            current_radius = int(p["radius"] * (p["lifetime"] / p["max_lifetime"]))
            if current_radius > 0:
                pygame.draw.circle(screen, p["color"], (int(p["x"]), int(p["y"])), current_radius)


def create_bosses(round_num):
    enemies = []
    milestone = milestone_boss_profile(round_num)
    # Every encounter has one opponent, including the four unique guardians.
    boss_count = 1
    progress = boss_difficulty_progress(round_num)
    tier = enemy_health_tier(round_num)
    solo_boss_hp = round((140 + 210 * progress + 40 * progress ** 2) * 1.12)
    # Infinite mode keeps growing after the campaign without raising the
    # projectile ceiling or shortening the laser's reaction window.
    solo_boss_hp += round(2.5 * max(0, round_num - MAX_CAMPAIGN_ROUND))
    hp_per_boss = scale_enemy_health(round(solo_boss_hp * (0.61 if boss_count > 1 else 1.0)))
    if milestone is not None:
        hp_per_boss = round(hp_per_boss * milestone["hp_multiplier"])

    scale_multiplier = 2.5 if boss_count == 1 else 1.8
    b_width = int(ENEMY_WIDTH * scale_multiplier)
    b_height = int(ENEMY_HEIGHT * scale_multiplier)
    if milestone is not None:
        b_width, b_height = milestone["size"]

    spacing = SCREEN_WIDTH // (boss_count + 1)
    attack_level = max(1, round_num // 5)
    unlocked_patterns = get_unlocked_boss_attacks(round_num)
    # Smooth growth across the campaign, with breathing room between patterns.
    attack_delay = round(140 - 38 * progress)
    if boss_count > 1:
        attack_delay = round(attack_delay * 1.25)
    if round_num > MAX_CAMPAIGN_ROUND:
        attack_delay = max(90, attack_delay - (round_num - MAX_CAMPAIGN_ROUND) // 20)

    for i in range(boss_count):
        x = spacing * (i + 1) - (b_width // 2)
        y = OFFSET_Y + 30

        attack_pattern = random.choices(
            unlocked_patterns,
            weights=[BOSS_ATTACKS[pattern][1] for pattern in unlocked_patterns],
            k=1,
        )[0]
        boss_color = milestone["color"] if milestone is not None else BOSS_ATTACKS[attack_pattern][0]
        boss_art = milestone["art"] if milestone is not None else BOSS_ART
        sprite = generate_pixel_sprite(boss_art, boss_color, b_width, b_height)

        boss_data = {
            "type": "boss",
            "is_boss": True,
            "color": boss_color,
            "can_shoot": True,
            "is_speedy": True,  # Uses speedy movement logic
            "attack_pattern": attack_pattern,
            "attack_patterns": unlocked_patterns,
            "attack_level": attack_level,
            "difficulty_progress": progress,
            "health_tier": tier,
            "last_attack_pattern": None,
            "cross_lane_phase": 0,
            "attack_delay": attack_delay,
            "attack_queue": [],
            "attack_cooldown": attack_delay + i * BOSS_ENCOUNTER_RECOVERY_FRAMES,
            "rect": pygame.Rect(int(x), int(y), b_width, b_height),
            "x": float(x),
            "surface": sprite,
            "dx": 1 if i % 2 == 0 else -1,
            "hp": hp_per_boss,
            "max_hp": hp_per_boss,
            "speed_mult": 1.5,
        }
        if milestone is not None:
            boss_data.update(milestone_kind=milestone["kind"], boss_name=milestone["name"],
                             boss_subtitle=milestone["subtitle"], milestone_wave=round_num,
                             signature_index=0, signature_warning=None)
        attach_ship_animation(boss_data, boss_art, boss_color, b_width, b_height, "heavy")
        enemies.append(boss_data)

    return enemies


def plan_enemy_wave(round_num, slots, unlocked_types, special_chance, wave_index):
    """Use a fixed special-enemy budget and rotate featured unlocked types."""
    if not unlocked_types or not slots:
        return {}
    budget = min(len(slots), max(1, round(len(slots) * special_chance)))
    previous_round = round_num - (2 if (round_num - 1) % 5 == 0 else 1)
    featured = [kind for kind in unlocked_types
                if previous_round < ENEMY_TYPE_UNLOCK_ROUNDS[kind] <= round_num]
    ordered_types = sorted(unlocked_types, key=lambda kind: (ENEMY_TYPE_UNLOCK_ROUNDS[kind], kind))
    featured_count = min(len(ordered_types), 1 + round_num // 20, 4)
    start = wave_index * max(1, featured_count - 1) % len(ordered_types)
    for offset in range(len(ordered_types)):
        if len(featured) >= featured_count:
            break
        kind = ordered_types[(start + offset) % len(ordered_types)]
        if kind not in featured:
            featured.append(kind)

    roster, counts = [], {}

    def type_limit(kind):
        if kind in ENEMY_SINGLE_SPAWN_TYPES:
            return 1
        return ENEMY_WAVE_TYPE_CAPS.get(kind, budget)

    def add_type(kind):
        # Swarmers still arrive in groups, each counted against the wave budget.
        amount = min(random.randint(2, 4), budget - len(roster)) if kind == "swarmer" else 1
        amount = min(amount, type_limit(kind) - counts.get(kind, 0))
        roster.extend([kind] * amount)
        counts[kind] = counts.get(kind, 0) + amount

    # Reserve a slot for every featured type before filling random groups.
    for kind in featured[:budget]:
        roster.append(kind)
        counts[kind] = counts.get(kind, 0) + 1
    while len(roster) < budget:
        available = [kind for kind in unlocked_types if counts.get(kind, 0) < type_limit(kind)]
        if not available:
            break
        kind = random.choices(available, weights=[
            ENEMY_TYPE_SPAWN_WEIGHTS[kind] / (1 + counts.get(kind, 0) * 0.65)
            for kind in available
        ], k=1)[0]
        add_type(kind)

    assignments = {}
    free_slots = set(slots)
    bottom_row = max(row for row, _ in slots)
    last_slot = None
    for index, kind in enumerate(roster):
        # Introduce featured abilities near the visible front of the formation.
        choices = sorted(slot for slot in free_slots if index < len(featured) and slot[0] >= bottom_row - 1)
        if not choices:
            choices = sorted(free_slots)
        if kind == "swarmer" and last_slot is not None and index > 0 and roster[index - 1] == "swarmer":
            row, column = last_slot
            neighbors = [slot for slot in choices if slot[0] == row and abs(slot[1] - column) == 1]
            if neighbors:
                choices = neighbors
        last_slot = random.choice(choices)
        assignments[last_slot] = kind
        free_slots.remove(last_slot)
    return assignments


def sector_for_round(round_num):
    """Checkpoint sectors: waves 1-5, 6-10, 11-15, etc."""
    return (max(1, int(round_num)) - 1) // WAVES_PER_SECTOR + 1


def sector_start_round(round_num):
    """Earliest wave to replay after defeat (the first wave of this sector)."""
    return (sector_for_round(round_num) - 1) * WAVES_PER_SECTOR + 1


def enemy_health_tier(round_num):
    """Base health through wave 50, then one permanent increase from wave 51."""
    return 2 if int(round_num) >= ENEMY_HEALTH_INCREASE_WAVE else 1


def enemy_combat_tier(round_num):
    """Keep existing firing and aiming progression separate from health."""
    return (max(1, int(round_num)) - 1) // WAVES_PER_COMBAT_TIER + 1


def health_tier_bonus(enemy_type, round_num):
    """Non-fragile types receive at most one health-tier bonus, after wave 50."""
    if enemy_type in HEALTH_SCALING_EXEMPT_TYPES:
        return 0
    return enemy_health_tier(round_num) - 1


def scale_enemy_health(base_hp):
    """Reduce generated enemy health once, retaining at least one whole hit point."""
    return max(1, round(base_hp * ENEMY_HEALTH_MULTIPLIER))


def create_enemies(round_num, infinite_mode=False):
    # Trigger Boss Wave every 5 rounds
    if round_num % 5 == 0:
        return create_bosses(round_num)

    enemies = []

    curr_w = int(ENEMY_WIDTH)
    curr_h = int(ENEMY_HEIGHT)

    additional_rows = min(6, max(0, (round_num - 1) // 5))
    side_columns = min(4, max(0, (round_num - 1) // 15))
    if infinite_mode and round_num > MAX_CAMPAIGN_ROUND:
        additional_rows += (round_num - MAX_CAMPAIGN_ROUND) // 5
        side_columns = min(
            8,
            side_columns + (round_num - MAX_CAMPAIGN_ROUND) // 15,
        )
    row_count = ROWS + additional_rows
    row_offset_y = OFFSET_Y - additional_rows * (curr_h + PADDING)
    col_count = COLS + side_columns * 2
    formations = ("grid", "staggered", "v", "diamond", "wedge", "pairs")
    non_boss_wave = round_num - 1 - ((round_num - 1) // 5)
    formation = formations[non_boss_wave % len(formations)]
    special_chance = min(0.38, 0.20 + max(0, round_num - 2) * 0.0018)
    if infinite_mode and round_num > MAX_CAMPAIGN_ROUND:
        special_chance = min(
            0.60,
            special_chance + (round_num - MAX_CAMPAIGN_ROUND) * 0.001,
        )
    mutation_chance = min(0.05, (round_num - 1) * 0.0025)
    # Leave lateral travel room even on smaller displays and endless-mode waves.
    formation_overhang = min(row_count - 1, 10) * 16 if formation == "v" else 0
    if formation == "staggered":
        formation_overhang = (curr_w + PADDING) // 2
    available_width = SCREEN_WIDTH - 2 * MARGIN - 80 - formation_overhang
    max_columns = max(1, int((available_width + PADDING) // (curr_w + PADDING)))
    col_count = min(col_count, max_columns)
    center_col = (col_count - 1) / 2
    center_row = (row_count - 1) / 2

    def is_valid_formation_slot(row, col):
        if formation == "diamond":
            row_width = col_count * (1 - abs(row - center_row) / (center_row + 1))
            return abs(col - center_col) <= row_width / 2
        if formation == "wedge":
            half_width = min(col_count / 2, (row + 1) * 1.8)
            return abs(col - center_col) <= half_width
        if formation == "pairs":
            return col % 4 not in (2, 3)
        return True

    unlocked_types = tuple(
        enemy_type
        for enemy_type, unlock_round in ENEMY_TYPE_UNLOCK_ROUNDS.items()
        if round_num >= unlock_round
    )
    slots = [(row, col) for row in range(row_count) for col in range(col_count)
             if is_valid_formation_slot(row, col)]
    planned_types = plan_enemy_wave(round_num, slots, unlocked_types, special_chance, non_boss_wave)

    for row in range(row_count):
        for col in range(col_count):
            if not is_valid_formation_slot(row, col):
                continue

            x = (SCREEN_WIDTH - curr_w) / 2 + (col - center_col) * (curr_w + PADDING)
            y = row_offset_y + row * (curr_h + PADDING)
            if formation == "staggered" and row % 2:
                x += (curr_w + PADDING) / 2
            elif formation == "v":
                if col < center_col:
                    x -= min(row, 10) * 8
                elif col > center_col:
                    x += min(row, 10) * 8

            type_key = planned_types.get((row, col), "standard")

            mutation = (
                random.choice(tuple(MUTATION_COLORS))
                if random.random() < mutation_chance else None
            )
            visual = random.choice(VISUAL_VARIATIONS[type_key])
            is_speedy = type_key in (
                "speedy", "diver", "scout", "swarmer", "blink", "charger",
            ) or mutation == "swift"
            enemy_hp = (
                4 if type_key == "bulwark" else
                3 if type_key == "tank" else
                2 if type_key in ("splitter", "warden", "artillery") else
                2 if mutation == "armored" else 1
            )
            # Once after wave 50, sturdy enemies gain HP, but nimble/fragile
            # archetypes remain quick kills even in late sectors.
            enemy_hp += health_tier_bonus(type_key, round_num)
            enemy_hp = scale_enemy_health(enemy_hp)
            enemy_scale = (
                1.3 if type_key == "bulwark" else
                1.2 if type_key == "tank" else
                1.15 if type_key == "artillery" else
                0.75 if type_key == "swarmer" else
                0.85 if type_key == "scout" else 1
            )
            enemy_width = int(curr_w * enemy_scale)
            enemy_height = int(curr_h * enemy_scale)
            x += (curr_w - enemy_width) / 2
            sprite = generate_pixel_sprite(visual["art"], visual["color"], enemy_width, enemy_height)

            enemy_data = {
                "type": type_key,
                "is_boss": False,
                "formation": formation,
                "mutation": mutation,
                "color": visual["color"],
                "can_shoot": type_key in (
                    "shooter", "sniper", "bomber", "striker", "lancer", "bulwark", "artillery",
                    "volley", "mine_layer", "seeker", "ricochet", "prism", "pulse",
                    "charger", "scatterer", "phantom",
                ),
                "is_speedy": is_speedy,
                "rect": pygame.Rect(int(x), int(y), enemy_width, enemy_height),
                "x": float(x),
                "surface": sprite,
                "dx": 1,
                "hp": enemy_hp,
                "max_hp": enemy_hp,
                "shield_charges": 0,
                "speed_mult": (
                    1.2 if type_key == "swarmer" else
                    3.1 if type_key == "diver" else
                    2.8 if type_key == "scout" or mutation == "swift" else
                    1.8
                ),
                "blink_timer": 0,
                "support_timer": 0,
                "weave_phase": (row + col) * math.pi / 3,
                "weave_y_phase": random.uniform(0, 2 * math.pi),
                "weave_y_amplitude": random.uniform(26, 46),
                "weave_y_rate": random.uniform(0.025, 0.045),
                "weave_origin_y": float(y),
                "dive_phase": 0.0,
                "dive_origin_y": float(y),
            }
            attach_ship_animation(enemy_data, visual["art"], visual["color"],
                                  enemy_width, enemy_height, enemy_animation_style(type_key))
            enemies.append(enemy_data)

    wardens = [enemy for enemy in enemies if enemy["type"] == "warden"]
    for warden in wardens:
        for enemy in enemies:
            if enemy is warden:
                continue
            distance = math.hypot(
                enemy["rect"].centerx - warden["rect"].centerx,
                enemy["rect"].centery - warden["rect"].centery,
            )
            if distance <= (ENEMY_WIDTH + PADDING) * 2:
                enemy["shield_charges"] = max(enemy.get("shield_charges", 0), 1)
                enemy["shield_color"] = warden["color"]

    return enemies


def enemy_is_visible(enemy):
    """Incoming enemies become visible as their first pixels enter the screen."""
    return enemy["rect"].bottom > GAMEPLAY_TOP


def move_enemy_down(enemy, distance):
    """Move a ship while preserving diver/weaver anchor positions."""
    distance_with_remainder = distance + enemy.get("descent_fraction", 0.0)
    whole_pixels = int(distance_with_remainder)
    enemy["descent_fraction"] = distance_with_remainder - whole_pixels
    enemy["rect"].y += whole_pixels
    if enemy.get("type") == "diver":
        enemy["dive_origin_y"] += distance
    elif enemy.get("type") in ("weaver", "orbit"):
        enemy["weave_origin_y"] += distance


def enemy_cryo_multiplier(enemy, now=None):
    now = pygame.time.get_ticks() if now is None else now
    if enemy.get("cryo_slow_until", 0) > now:
        return (FROSTBITE_BOSS_SPEED_MULTIPLIER if enemy.get("is_boss", False)
                else FROSTBITE_ENEMY_SPEED_MULTIPLIER)
    return 1.0


def apply_cryo_hit(enemy, bullet):
    if isinstance(bullet, dict) and bullet.get("cryo") and enemy["hp"] > 0:
        enemy["cryo_slow_until"] = pygame.time.get_ticks() + CRYO_SLOW_MS


def update_enemies(enemies, fleet_dx, enemy_dy, round_num):
    # Independent shardling timers: destroying one fragment does not prevent
    # its surviving siblings from becoming separate Splitters.
    for fragment in enemies[:]:
        if fragment.get("type") != "shardling" or "regrow_timer" not in fragment:
            continue
        fragment["regrow_timer"] -= 1
        if fragment["regrow_timer"] > 0:
            continue
        original = fragment["regrow_template"].copy()
        new_rect = original["rect"].copy()
        new_rect.center = fragment["rect"].center
        original["rect"] = new_rect
        original["x"] = float(new_rect.x)
        original["hp"] = original["max_hp"]
        original["animation_hit"] = 0
        original["animation_fire"] = 0
        original["animation_last_center"] = new_rect.center
        original.pop("damage_by_player", None)
        enemies.remove(fragment)
        enemies.append(original)

    speed_cap = ENEMY_SPEED_CAP + max(0, round_num - MAX_CAMPAIGN_ROUND) * 0.005
    speed_boost = min(
        speed_cap,
        ENEMY_SPEED_START + ENEMY_SPEED_PER_ROUND * (round_num - 1),
    )

    # Movement identities are exclusive: Swift adds pace to a weave rather
    # than applying a second independent horizontal move in the same frame.
    fleet_enemies = [e for e in enemies if not e["is_speedy"] and e["type"] not in ("diver", "weaver", "orbit")]
    speedy_enemies = [e for e in enemies if e["is_speedy"] and e["type"] not in ("diver", "weaver", "orbit")]
    diving_enemies = [e for e in enemies if e["type"] == "diver"]
    weaving_enemies = [e for e in enemies if e["type"] in ("weaver", "orbit")]

    fleet_move = fleet_dx * min(speed_boost, PLAYER_SPEED)

    hit_edge = False
    for enemy in fleet_enemies:
        left = enemy["x"] + fleet_move * enemy_cryo_multiplier(enemy)
        right = left + enemy["rect"].width
        if (fleet_dx > 0 and right >= SCREEN_WIDTH - MARGIN) or \
           (fleet_dx < 0 and left <= MARGIN):
            hit_edge = True
            break

    if hit_edge:
        fleet_dx *= -1
        for enemy in fleet_enemies:
            enemy["descent_remaining"] = enemy.get("descent_remaining", 0) + enemy_dy
    else:
        for enemy in fleet_enemies:
            enemy["x"] += fleet_move * enemy_cryo_multiplier(enemy)
            enemy["rect"].x = int(round(enemy["x"]))

    for enemy in speedy_enemies:
        if enemy["type"] == "blink":
            enemy["blink_timer"] += enemy_cryo_multiplier(enemy)
            if enemy["blink_timer"] >= 90:
                enemy["blink_timer"] = 0
                enemy["blink_count"] = enemy.get("blink_count", 0) + 1
                if enemy["blink_count"] % 3 == 0:
                    enemy["descent_remaining"] = enemy.get("descent_remaining", 0) + enemy_dy
                enemy["x"] = max(
                    MARGIN,
                    min(
                        SCREEN_WIDTH - MARGIN - enemy["rect"].width,
                        enemy["x"] + random.choice((-1, 1)) * random.randint(110, 170),
                    ),
                )
                enemy["rect"].x = int(round(enemy["x"]))
            continue

        mult = enemy.get("speed_mult", 1.8)
        move_speed = mult * speed_boost
        if enemy.get("type") != "speedy" or enemy.get("mutation") != "swift":
            move_speed = min(move_speed, PLAYER_SPEED)
        speedy_move = enemy["dx"] * move_speed * enemy_cryo_multiplier(enemy)
        left = enemy["x"] + speedy_move
        right = left + enemy["rect"].width

        if (enemy["dx"] > 0 and right >= SCREEN_WIDTH - MARGIN) or \
           (enemy["dx"] < 0 and left <= MARGIN):
            enemy["dx"] *= -1
            enemy["descent_remaining"] = enemy.get("descent_remaining", 0) + enemy_dy
        else:
            enemy["x"] += speedy_move
            enemy["rect"].x = int(round(enemy["x"]))

    for enemy in diving_enemies:
        mult = enemy.get("speed_mult", 3.1)
        dive_move = enemy["dx"] * min(mult * speed_boost, PLAYER_SPEED) * enemy_cryo_multiplier(enemy)
        left = enemy["x"] + dive_move
        right = left + enemy["rect"].width
        if (enemy["dx"] > 0 and right >= SCREEN_WIDTH - MARGIN) or \
           (enemy["dx"] < 0 and left <= MARGIN):
            enemy["dx"] *= -1
            enemy["descent_remaining"] = enemy.get("descent_remaining", 0) + enemy_dy
        else:
            enemy["x"] += dive_move
            enemy["rect"].x = int(round(enemy["x"]))
        enemy["dive_phase"] += 0.035 * enemy_cryo_multiplier(enemy)
        enemy["rect"].y = int(enemy["dive_origin_y"] + max(0, math.sin(enemy["dive_phase"])) * 75)

    for enemy in weaving_enemies:
        swift_multiplier = 1.15 if enemy.get("mutation") == "swift" else 1.0
        cryo_multiplier = enemy_cryo_multiplier(enemy)
        enemy["weave_phase"] += 0.09 * swift_multiplier * cryo_multiplier
        enemy["weave_y_phase"] += enemy["weave_y_rate"] * swift_multiplier * cryo_multiplier
        weave_amplitude = 10 if enemy["type"] == "orbit" else 6
        weave_move = max(
            -PLAYER_SPEED,
            min(
                PLAYER_SPEED,
                (enemy["dx"] * speed_boost
                 + math.sin(enemy["weave_phase"]) * weave_amplitude) * swift_multiplier,
            ),
        )
        right_limit = SCREEN_WIDTH - MARGIN - enemy["rect"].width
        next_x = enemy["x"] + weave_move * cryo_multiplier
        if next_x >= right_limit:
            enemy["x"] = right_limit
            if enemy["dx"] > 0:
                enemy["dx"] = -1
                enemy["descent_remaining"] = enemy.get("descent_remaining", 0) + enemy_dy
        elif next_x <= MARGIN:
            enemy["x"] = MARGIN
            if enemy["dx"] < 0:
                enemy["dx"] = 1
                enemy["descent_remaining"] = enemy.get("descent_remaining", 0) + enemy_dy
        else:
            enemy["x"] = next_x
        enemy["rect"].x = int(round(enemy["x"]))
        enemy["rect"].y = int(round(
            enemy["weave_origin_y"]
            + math.sin(enemy["weave_y_phase"]) * enemy["weave_y_amplitude"]
        ))

    for enemy in enemies:
        descent = min(ENEMY_DESCENT_STEP * enemy_cryo_multiplier(enemy), enemy.get("descent_remaining", 0))
        if descent:
            move_enemy_down(enemy, descent)
            enemy["descent_remaining"] -= descent

    # Without a visible enemy to fight, don't make players wait for an
    # offscreen row to crawl down by a few pixels on each screen bounce.
    # Only hidden enemies are accelerated; never teleport or reveal all at once.
    if enemies and not any(enemy_is_visible(enemy) for enemy in enemies):
        hidden = [enemy for enemy in enemies if not enemy_is_visible(enemy)]
        for enemy in hidden:
            distance = GAMEPLAY_TOP + 3 - enemy["rect"].bottom
            if distance > 0:
                move_enemy_down(enemy, min(HIDDEN_ENEMY_CATCHUP_SPEED * enemy_cryo_multiplier(enemy), distance))

    return fleet_dx


def create_enemy_projectile(x, y, dx, dy, size=8, color=RED):
    rect = pygame.Rect(round(x - size / 2), round(y - size / 2), size, size)
    return {
        "rect": rect,
        "x": float(rect.x),
        "y": float(rect.y),
        "dx": dx * ENEMY_PROJECTILE_SPEED_MULTIPLIER,
        "dy": dy * ENEMY_PROJECTILE_SPEED_MULTIPLIER,
        "color": color,
    }


def damage_enemy(enemy, damage, player_number, *, ignore_shields=False):
    if damage <= 0:
        return 0
    if not ignore_shields and enemy.get("shield_charges", 0) > 0:
        enemy["shield_charges"] -= 1
        enemy["animation_hit"] = 6
        return 0

    actual_damage = min(enemy["hp"], max(0, damage))
    enemy["hp"] -= actual_damage
    if actual_damage > 0:
        enemy["animation_hit"] = 8
    if player_number is not None and actual_damage > 0:
        damage_by_player = enemy.setdefault("damage_by_player", {})
        damage_by_player[player_number] = damage_by_player.get(player_number, 0) + actual_damage
    if actual_damage > 0 and enemy["hp"] <= 0:
        audio = ensure_audio_manager()
        if audio is not None:
            audio.play(audio.explosion)
    return actual_damage


def award_enemy_score(enemy, players):
    damage_by_player = enemy.get("damage_by_player", {})
    total_damage = sum(damage_by_player.values())
    if total_damage <= 0:
        return

    if enemy.get("is_boss", False):
        points = enemy["max_hp"] * 25
    else:
        points = ENEMY_SCORE_VALUES.get(enemy.get("type", "standard"), 100)
    points = int(points * MUTATION_SCORE_MULTIPLIERS.get(enemy.get("mutation"), 1))

    contributors = [
        (player, damage_by_player.get(player["number"], 0))
        for player in players
        if damage_by_player.get(player["number"], 0) > 0
    ]
    top_contributor = max(contributors, key=lambda contribution: contribution[1])[0]
    top_contributor["kills"] += 1
    now = pygame.time.get_ticks()
    shares = [
        points * damage / total_damage
        * (2 if player.get("score_boost_until", 0) > now else 1)
        for player, damage in contributors
    ]
    awarded = [int(share) for share in shares]
    remainder = round(sum(shares)) - sum(awarded)
    order = sorted(range(len(shares)), key=lambda index: shares[index] - awarded[index], reverse=True)
    for index in order[:remainder]:
        awarded[index] += 1
    for (player, _), score in zip(contributors, awarded):
        player["score"] += score


def defeat_enemy(enemy, enemies, players):
    award_enemy_score(enemy, players)
    enemies.remove(enemy)
    if enemy.get("type") != "splitter":
        return

    visual = random.choice(VISUAL_VARIATIONS["shardling"])
    width = max(12, ENEMY_WIDTH // 2)
    height = max(10, ENEMY_HEIGHT // 2)
    regrow_template = enemy.copy()
    direction = -1 if enemy.get("dx", 1) < 0 else 1
    # Keep siblings in one readable stream instead of sending them both ways.
    # Near an edge, the whole group launches back toward the playfield center.
    if enemy["rect"].left <= MARGIN + width * 2:
        direction = 1
    elif enemy["rect"].right >= SCREEN_WIDTH - MARGIN - width * 2:
        direction = -1
    spacing = max(width + 4, enemy["rect"].width + 8)
    group_width = width + spacing * (SPLITTER_FRAGMENT_COUNT - 1)
    group_left = max(MARGIN, min(SCREEN_WIDTH - MARGIN - group_width,
                                 enemy["rect"].centerx - group_width / 2))
    for index in range(SPLITTER_FRAGMENT_COUNT):
        x = group_left + index * spacing
        y = enemy["rect"].centery - height // 2
        enemies.append({
            "type": "shardling",
            "is_boss": False,
            "formation": enemy.get("formation", "grid"),
            "mutation": None,
            "color": visual["color"],
            "can_shoot": False,
            "is_speedy": True,
            "rect": pygame.Rect(round(x), round(y), width, height),
            "x": float(x),
            "surface": generate_pixel_sprite(visual["art"], visual["color"], width, height),
            "dx": direction,
            "hp": 1,
            "max_hp": 1,
            "shield_charges": 0,
            "speed_mult": SPLITTER_SHARD_SPEED_MULTIPLIER,
            "weave_phase": 0,
            "weave_y_phase": 0,
            "weave_y_amplitude": 0,
            "weave_y_rate": 0,
            "weave_origin_y": float(y),
            "dive_phase": 0,
            "dive_origin_y": float(y),
            "regrow_timer": SPLITTER_REGROW_FRAMES + index * SPLITTER_REGROW_STAGGER_FRAMES,
            "regrow_template": regrow_template,
        })
        attach_ship_animation(enemies[-1], visual["art"], visual["color"], width, height, "fast")


def fire_boss_queued_shot(enemy, enemy_bullets, shot, target_positions=()):
    animate_ship_fire(enemy)
    x, y, dx, dy, size, color, *properties = shot
    if x is None:
        x = enemy["rect"].centerx
        y = enemy["rect"].bottom
    extras = dict(properties[0]) if properties else {}
    # The whole volley uses its initial aim. Moving after the tell opens a
    # dodge route instead of making every later pulse follow the pilot.
    projectile = create_enemy_projectile(x, y, dx, dy, size, color)
    projectile.update(extras)
    if enemy.get("attack_pattern") in AIMED_BOSS_PATTERNS:
        projectile["aimed_shot"] = True
        projectile["aimed_fired_ms"] = pygame.time.get_ticks()
    enemy_bullets.append(projectile)


def choose_target_position(target_positions, fallback):
    return random.choice(target_positions) if target_positions else fallback


def aimed_velocity(origin_x, origin_y, target_positions, speed):
    if not target_positions:
        return 0, speed

    target_x, target_y = random.choice(target_positions)
    direction_x = target_x - origin_x
    direction_y = target_y - origin_y
    distance = max(1, math.hypot(direction_x, direction_y))
    return direction_x / distance * speed, direction_y / distance * speed


def predicted_boss_targets(players, fallback_targets, round_num):
    """Lead MOVING players at launch, not homing unfairly after launch.

    Aim prediction is capped so reversing direction or passing through a gap
    remains a viable dodge. It gets a little smarter at later boss waves.
    """
    lead_frames = min(14, 6 + 2 * (enemy_combat_tier(round_num) - 1))
    positions = []
    for player in players:
        if player.get("eliminated") or player.get("respawn_until", 0) > 0:
            continue
        x = player["x"] + PLAYER_WIDTH / 2
        y = player["y"] + PLAYER_HEIGHT / 2
        shift_x = max(-BOSS_AIM_MAX_LEAD_PX, min(BOSS_AIM_MAX_LEAD_PX, player.get("move_dx", 0) * lead_frames))
        shift_y = max(-75, min(75, player.get("move_dy", 0) * lead_frames))
        positions.append((max(20, min(SCREEN_WIDTH - 20, x + shift_x)),
                          max(GAMEPLAY_TOP + 25, min(SCREEN_HEIGHT - 25, y + shift_y))))
    return positions or list(fallback_targets)


def boss_lane_positions(target_x, round_num, crossing=False):
    """Broad lanes stay on screen, with ship-sized gaps between every shot."""
    progress = boss_difficulty_progress(round_num)
    coverage = (0.56 + 0.14 * progress) if crossing else (0.58 + 0.16 * progress)
    span = SCREEN_WIDTH * coverage
    count = max(7, math.ceil(span / 82) + 1)
    # Cross lanes alternate direction in pairs. Curtains stay symmetrical.
    if crossing:
        count += count % 2
    elif count % 2 == 0:
        count += 1
    half_span = span / 2
    center = max(half_span + 12, min(SCREEN_WIDTH - half_span - 12, target_x))
    return [center - half_span + index * span / (count - 1) for index in range(count)]


def boss_burst_profile(enemy):
    """Near defeat, bosses become aggressive; never eliminate counterplay."""
    hp_fraction = enemy["hp"] / max(1, enemy["max_hp"])
    progress = enemy.get("difficulty_progress", 0.0)
    # Enrage tightens recovery, but never doubles the number of simultaneous
    # shots. Late-game patterns get denser gradually rather than at wave 21.
    batch = 2 if (progress >= 0.45 or enemy.get("attack_pattern") in ("curtain", "cross_lanes")) else 1
    gap = max(10, round(14 - 4 * progress) - (1 if hp_fraction <= 0.35 else 0))
    rest = max(84, round(enemy["attack_delay"] * (0.88 if hp_fraction <= 0.35 else 0.95 if hp_fraction <= 0.65 else 1)))
    if enemy.get("attack_pattern") in AIMED_BOSS_PATTERNS:
        # Aimed attacks demand a deliberate dodge; give it room to finish.
        rest = round(rest * 1.18)
        gap += 3
    return batch, gap, rest


def fire_boss_burst(enemy, enemy_bullets, target_positions, max_bullets, encounter=()):
    """Launch grouped but bounded projectiles for readable bullet-hell arcs."""
    batch_size, burst_gap, rest = boss_burst_profile(enemy)
    for _ in range(batch_size):
        if not enemy["attack_queue"] or len(enemy_bullets) >= max_bullets:
            break
        shot = enemy["attack_queue"].pop(0)
        fire_boss_queued_shot(enemy, enemy_bullets, shot, target_positions)
    # Discard remaining shots if the current screen is already crowded.
    if len(enemy_bullets) >= max_bullets:
        enemy["attack_queue"].clear()
    enemy["attack_cooldown"] = burst_gap if enemy["attack_queue"] else rest
    for other in encounter:
        if other is not enemy and other.get("is_boss"):
            other["attack_cooldown"] = max(other["attack_cooldown"],
                                           BOSS_ENCOUNTER_RECOVERY_FRAMES)


def milestone_boss_phase(enemy):
    """Three readable stages, with the same full warning window in every stage."""
    fraction = enemy["hp"] / max(1, enemy["max_hp"])
    return 3 if fraction <= .35 else 2 if fraction <= .65 else 1


def plan_milestone_attack(enemy):
    """Commit the whole signature before its tell; no tracking or surprise aim."""
    kind = enemy["milestone_kind"]
    phase = milestone_boss_phase(enemy)
    cursor = enemy.get("signature_index", 0)
    color = enemy["color"]
    origin_x, origin_y = enemy["rect"].midbottom
    shots, beams = [], []
    safe_gap = None
    cycles = {"bulwark": ("gates", "hammer"),
              "helix": ("helix", "bloom"),
              "tempest": ("channels", "crosswind"),
              "eclipse": ("eclipse_gates", "corona", "lances", "horizon")}
    options = cycles[kind]
    if kind == "eclipse":
        options = options[:phase + 1]
    pattern = options[cursor % len(options)]
    names = {"gates": "IRON GATES", "hammer": "HAMMER FAN",
             "helix": "DOUBLE HELIX", "bloom": "PRISM BLOOM",
             "channels": "STORM CHANNELS", "crosswind": "CROSSWIND",
             "eclipse_gates": "ECLIPSE GATES", "corona": "SOLAR CORONA",
             "lances": "SINGULARITY LANCES", "horizon": "EVENT HORIZON"}

    if pattern in ("gates", "eclipse_gates"):
        # A broad wall has one deliberate, generous opening. Alternate its
        # position between volleys; the displayed gate never moves during a tell.
        gate_fraction = (.28, .72, .5)[(cursor // 2) % 3]
        gap_width = 220 if kind == "bulwark" else 200
        safe_gap = pygame.Rect(round(SCREEN_WIDTH * gate_fraction - gap_width / 2),
                               origin_y, gap_width, SCREEN_HEIGHT - origin_y)
        count = 18 if kind == "bulwark" else 22
        for index in range(count):
            x = 36 + index * (SCREEN_WIDTH - 72) / (count - 1)
            if safe_gap.left - 16 <= x <= safe_gap.right + 16:
                continue
            shots.append((x, origin_y, 0, 4.5 + .2 * phase, 18, color))
    elif pattern == "hammer":
        # Wide heavy arcs, with a central corridor instead of an aimed burst.
        for index in range(12):
            angle = -1.0 + 2.0 * index / 11
            if abs(angle) < .22:
                continue
            speed = 4.3 + .15 * phase
            shots.append((origin_x, origin_y, math.sin(angle) * speed,
                          math.cos(angle) * speed, 23, color))
    elif pattern == "helix":
        # Two mirrored ribbons originate at the visible wing beacons. Their
        # headings alternate between cycles, and remain fixed after launch.
        tilt = .12 if (cursor // 2) % 2 else -.12
        for side in (-1, 1):
            x = max(30, min(SCREEN_WIDTH - 30,
                           origin_x + side * enemy["rect"].width * .48))
            for index in range(6):
                angle = -.78 + 1.56 * index / 5 + side * tilt
                speed = 4.5 + .15 * phase
                shots.append((x, origin_y, math.sin(angle) * speed,
                              math.cos(angle) * speed, 12, color))
    elif pattern in ("bloom", "corona"):
        count = 16 if pattern == "bloom" else 22
        rotation = (cursor // 2) * .19
        for index in range(count):
            angle = math.tau * index / count + rotation
            speed = (4.0 if pattern == "bloom" else 4.5) + .15 * phase
            shots.append((origin_x, origin_y, math.cos(angle) * speed,
                          math.sin(angle) * speed, 12, color))
    elif pattern in ("channels", "lances"):
        if pattern == "channels":
            # Alternate the middle and edge lanes, with the same full warning.
            # Neither central parking nor a permanent corner solves the fight.
            channel_sets = ((.3, .7), (.18, .5), (.025, .975), (.5, .82))
            fractions = channel_sets[(cursor // 2) % len(channel_sets)]
        else:
            fractions = (.18, .5, .82)
        width = (64 if pattern == "channels" else 58) + 4 * (phase - 1)
        shift = (0 if pattern == "channels" else
                 .045 * SCREEN_WIDTH * (1 if (cursor // 2) % 2 else -1))
        for fraction in fractions:
            x = max(8, min(SCREEN_WIDTH - width - 8,
                           round(SCREEN_WIDTH * fraction + shift - width / 2)))
            beams.append(pygame.Rect(x, origin_y, width, SCREEN_HEIGHT - origin_y))
    else:
        count = 12 if pattern == "crosswind" else 16
        direction = 1 if (cursor // 2) % 2 else -1
        for index in range(count):
            x = 60 + index * (SCREEN_WIDTH - 120) / (count - 1)
            # Each half follows one wind direction; this opens a large middle
            # channel rather than filling every lane with converging bullets.
            side = -1 if x < SCREEN_WIDTH / 2 else 1
            dx = side * (1.15 if pattern == "crosswind" else 1.5)
            if direction > 0:
                dx *= .7
            shots.append((x, origin_y, dx, 4.4 + .15 * phase, 14, color))

    return {"name": names[pattern], "pattern": pattern, "shots": shots,
            "beams": beams, "safe_gap": safe_gap,
            "remaining_frames": BOSS_LASER_WARNING_FRAMES,
            "warning_frames": BOSS_LASER_WARNING_FRAMES, "phase": phase}


def update_milestone_boss_attack(enemy, enemy_bullets, max_bullets):
    """One fully telegraphed signature at a time, within the ordinary cap."""
    warning = enemy.get("signature_warning")
    if warning is not None:
        warning["remaining_frames"] -= 1
        if warning["remaining_frames"] > 0:
            return
        available = max(0, max_bullets - len(enemy_bullets))
        # Never release half a planned wall and change its announced geometry.
        required = len(warning["shots"]) + len(warning["beams"])
        if required > available:
            warning["remaining_frames"] = 1
            return
        animate_ship_fire(enemy)
        for x, y, dx, dy, size, color in warning["shots"]:
            projectile = create_enemy_projectile(x, y, dx, dy, size, color)
            projectile["milestone_signature"] = warning["pattern"]
            enemy_bullets.append(projectile)
        for rect in warning["beams"]:
            enemy_bullets.append({"rect": rect.copy(), "dx": 0, "dy": 0,
                                  "color": enemy["color"], "laser_state": "active",
                                  "remaining_frames": BOSS_LASER_ACTIVE_FRAMES + 1,
                                  "milestone_signature": warning["pattern"]})
        enemy["signature_warning"] = None
        enemy["signature_index"] = enemy.get("signature_index", 0) + 1
        enemy["attack_cooldown"] = max(96, 156 - warning["phase"] * 15
                                       - (12 if enemy["milestone_kind"] == "eclipse" else 0))
        return
    # The beam and its escape lanes finish before the next warning can begin.
    if any(shot.get("laser_state") for shot in enemy_bullets):
        return
    enemy["attack_cooldown"] -= 1
    if enemy["attack_cooldown"] > 0:
        return
    # Let previous waves disperse. There is no extra aimed/homing stream hiding
    # behind the signature, even during the final boss's last phase.
    if len(enemy_bullets) > max_bullets // 3:
        enemy["attack_cooldown"] = 15
        return
    warning = plan_milestone_attack(enemy)
    enemy["signature_warning"] = warning
    enemy["attack_pattern"] = warning["pattern"]
    enemy["last_attack_pattern"] = warning["pattern"]


def draw_milestone_attack_warning(screen, enemy):
    """Pure, lightweight tells use the exact committed launch geometry."""
    warning = enemy.get("signature_warning")
    if warning is None:
        return
    color = enemy["color"]
    elapsed = warning["warning_frames"] - warning["remaining_frames"]
    bright = blend_color(color, UI_TEXT, .3 + .2 * math.sin(elapsed * .2))
    for rect in warning["beams"]:
        pygame.draw.rect(screen, color, rect, 2)
        pygame.draw.line(screen, bright, rect.midtop, rect.midbottom, 1)
        for y in range(rect.top + (elapsed * 2) % 32, rect.bottom, 32):
            pygame.draw.line(screen, color, (rect.left + 3, y),
                             (rect.right - 3, min(rect.bottom, y + 12)), 1)
    safe_gap = warning["safe_gap"]
    if safe_gap is not None:
        pygame.draw.line(screen, UI_MINT, safe_gap.topleft, safe_gap.bottomleft, 2)
        pygame.draw.line(screen, UI_MINT, safe_gap.topright, safe_gap.bottomright, 2)
    for x, y, dx, dy, size, _ in warning["shots"]:
        speed = max(.01, math.hypot(dx, dy))
        end = (round(x + dx / speed * 90), round(y + dy / speed * 90))
        pygame.draw.circle(screen, color, (round(x), round(y)), max(4, size // 2), 1)
        pygame.draw.line(screen, bright, (round(x), round(y)), end, 1)
    label = hud_font(22).render(warning["name"], True, bright)
    label_rect = label.get_rect(midtop=(SCREEN_WIDTH // 2,
                                       max(110, enemy["rect"].bottom + 24)))
    screen.blit(label, label_rect)


def choose_powerup_type():
    return random.choices(
        POWERUP_TYPES, weights=[POWERUP_SPAWN_WEIGHTS[kind] for kind in POWERUP_TYPES], k=1,
    )[0]


def create_powerup(x, y):
    powerup_type = choose_powerup_type()
    return {
        "type": powerup_type,
        "rect": pygame.Rect(round(x - 12), round(y - 12), 24, 24),
        "dx": random.uniform(-0.8, 0.8),
        "dy": 2.4,
        "lifetime": 500,
        # Cosmetic phase is deterministic and does not consume gameplay RNG.
        "visual_phase": POWERUP_TYPES.index(powerup_type) * 0.73,
    }


def maybe_drop_powerup(powerups, x, y, chance=1.0, guaranteed=False):
    """One team pickup for boss clear; ordinary drops have strict pacing."""
    global _LAST_RANDOM_POWERUP_DROP_MS
    now = pygame.time.get_ticks()
    if not guaranteed:
        if len(powerups) >= MAX_WORLD_POWERUPS:
            return False
        if now - _LAST_RANDOM_POWERUP_DROP_MS < POWERUP_DROP_COOLDOWN_MS:
            return False
        if random.random() >= chance:
            return False
        _LAST_RANDOM_POWERUP_DROP_MS = now
    elif len(powerups) >= MAX_WORLD_POWERUPS:
        # Make room for the guaranteed ONE pickup earned by the whole team.
        powerups.pop(0)
    powerups.append(create_powerup(x, y))
    return True


def player_life_capacity(player):
    """Lives and regenerating durability are separate resources."""
    return BASE_MAX_LIVES


def durability_capacity(player):
    """Total unblocked hits a fresh ship can take before losing its life."""
    return 1 + min(MAX_DURABILITY_BONUS, max(0, player.get("durability_bonus", 0)))


def durability_remaining(player):
    return max(1, durability_capacity(player) - player.get("durability_damage", 0))


def reset_durability(player):
    player["durability_damage"] = 0
    player["durability_regen_until"] = 0
    player["durability_invuln_until"] = 0


def update_durability(players, now=None):
    """Repair one absorbed hit after a quiet interval, then every two seconds."""
    now = pygame.time.get_ticks() if now is None else now
    for player in players:
        damage = player.get("durability_damage", 0)
        if not damage:
            player["durability_regen_until"] = 0
            continue
        if player.get("eliminated", False) or player.get("respawn_until", 0) > now:
            continue
        deadline = player.get("durability_regen_until", 0)
        if not deadline:
            player["durability_regen_until"] = now + DURABILITY_REGEN_DELAY_MS
        elif now >= deadline:
            repaired = min(damage, 1 + (now - deadline) // DURABILITY_REGEN_INTERVAL_MS)
            player["durability_damage"] = damage - repaired
            player["durability_regen_until"] = (
                deadline + repaired * DURABILITY_REGEN_INTERVAL_MS
                if player["durability_damage"] else 0)


def migrate_legacy_health_state(pilot):
    """Convert an earlier capacity upgrade to durability without granting lives."""
    if "health_bonus" in pilot:
        pilot.setdefault("durability_bonus", pilot.pop("health_bonus"))
        if "lives" in pilot:
            pilot["lives"] = min(BASE_MAX_LIVES, pilot["lives"])
    return pilot


def grant_powerup(player, powerup_type, enemy_bullets=None):
    now = pygame.time.get_ticks()
    audio = ensure_audio_manager()
    if powerup_type == "damage_up" and player["damage_bonus"] >= MAX_DAMAGE_BONUS:
        powerup_type = "score_boost"
    if powerup_type == "health_up" and player.get("durability_bonus", 0) >= MAX_DURABILITY_BONUS:
        powerup_type = "score_boost"
    if ((powerup_type == "emergency_warp" and player.get("warp_ready", False))
            or (powerup_type == "reflector" and player.get("reflector_charges", 0) >= 3)
            or (powerup_type == "supply_beacon" and player.get("supply_kills_left", 0) >= 8)):
        powerup_type = "score_boost"
    duration = POWERUP_DURATIONS.get(powerup_type, 0)
    if powerup_type == "life":
        if player["eliminated"]:
            player["eliminated"] = False
            player["lives"] = 1
            player["respawn_until"] = now + RESPAWN_DURATION
            reset_durability(player)
        else:
            player["lives"] = min(player_life_capacity(player), player["lives"] + 1)
    elif powerup_type == "damage_up":
        player["damage_bonus"] += 1
    elif powerup_type == "health_up":
        player["durability_bonus"] = player.get("durability_bonus", 0) + 1
    elif powerup_type == "emergency_warp":
        player["warp_ready"] = True
    elif powerup_type == "reflector":
        player["reflector_charges"] = 3
    elif powerup_type == "supply_beacon":
        player["supply_kills_left"] = 8
    elif powerup_type == "nova_pulse":
        player["pending_nova"] = True
        # A second pickup refreshes one charge instead of banking extra blasts.
        player["nova_charge_until"] = now + NOVA_COUNTDOWN_MS
    elif powerup_type == "missile_swarm":
        player["pending_missiles"] = True
    elif powerup_type in POWERUP_TIMER_KEYS:
        timer_key = POWERUP_TIMER_KEYS[powerup_type]
        if powerup_type == "bullet_time" and player[timer_key] <= now:
            player["momentum_stacks"] = 0
            player["momentum_flash_until"] = 0
            # New charge: an old projectile may count again, but never twice
            # during the same charge (even if it leaves/re-enters the field).
            player["momentum_generation"] = player.get("momentum_generation", 0) + 1
        if powerup_type == "cryo" and player[timer_key] <= now:
            player["shatter_stacks"] = 0
            player["shatter_flash_until"] = 0
        # Repeated drops extend a buff, but cannot bank unlimited invulnerability.
        player[timer_key] = min(max(now, player[timer_key]) + duration, now + duration * 2)
    if powerup_type in ("rapid_fire", "laser", "bomb", "triple_shot", "piercing"):
        player["cooldown"] = min(player["cooldown"], 1)

    player["powerup_notice"] = POWERUP_LABELS[powerup_type]
    player["powerup_notice_until"] = now + 1800
    if audio is not None:
        audio.play(audio.powerup)


def update_powerups(powerups, players, enemy_bullets, particles=None):
    now = pygame.time.get_ticks()

    for powerup in powerups[:]:
        powerup["lifetime"] -= 1
        if powerup["lifetime"] <= 0:
            powerups.remove(powerup)
            continue

        magnet_players = [
            player for player in players
            if not player["eliminated"] and player["respawn_until"] <= now
            and player["magnet_until"] > now
        ]
        if magnet_players:
            target = min(
                magnet_players,
                key=lambda player: (player["x"] - powerup["rect"].centerx) ** 2
                + (player["y"] - powerup["rect"].centery) ** 2,
            )
            direction_x = target["x"] - powerup["rect"].centerx
            direction_y = target["y"] - powerup["rect"].centery
            distance = max(1, math.hypot(direction_x, direction_y))
            powerup["dx"] += (direction_x / distance * 5 - powerup["dx"]) * 0.08
            powerup["dy"] += (direction_y / distance * 5 - powerup["dy"]) * 0.08
        else:
            powerup["dx"] *= 0.9
            powerup["dy"] = min(2.4, powerup["dy"] + 0.1)
        powerup["rect"].x += round(powerup["dx"])
        powerup["rect"].y += round(powerup["dy"])
        if powerup["rect"].top > SCREEN_HEIGHT:
            powerups.remove(powerup)
            continue

        for player in players:
            if (player["eliminated"] or player["respawn_until"] > now):
                continue
            player_rect = pygame.Rect(player["x"], player["y"], PLAYER_WIDTH, PLAYER_HEIGHT)
            if powerup["rect"].colliderect(player_rect):
                grant_powerup(player, powerup["type"], enemy_bullets)
                if particles is not None:
                    spawn_powerup_pickup_effect(player, powerup["type"], particles)
                powerups.remove(powerup)
                break


def momentum_stacks(player, now):
    """Bullet Time's captured energy only lasts while that buff is active."""
    if (player.get("bullet_time_until", 0) <= now
            or player.get("eliminated", False)
            or player.get("respawn_until", 0) > now):
        return 0
    return min(BULLET_TIME_MAX_STACKS, player.get("momentum_stacks", 0))


def shatter_stacks(player, now):
    """Frostbite kill stacks are independent, with a lower total bonus."""
    if (player.get("cryo_until", 0) <= now or player.get("eliminated", False)
            or player.get("respawn_until", 0) > now):
        return 0
    return min(SHATTER_MAX_STACKS, player.get("shatter_stacks", 0))


def powerup_speed_bonus(player, now):
    return max(momentum_stacks(player, now) * BULLET_TIME_SPEED_PER_STACK,
               shatter_stacks(player, now) * SHATTER_SPEED_PER_STACK)


def powerup_fire_bonus(player, now):
    return max(momentum_stacks(player, now) * BULLET_TIME_FIRE_PER_STACK,
               shatter_stacks(player, now) * SHATTER_FIRE_PER_STACK)


def grant_momentum(player, now, origin=None, particles=None):
    """Award one Bullet Time stack to a living pilot."""
    if (player.get("bullet_time_until", 0) <= now
            or player.get("eliminated", False) or player.get("respawn_until", 0) > now):
        return False
    old_stacks = player.get("momentum_stacks", 0)
    player["momentum_stacks"] = min(BULLET_TIME_MAX_STACKS, old_stacks + 1)
    player["momentum_flash_until"] = now + 440
    # Small energy motes communicate a captured shot.
    if particles is not None and origin is not None:
        start_x, start_y = origin
        target_x = player["x"] + PLAYER_WIDTH / 2
        target_y = player["y"] + PLAYER_HEIGHT / 2
        distance = max(1.0, math.hypot(target_x - start_x, target_y - start_y))
        for index in range(5):
            spread = (index - 2) * 0.20
            particles.append({
                "kind": "momentum",
                "x": float(start_x), "y": float(start_y),
                "dx": (target_x - start_x) / distance * (7.5 + index * 0.75) - (target_y - start_y) / distance * spread,
                "dy": (target_y - start_y) / distance * (7.5 + index * 0.75) + (target_x - start_x) / distance * spread,
                "radius": 3,
                "color": (UI_CYAN, UI_VIOLET, player["color"])[index % 3],
                "lifetime": 13, "max_lifetime": 13,
            })
    return True


def grant_shatter(player, now, origin=None, particles=None):
    """One credited Frostbite kill grants one Shatter stack, up to six."""
    if (player.get("cryo_until", 0) <= now or player.get("eliminated", False)
            or player.get("respawn_until", 0) > now):
        return False
    old_stacks = player.get("shatter_stacks", 0)
    player["shatter_stacks"] = min(SHATTER_MAX_STACKS, old_stacks + 1)
    if old_stacks < SHATTER_MAX_STACKS:
        player["shatter_flash_until"] = now + 500
    if particles is not None and origin is not None and old_stacks < SHATTER_MAX_STACKS:
        available = max(0, 48 - sum(p.get("kind") == "shatter" for p in particles))
        for index in range(min(6, available)):
            angle = math.tau * index / 6
            particles.append({"kind": "shatter", "x": float(origin[0]), "y": float(origin[1]),
                              "dx": math.cos(angle) * 4.5, "dy": math.sin(angle) * 4.5,
                              "radius": 4, "color": POWERUP_COLORS["cryo"],
                              "angle": angle, "lifetime": 18, "max_lifetime": 18})
    return True


def collect_bullet_momentum(bullet, player, now, particles=None):
    """Each projectile charges each pilot at most once per Bullet Time charge."""
    if bullet.get("laser_state") is not None:
        return False
    generation = player.get("momentum_generation", 0)
    absorbed = bullet.setdefault("momentum_collected_by", {})
    player_number = player["number"]
    if absorbed.get(player_number) == generation:
        return False
    if not grant_momentum(player, now, bullet["rect"].center, particles):
        return False
    absorbed[player_number] = generation
    return True


# Special salvo sizes are larger than ordinary shots; reserve enough space
# BEFORE firing instead of clipping the volley and making it look broken.
ENEMY_SALVO_SIZES = {"volley": 3, "mine_layer": 2, "pulse": 6,
                     "scatterer": 5, "lancer": 2}
ENEMY_HEAVY_SHOOTERS = frozenset(("volley", "mine_layer", "pulse",
                                  "scatterer", "prism", "bomber"))
AIMED_ENEMY_TYPES = frozenset(("volley", "seeker", "ricochet", "prism",
                               "charger", "phantom", "sniper", "artillery",
                               "striker", "lancer"))
AIMED_BOSS_PATTERNS = frozenset(("aimed", "double_lance", "heavy_orb", "crossfire",
                                "pincer", "triple_burst", "homing", "wave_shot",
                                "splitter", "sniper", "bouncer", "ricochet",
                                "zigzag", "double_wave", "bombardment",
                                "seeker_pair", "triad"))
AIMED_VOLLEY_SPACING_MS = 180


def boss_difficulty_progress(round_num):
    """Bounded campaign curve: wave 5 is the introduction, wave 100 the peak."""
    return max(0.0, min(1.0, (round_num - 5) / (MAX_CAMPAIGN_ROUND - 5)))


def enemy_bullet_cap(player_count, is_boss=False, round_num=1):
    return (BASE_ENEMY_BULLET_CAP
            + max(0, min(4, player_count) - 1) * (6 if is_boss else ENEMY_BULLET_CAP_PER_EXTRA_PLAYER)
            + (BOSS_BULLET_CAP_BONUS + round(BOSS_LATE_EXTRA_BULLET_CAP
               * boss_difficulty_progress(round_num)) if is_boss else 0))


def enemy_fire_probability(enemy_type, round_num, player_count):
    """A controlled chance per 60 Hz frame with gentle co-op scaling.

    Projectile count is managed independently, so even a large wave at 30+
    cannot spawn an infinite wall of multi-shot projectiles.
    """
    base = {
        "shooter": .0040,
        "sniper": .0025, "bomber": .0015, "striker": .0030,
        "lancer": .0021, "bulwark": .0012, "artillery": .0018,
        "volley": .0018, "mine_layer": .0011, "seeker": .0021,
        "ricochet": .0026, "prism": .0015, "pulse": .0013,
        "charger": .0030, "scatterer": .0014, "phantom": .0022,
    }.get(enemy_type, .0030)
    # Firing progression is independent of the single health increase.
    sector_factor = min(1.15, .94 + .025 * (enemy_combat_tier(round_num) - 1))
    coop_factor = 1 + .12 * max(0, min(4, player_count) - 1)
    pressure_factor = .65 if enemy_type in AIMED_ENEMY_TYPES else .80
    return min(.012, base * 1.55 * sector_factor * coop_factor * pressure_factor)


def bend_projectile_from_gravity(bullet, players, now):
    """Deflect one moving shot gently, without slowing it or stacking fields."""
    if bullet.get("laser_state") is not None:
        return
    dx, dy = bullet.get("dx", 0.0), bullet.get("dy", 0.0)
    speed = math.hypot(dx, dy)
    remaining_turn = GRAVITY_MAX_PROJECTILE_TURN - bullet.get("gravity_turn_used", 0.0)
    if speed < 0.01 or remaining_turn <= 0:
        return
    choices = []
    for player in players:
        if (player.get("gravity_until", 0) <= now or player["eliminated"]
                or player["respawn_until"] > now):
            continue
        rx = bullet["rect"].centerx - (player["x"] + PLAYER_WIDTH / 2)
        ry = bullet["rect"].centery - (player["y"] + PLAYER_HEIGHT / 2)
        distance = math.hypot(rx, ry)
        if distance < GRAVITY_FIELD_RADIUS and dx * rx + dy * ry < 0:
            choices.append((distance, rx, ry))
    if not choices:
        return
    # The closest active field owns the force; co-op overlap never multiplies it.
    distance, rx, ry = min(choices)
    angle = math.atan2(dy, dx)
    away = math.atan2(ry, rx)
    difference = math.atan2(math.sin(away - angle), math.cos(away - angle))
    strength = 0.045 * (0.35 + 0.65 * (1 - distance / GRAVITY_FIELD_RADIUS))
    turn = max(-min(strength, remaining_turn), min(strength, remaining_turn, difference))
    bullet["dx"] = math.cos(angle + turn) * speed
    bullet["dy"] = math.sin(angle + turn) * speed
    bullet["gravity_turn_used"] = bullet.get("gravity_turn_used", 0.0) + abs(turn)


def update_enemy_projectiles(enemies, enemy_bullets, target_positions=(), players=(), particles=None, round_num=1):
    now = pygame.time.get_ticks()
    active_players = max(1, len(target_positions))
    boss_wave = any(enemy.get("is_boss", False) for enemy in enemies)
    max_bullets = enemy_bullet_cap(active_players, is_boss=boss_wave, round_num=round_num)
    boss_targets = predicted_boss_targets(players, target_positions, round_num)
    # The whole fleet shares a short aim window. Its live projectiles carry
    # the timing, so no hidden global or saved state can leak between runs.
    next_aimed_volley_ms = max((shot.get("aimed_fired_ms", -AIMED_VOLLEY_SPACING_MS)
                                + AIMED_VOLLEY_SPACING_MS
                               for shot in enemy_bullets if shot.get("aimed_shot")),
                              default=now)

    for enemy in enemies:
        if enemy["type"] == "medic":
            enemy["support_timer"] += 1
            if enemy["support_timer"] >= 180:
                enemy["support_timer"] = 0
                wounded = [ally for ally in enemies
                           if ally is not enemy and not ally.get("is_boss", False)
                           and ally["hp"] < ally["max_hp"]
                           and math.hypot(ally["rect"].centerx - enemy["rect"].centerx,
                                          ally["rect"].centery - enemy["rect"].centery) <= 185]
                if wounded:
                    # Medic is a healer, while Warden is strictly shield support.
                    target = min(wounded, key=lambda ally: ally["hp"] / max(1, ally["max_hp"]))
                    target["hp"] = min(target["max_hp"], target["hp"] + 2)
                    target["animation_support"] = 24
                    enemy["animation_support"] = 24

        # Entirely offscreen ships cannot fire invisible shots.
        if not enemy_is_visible(enemy) or not target_positions:
            continue

        if enemy.get("is_boss", False):
            if enemy.get("milestone_kind"):
                update_milestone_boss_attack(enemy, enemy_bullets, max_bullets)
                continue
            # One boss owns the current volley. Beams reserve their entire
            # warning/active window so a partner cannot hide the escape route.
            if (any(shot.get("laser_state") for shot in enemy_bullets)
                    or any(other is not enemy and other.get("attack_queue")
                           for other in enemies if other.get("is_boss"))):
                enemy["attack_cooldown"] = max(18, enemy["attack_cooldown"])
                continue
            if enemy["attack_queue"]:
                enemy["attack_cooldown"] -= 1
                if enemy["attack_cooldown"] <= 0:
                    fire_boss_burst(enemy, enemy_bullets, boss_targets, max_bullets, enemies)
                continue

            enemy["attack_cooldown"] -= 1
            if enemy["attack_cooldown"] > 0:
                continue
            # Let ongoing shots travel away before starting a new barrage.
            if len(enemy_bullets) >= max_bullets - 5:
                enemy["attack_cooldown"] = 18
                continue

            origin_x = enemy["rect"].centerx
            origin_y = enemy["rect"].bottom
            attack_patterns = enemy.get("attack_patterns", tuple(BOSS_ATTACKS))
            available_patterns = [
                pattern for pattern in attack_patterns
                if pattern != enemy.get("last_attack_pattern")
            ]
            if not available_patterns:
                available_patterns = list(attack_patterns)
            pattern = random.choices(
                available_patterns,
                weights=[BOSS_ATTACKS[name][1] * (1.10 if
                         enemy_combat_tier(round_num) >= 4 and name in
                         ("aimed", "fan", "crossfire", "pincer", "triple_burst", "triad", "sniper")
                         else 1.0) for name in available_patterns],
                k=1,
            )[0]
            enemy["last_attack_pattern"] = pattern
            enemy["attack_pattern"] = pattern
            enemy["color"] = BOSS_ATTACKS[pattern][0]
            enemy["surface"] = generate_pixel_sprite(
                BOSS_ART, enemy["color"], enemy["rect"].width, enemy["rect"].height
            )
            attach_ship_animation(enemy, BOSS_ART, enemy["color"],
                                  enemy["rect"].width, enemy["rect"].height, "heavy")

            if pattern == "laser":
                animate_ship_fire(enemy)
                target_x = choose_target_position(
                    boss_targets, (origin_x, SCREEN_HEIGHT - 40)
                )[0]
                beam_width = round(54 + 16 * boss_difficulty_progress(round_num))
                beam_x = max(0, min(SCREEN_WIDTH - beam_width, int(target_x - beam_width / 2)))
                enemy_bullets.append({
                    "rect": pygame.Rect(beam_x, origin_y, beam_width, SCREEN_HEIGHT - origin_y),
                    "dx": 0,
                    "dy": 0,
                    "color": PINK,
                    "laser_state": "warning",
                    "remaining_frames": BOSS_LASER_WARNING_FRAMES + 1,
                    "warning_frames": BOSS_LASER_WARNING_FRAMES,
                })
                enemy["attack_queue"] = []
                enemy["attack_cooldown"] = BOSS_ENCOUNTER_RECOVERY_FRAMES
                for other in enemies:
                    if other.get("is_boss"):
                        other["attack_cooldown"] = max(other["attack_cooldown"],
                                                       BOSS_ENCOUNTER_RECOVERY_FRAMES)
                continue

            if pattern == "scatter":
                shots = []
                for _ in range(10):
                    angle = random.uniform(-1.05, 1.05)
                    shots.append((None, None, math.sin(angle) * 6,
                                  math.cos(angle) * 6, 9, enemy["color"]))
            elif pattern == "slow_fan":
                shots = []
                for index in range(9):
                    angle = -0.9 + 1.8 * index / 8
                    shots.append((None, None, math.sin(angle) * 3.7,
                                  math.cos(angle) * 3.7, 11, enemy["color"]))
            elif pattern == "fan":
                shot_count = 5 + 2 * int(4 * boss_difficulty_progress(round_num))
                shots = []
                for index in range(shot_count):
                    angle = -0.72 + 1.44 * index / (shot_count - 1)
                    shots.append((None, None, math.sin(angle) * 5.5,
                                  math.cos(angle) * 5.5, 10, enemy["color"]))
            elif pattern in (
                "aimed", "double_lance", "heavy_orb", "triple_burst", "homing",
                "wave_shot", "splitter", "sniper", "bouncer", "ricochet",
            ):
                speed = {
                    "aimed": 8,
                    "double_lance": 11,
                    "heavy_orb": 4.8,
                    "triple_burst": 9,
                    "homing": 5.5,
                    "wave_shot": 7,
                    "splitter": 6,
                    "sniper": 13,
                    "bouncer": 7,
                    "ricochet": 7,
                }[pattern]
                speed *= 1.0 + 0.16 * boss_difficulty_progress(round_num)
                velocity_x, velocity_y = aimed_velocity(
                    origin_x, origin_y, boss_targets, speed
                )
                if pattern == "aimed":
                    shot_count = 3 + 2 * int(boss_difficulty_progress(round_num) >= .55)
                    spreads = [-0.24 + 0.48 * index / (shot_count - 1) for index in range(shot_count)]
                    shots = []
                    for spread in spreads:
                        rotated_x = velocity_x * math.cos(spread) - velocity_y * math.sin(spread)
                        rotated_y = velocity_x * math.sin(spread) + velocity_y * math.cos(spread)
                        shots.append((origin_x, origin_y, rotated_x, rotated_y, 12, enemy["color"]))
                elif pattern == "double_lance":
                    shots = []
                    for spread in (-0.12, 0.12):
                        rotated_x = velocity_x * math.cos(spread) - velocity_y * math.sin(spread)
                        rotated_y = velocity_x * math.sin(spread) + velocity_y * math.cos(spread)
                        shots.append((origin_x, origin_y, rotated_x, rotated_y, 11, enemy["color"]))
                elif pattern == "heavy_orb":
                    shots = [(origin_x, origin_y, velocity_x, velocity_y, 28, enemy["color"])]
                elif pattern == "triple_burst":
                    shots = []
                    for spread in (-0.08, 0, 0.08):
                        rotated_x = velocity_x * math.cos(spread) - velocity_y * math.sin(spread)
                        rotated_y = velocity_x * math.sin(spread) + velocity_y * math.cos(spread)
                        shots.append((origin_x, origin_y, rotated_x, rotated_y, 10, enemy["color"]))
                elif pattern == "homing":
                    shots = [(origin_x, origin_y, velocity_x, velocity_y, 11, enemy["color"],
                              {"homing": True, "homing_speed": 5.5,
                               "homing_turn_rate": 0.025, "lifetime": 150,
                               "homing_target_index": (
                                   random.randrange(len(boss_targets))
                                   if boss_targets else None
                               )})]
                elif pattern == "wave_shot":
                    shots = [(origin_x, origin_y, velocity_x, velocity_y, 10, enemy["color"],
                              {"wave": True, "wave_phase": 0.0})]
                elif pattern == "splitter":
                    shots = [(origin_x, origin_y, velocity_x, velocity_y, 16, enemy["color"],
                              {"split_timer": 50, "split_count": 5})]
                elif pattern == "sniper":
                    shots = [(origin_x, origin_y, velocity_x, velocity_y, 12, enemy["color"])]
                elif pattern == "bouncer":
                    shots = [(origin_x, origin_y, velocity_x, velocity_y, 13, enemy["color"],
                              {"bounces_left": 3})]
                else:
                    shots = []
                    for spread in (-0.18, 0, 0.18):
                        rotated_x = velocity_x * math.cos(spread) - velocity_y * math.sin(spread)
                        rotated_y = velocity_x * math.sin(spread) + velocity_y * math.cos(spread)
                        shots.append((origin_x, origin_y, rotated_x, rotated_y, 11, enemy["color"],
                                      {"bounces_left": 2}))
            elif pattern == "curtain":
                target_x = choose_target_position(
                    boss_targets, (origin_x, SCREEN_HEIGHT - 40)
                )[0]
                progress = boss_difficulty_progress(round_num)
                shots = [
                    (lane_x, origin_y, 0, 4.5 + 0.4 * progress,
                     18 + round(4 * progress), enemy["color"])
                    for lane_x in boss_lane_positions(target_x, round_num)
                ]
            elif pattern == "spiral":
                shot_count = 12 + 2 * int(3 * boss_difficulty_progress(round_num))
                shots = []
                for index in range(shot_count):
                    angle = -math.pi / 2 + 2 * math.pi * index / shot_count
                    shots.append((None, None, math.cos(angle) * 5.5,
                                  math.sin(angle) * 5.5, 10, enemy["color"]))
            elif pattern == "crossfire":
                target_x, target_y = choose_target_position(
                    boss_targets, (origin_x, SCREEN_HEIGHT - 40)
                )
                shots = []
                for side in (-1, 1):
                    shot_x = origin_x + side * enemy["rect"].width / 2
                    velocity_x, velocity_y = aimed_velocity(shot_x, origin_y, [(target_x, target_y)], 7)
                    shots.append((shot_x, origin_y, velocity_x, velocity_y, 12, enemy["color"]))
            elif pattern == "sweep":
                shots = []
                for index in range(9):
                    angle = -1.0 + index * 0.25
                    shots.append((None, None, math.sin(angle) * 5.5,
                                  math.cos(angle) * 5.5, 9, enemy["color"]))
            elif pattern == "minefield":
                target_x = choose_target_position(
                    boss_targets, (origin_x, SCREEN_HEIGHT - 40)
                )[0]
                shots = [
                    (target_x + offset * 38, origin_y, 0, 5, 14, enemy["color"])
                    for offset in range(-3, 4)
                ]
            elif pattern == "pincer":
                shots = []
                for side in (-1, 1):
                    shot_x = origin_x + side * enemy["rect"].width / 2
                    velocity_x, velocity_y = aimed_velocity(shot_x, origin_y, boss_targets, 7)
                    shots.append((shot_x, origin_y, velocity_x, velocity_y, 13, enemy["color"]))
            elif pattern == "mine_burst":
                target_x = choose_target_position(
                    boss_targets, (origin_x, SCREEN_HEIGHT - 40)
                )[0]
                shots = [(target_x, origin_y, 0, 0, 17, enemy["color"], {"mine_timer": 54})]
            elif pattern == "zigzag":
                velocity_x, velocity_y = aimed_velocity(origin_x, origin_y, boss_targets, 7.5)
                shots = [(origin_x, origin_y, velocity_x, velocity_y, 11, enemy["color"],
                          {"wave": True, "wave_phase": 0.0,
                           "wave_amplitude": 9, "wave_rate": 0.34})]
            elif pattern == "double_wave":
                velocity_x, velocity_y = aimed_velocity(origin_x, origin_y, boss_targets, 6)
                shots = [
                    (origin_x + offset, origin_y, velocity_x, velocity_y, 11, enemy["color"],
                     {"wave": True, "wave_phase": phase, "wave_amplitude": 6, "wave_rate": 0.25})
                    for offset, phase in ((-18, 0), (18, math.pi))
                ]
            elif pattern == "cross_lanes":
                target_x = sum(target[0] for target in boss_targets) / len(boss_targets) if boss_targets else origin_x
                progress = boss_difficulty_progress(round_num)
                lanes = boss_lane_positions(target_x, round_num, crossing=True)
                if enemy.get("cross_lane_phase", 0):
                    # Shift alternate barrages toward the playfield center so
                    # the same central parking spot is not always a safe lane.
                    center_x = (lanes[0] + lanes[-1]) / 2
                    shift = (lanes[1] - lanes[0]) / 2
                    center_x += -shift if center_x >= SCREEN_WIDTH / 2 else shift
                    lanes = boss_lane_positions(center_x, round_num, crossing=True)
                enemy["cross_lane_phase"] = 1 - enemy.get("cross_lane_phase", 0)
                shots = [
                    (lane_x, origin_y, -1.7 if index % 2 else 1.7,
                     5.5, 14 + round(4 * progress), enemy["color"])
                    for index, lane_x in enumerate(lanes)
                ]
            elif pattern == "bombardment":
                target_x = min(
                    boss_targets,
                    key=lambda target: (target[0] - origin_x) ** 2 + (target[1] - origin_y) ** 2,
                )[0] if boss_targets else origin_x
                shots = [
                    (target_x + offset * 31, origin_y, 0, 8, 12, enemy["color"])
                    for offset in range(-5, 6)
                ]
            elif pattern == "delayed_ring":
                shots = []
                for index in range(16):
                    angle = math.pi / 16 + 2 * math.pi * index / 16
                    shots.append((None, None, math.cos(angle) * 4.8,
                                  math.sin(angle) * 4.8, 10, enemy["color"]))
            elif pattern == "seeker_pair":
                shots = []
                for side in (-1, 1):
                    shot_x = origin_x + side * enemy["rect"].width / 2
                    velocity_x, velocity_y = aimed_velocity(shot_x, origin_y, boss_targets, 4.5)
                    shots.append((shot_x, origin_y, velocity_x, velocity_y, 12, enemy["color"],
                                  {"homing": True, "homing_speed": 4.5,
                                   "homing_turn_rate": 0.012, "lifetime": 105,
                                   "homing_target_index": (
                                       random.randrange(len(boss_targets))
                                       if boss_targets else None
                                   )}))
            elif pattern == "triad":
                target_x, target_y = choose_target_position(
                    boss_targets, (origin_x, SCREEN_HEIGHT - 40)
                )
                shots = []
                for offset in (-26, 0, 26):
                    shot_x = origin_x + offset
                    velocity_x, velocity_y = aimed_velocity(shot_x, origin_y, [(target_x, target_y)], 8)
                    shots.append((shot_x, origin_y, velocity_x, velocity_y, 11, enemy["color"]))
            elif pattern == "pulse_burst":
                shots = []
                for pulse in range(2):
                    for index in range(12):
                        angle = pulse * math.pi / 12 + 2 * math.pi * index / 12
                        shots.append((None, None, math.cos(angle) * 5.2,
                                      math.sin(angle) * 5.2, 9, enemy["color"]))
            else:
                shots = []
                for index in range(18):
                    angle = 2 * math.pi * index / 18
                    shots.append((None, None, math.cos(angle) * 5.8,
                                  math.sin(angle) * 5.8, 9, enemy["color"]))

            enemy["attack_queue"] = shots
            fire_boss_burst(enemy, enemy_bullets, boss_targets, max_bullets, enemies)
        elif enemy["can_shoot"]:
            salvo_size = ENEMY_SALVO_SIZES.get(enemy["type"], 1)
            aimed_attack = enemy["type"] in AIMED_ENEMY_TYPES
            if (len(enemy_bullets) + salvo_size <= max_bullets
                    and now >= enemy.get("next_fire_ms", 0)
                    and (not aimed_attack or now >= next_aimed_volley_ms)
                    and random.random() < enemy_fire_probability(
                        enemy["type"], round_num, active_players)):
                # Spaced-out attacks prevent one fast-moving enemy from firing
                # overlapping multi-shot patterns in a very short burst.
                enemy["next_fire_ms"] = now + random.randint(
                    1450, 2300) if enemy["type"] in ENEMY_HEAVY_SHOOTERS else now + random.randint(650, 1100)
                animate_ship_fire(enemy)
                first_new_shot = len(enemy_bullets)
                if aimed_attack:
                    next_aimed_volley_ms = now + AIMED_VOLLEY_SPACING_MS
                origin_x = enemy["rect"].centerx
                origin_y = enemy["rect"].bottom + 5
                if enemy["type"] == "volley":
                    velocity_x, velocity_y = aimed_velocity(
                        origin_x, origin_y, target_positions, 6
                    )
                    shots = []
                    for spread in (-0.22, 0, 0.22):
                        rotated_x = velocity_x * math.cos(spread) - velocity_y * math.sin(spread)
                        rotated_y = velocity_x * math.sin(spread) + velocity_y * math.cos(spread)
                        shots.append((origin_x, origin_y, rotated_x, rotated_y))
                    for shot_x, shot_y, dx, dy in shots:
                        enemy_bullets.append(create_enemy_projectile(
                            shot_x, shot_y, dx, dy, 9, enemy["color"]
                        ))
                elif enemy["type"] == "mine_layer":
                    for shot_offset in (-34, 34):
                        mine = create_enemy_projectile(
                            origin_x + shot_offset, origin_y, 0, 2.8, 12, enemy["color"]
                        )
                        mine["mine_timer"] = 75
                        mine["mine_count"] = 5
                        enemy_bullets.append(mine)
                elif enemy["type"] == "seeker":
                    dx, dy = aimed_velocity(origin_x, origin_y, target_positions, 5)
                    shot = create_enemy_projectile(
                        origin_x, origin_y, dx, dy, 10, enemy["color"]
                    )
                    shot.update({
                        "homing": True,
                        "homing_speed": 5,
                        "homing_turn_rate": 0.025,
                        "lifetime": 165,
                        "homing_target_index": (
                            random.randrange(len(target_positions)) if target_positions else None
                        ),
                    })
                    enemy_bullets.append(shot)
                elif enemy["type"] == "ricochet":
                    dx, dy = aimed_velocity(origin_x, origin_y, target_positions, 7)
                    shot = create_enemy_projectile(
                        origin_x, origin_y, dx, dy, 10, enemy["color"]
                    )
                    shot["bounces_left"] = 2
                    enemy_bullets.append(shot)
                elif enemy["type"] == "prism":
                    dx, dy = aimed_velocity(origin_x, origin_y, target_positions, 5.5)
                    shot = create_enemy_projectile(
                        origin_x, origin_y, dx, dy, 14, enemy["color"]
                    )
                    shot["split_timer"] = 55
                    shot["split_count"] = 7
                    enemy_bullets.append(shot)
                elif enemy["type"] == "pulse":
                    for index in range(6):
                        angle = math.tau * index / 6
                        enemy_bullets.append(create_enemy_projectile(
                            origin_x,
                            origin_y,
                            math.cos(angle) * 4,
                            math.sin(angle) * 4,
                            9,
                            enemy["color"],
                        ))
                elif enemy["type"] == "charger":
                    dx, dy = aimed_velocity(origin_x, origin_y, target_positions, 7)
                    enemy_bullets.append(create_enemy_projectile(
                        origin_x, origin_y, dx, dy, 8, enemy["color"]
                    ))
                elif enemy["type"] == "scatterer":
                    shots = []
                    for index in range(5):
                        angle = -0.65 + 1.3 * index / 4
                        shots.append((math.sin(angle) * 5, math.cos(angle) * 5))
                    for dx, dy in shots:
                        enemy_bullets.append(create_enemy_projectile(
                            origin_x, origin_y, dx, dy, 9, enemy["color"]
                        ))
                elif enemy["type"] == "phantom":
                    dx, dy = aimed_velocity(origin_x, origin_y, target_positions, 5.5)
                    shot = create_enemy_projectile(
                        origin_x, origin_y, dx, dy, 10, enemy["color"]
                    )
                    shot.update({"wave": True, "wave_phase": 0.0,
                                 "wave_amplitude": 4.5, "wave_rate": 0.3})
                    enemy_bullets.append(shot)
                elif enemy["type"] == "sniper":
                    dx, dy = aimed_velocity(origin_x, origin_y, target_positions, 10)
                    enemy_bullets.append(create_enemy_projectile(
                        origin_x, origin_y, dx, dy, 10, enemy["color"]
                    ))
                elif enemy["type"] == "artillery":
                    dx, dy = aimed_velocity(origin_x, origin_y, target_positions, 5.5)
                    enemy_bullets.append(create_enemy_projectile(
                        origin_x, origin_y, dx, dy, 16, enemy["color"]
                    ))
                elif enemy["type"] == "striker":
                    dx, dy = aimed_velocity(origin_x, origin_y, target_positions, 6.5)
                    enemy_bullets.append(create_enemy_projectile(
                        origin_x, origin_y, dx, dy, 8, enemy["color"]
                    ))
                elif enemy["type"] == "lancer":
                    for shot_offset in (-8, 8):
                        shot_x = origin_x + shot_offset
                        dx, dy = aimed_velocity(shot_x, origin_y, target_positions, 7.5)
                        enemy_bullets.append(create_enemy_projectile(
                            shot_x, origin_y, dx, dy, 8, enemy["color"]
                        ))
                elif enemy["type"] == "bomber":
                    mine = create_enemy_projectile(
                        origin_x, origin_y, 0, 3.5, 16, enemy["color"]
                    )
                    mine["mine_timer"] = 90
                    enemy_bullets.append(mine)
                else:
                    enemy_bullets.append(create_enemy_projectile(
                        origin_x, origin_y, 0, 5, color=enemy["color"]
                    ))
                if aimed_attack:
                    for shot in enemy_bullets[first_new_shot:]:
                        shot["aimed_shot"] = True
                        shot["aimed_fired_ms"] = now

    for bullet in enemy_bullets[:]:
        slowdown_factor = bullet.get("permanent_slow_factor", 1.0)
        for player in players:
            if (player["bullet_time_until"] > now and not player["eliminated"]
                    and player["respawn_until"] <= now):
                center_x = player["x"] + PLAYER_WIDTH / 2
                center_y = player["y"] + PLAYER_HEIGHT / 2
                if math.hypot(bullet["rect"].centerx - center_x, bullet["rect"].centery - center_y) <= BULLET_TIME_RADIUS:
                    if bullet.get("laser_state") is None:
                        # This flag remains on the projectile for its entire life,
                        # even after it exits the field or Bullet Time expires.
                        bullet["permanent_slow_factor"] = min(
                            bullet.get("permanent_slow_factor", 1.0), BULLET_TIME_SLOWDOWN)
                        slowdown_factor = bullet["permanent_slow_factor"]
                        collect_bullet_momentum(bullet, player, now, particles)
                    # Other pilots in overlapping fields also earn a charge.

        if "laser_state" in bullet:
            bullet["remaining_frames"] -= 1
            if bullet["remaining_frames"] <= 0:
                if bullet["laser_state"] == "warning":
                    bullet["laser_state"] = "active"
                    bullet["remaining_frames"] = BOSS_LASER_ACTIVE_FRAMES
                else:
                    enemy_bullets.remove(bullet)
            continue

        if "split_timer" in bullet:
            bullet["split_timer"] -= 1
            if bullet["split_timer"] <= 0:
                center_x = bullet["rect"].centerx
                center_y = bullet["rect"].centery
                split_count = bullet["split_count"]
                enemy_bullets.remove(bullet)
                available = max(0, max_bullets - len(enemy_bullets))
                for index in range(min(split_count, available)):
                    angle = 2 * math.pi * index / split_count
                    enemy_bullets.append(create_enemy_projectile(
                        center_x, center_y, math.cos(angle) * 5,
                        math.sin(angle) * 5, 8, bullet["color"],
                    ))
                continue

        if "mine_timer" in bullet:
            bullet["mine_timer"] -= 1
            if bullet["mine_timer"] <= 0:
                center_x = bullet["rect"].centerx
                center_y = bullet["rect"].centery
                enemy_bullets.remove(bullet)
                mine_count = bullet.get("mine_count", 10)
                available = max(0, max_bullets - len(enemy_bullets))
                for index in range(min(mine_count, available)):
                    angle = 2 * math.pi * index / mine_count
                    enemy_bullets.append(create_enemy_projectile(
                        center_x, center_y, math.cos(angle) * 4.5,
                        math.sin(angle) * 4.5, 9, bullet["color"],
                    ))
                continue

        if bullet.get("homing"):
            bullet["lifetime"] -= 1
            if bullet["lifetime"] <= 0:
                enemy_bullets.remove(bullet)
                continue

            if target_positions:
                target_index = bullet.get("homing_target_index")
                if target_index is None:
                    target_index = random.randrange(len(target_positions))
                    bullet["homing_target_index"] = target_index
                target_x, target_y = target_positions[target_index % len(target_positions)]
                direction_x = target_x - bullet["rect"].centerx
                direction_y = target_y - bullet["rect"].centery
                distance = max(1, math.hypot(direction_x, direction_y))
                speed = bullet["homing_speed"] * ENEMY_PROJECTILE_SPEED_MULTIPLIER
                turn_rate = bullet["homing_turn_rate"]
                bullet["dx"] += (direction_x / distance * speed - bullet["dx"]) * turn_rate
                bullet["dy"] += (direction_y / distance * speed - bullet["dy"]) * turn_rate

        bend_projectile_from_gravity(bullet, players, now)
        if bullet.get("wave"):
            bullet["wave_phase"] += bullet.get("wave_rate", 0.22)
            wave_offset = math.sin(bullet["wave_phase"]) * bullet.get("wave_amplitude", 3.5)
            velocity_x = bullet["dx"] + wave_offset
        else:
            velocity_x = bullet["dx"]
        if bullet.get("homing"):
            update_homing_heading(bullet, velocity_x, bullet["dy"], resize_hitbox=False)
        # Preserve subpixel motion; slow and nearly vertical shots must not stall.
        bullet["x"] = bullet.get("x", float(bullet["rect"].x)) + velocity_x * slowdown_factor
        bullet["y"] = bullet.get("y", float(bullet["rect"].y)) + bullet["dy"] * slowdown_factor
        bullet["rect"].x = round(bullet["x"])
        bullet["rect"].y = round(bullet["y"])

        if bullet["rect"].left < 0 or bullet["rect"].right > SCREEN_WIDTH:
            if bullet.get("bounces_left", 0) > 0:
                bullet["bounces_left"] -= 1
                bullet["dx"] *= -1
                bullet["rect"].left = max(0, bullet["rect"].left)
                bullet["rect"].right = min(SCREEN_WIDTH, bullet["rect"].right)
                bullet["x"] = float(bullet["rect"].x)
            else:
                enemy_bullets.remove(bullet)
                continue

        if bullet["rect"].top > SCREEN_HEIGHT or bullet["rect"].bottom < 0:
            enemy_bullets.remove(bullet)


def assign_laser_homing_targets(beams, enemies, player):
    """Branch each piercing laser toward a different visible enemy if possible.

    The full-height original laser remains intact. Target references are refreshed
    every frame, so a dead enemy can never permanently trap a homing beam.
    """
    available = [e for e in enemies if enemy_is_visible(e)
                 and e["rect"].centery < player["y"]]
    claimed = set()
    for beam in beams:
        beam["homing_target"] = None
        if not beam.get("homing") or not available:
            continue
        # Favor enemies nearest to the beam; evenly distribute a triple volley.
        choices = [e for e in available if id(e) not in claimed] or available
        best = min(choices, key=lambda enemy:
                   abs(enemy["rect"].centerx - beam["rect"].centerx)
                   + 0.10 * abs(enemy["rect"].centery - beam["rect"].centery))
        beam["homing_target"] = best
        claimed.add(id(best))


def laser_homing_points(beam, time_ms):
    """A gently animated energy tendril from the main beam to its locked enemy."""
    target = beam.get("homing_target")
    if target is None:
        return ()
    x0 = beam["rect"].centerx
    x1, y1 = target["rect"].center
    y0 = max(GAMEPLAY_TOP + 3, min(beam["rect"].bottom - 10, y1 + 35))
    if abs(x0 - x1) < 7:
        return ((x0, y0), (x1, y1))
    points = []
    for index in range(9):
        t = index / 8
        wave = math.sin(t * math.pi) * math.sin(time_ms / 115 + index * 1.7) * 6
        points.append((round(x0 + (x1 - x0) * t),
                       round(y0 + (y1 - y0) * t + wave)))
    return tuple(points)


def player_laser_rect(player, shot_offset=0):
    # A charged laser reaches the very top of the playfield, including bosses.
    beam_bottom = max(0, int(round(player["y"])))
    return pygame.Rect(
        int(round(player["x"] + PLAYER_WIDTH / 2 - 5 + shot_offset)),
        0,
        10,
        beam_bottom,
    )


def update_homing_heading(bullet, velocity_x, velocity_y, resize_hitbox=True):
    """Face the actual travel direction; keep a rotated shot's hitbox centered."""
    if math.hypot(velocity_x, velocity_y) < 0.001:
        return
    bullet["heading"] = math.atan2(velocity_y, velocity_x)
    if not resize_hitbox:
        return
    rect = bullet["rect"]
    width, height = bullet.setdefault("projectile_base_size", rect.size)
    unit_x, unit_y = math.cos(bullet["heading"]), math.sin(bullet["heading"])
    rotated_width = max(1, math.ceil(abs(height * unit_x) + abs(width * unit_y) - 1e-9))
    rotated_height = max(1, math.ceil(abs(height * unit_y) + abs(width * unit_x) - 1e-9))
    center = rect.center
    rect.size = (rotated_width, rotated_height)
    rect.center = center


def player_weapon_cooldown(player, active_count, now, weapon="normal"):
    """Scale co-op firepower gently while keeping each gun slower than solo."""
    delay = BASE_SHOT_COOLDOWN * (1 + COOP_FIRE_COOLDOWN_STEP * max(0, active_count - 1))
    if weapon == "bomb":
        delay *= 1.65
    elif weapon == "laser":
        # Lasers are a powerful short-lived pickup, not a slow normal gun.
        # Additional pilots increase the interval modestly, without making
        # the beam weak in co-op or multiplying firepower fourfold.
        delay = 7 + 4 * (max(1, active_count) - 1)
    rapid_multiplier = 1.0
    if player["rapid_fire_until"] > now:
        if weapon == "laser":
            # Strengthen pulses without bypassing the minimum laser interval.
            rapid_multiplier = RAPID_FIRE_LASER_MULTIPLIER
        else:
            pilot_index = min(max(int(active_count), 1), len(RAPID_FIRE_MULTIPLIERS)) - 1
            rapid_multiplier = RAPID_FIRE_MULTIPLIERS[pilot_index]
    # Each pickup keeps its full solo benefit. Overlapping fire-rate bonuses
    # add their extra rate instead of multiplying into instant boss kills.
    delay /= rapid_multiplier + powerup_fire_bonus(player, now)
    return max(2 if weapon == "laser" else 3, math.ceil(delay))


ORBIT_SHOT_INTERVAL_FRAMES = 28
ORBIT_PROJECTILES_PER_PILOT = 6


def primary_shot_damage(player, now):
    """Snapshot the equipped weapon's base damage, without its special effects."""
    if player.get("laser_until", 0) > now or player.get("bomb_until", 0) > now:
        base_damage = 3
    elif player.get("piercing_until", 0) > now:
        base_damage = 2
    else:
        base_damage = 1
    return base_damage + player.get("damage_bonus", 0)


def orbit_drone_positions(player, now):
    center_x = player["x"] + PLAYER_WIDTH / 2
    center_y = player["y"] + PLAYER_HEIGHT / 2
    phase = now / 340
    return tuple((round(center_x + math.cos(phase + index * math.pi) * 39),
                  round(center_y + math.sin(phase + index * math.pi) * 24))
                 for index in range(2))


def update_orbit_drones(players, player_bullets, active_count, now):
    """Two support emitters inherit per-hit damage, with independent rate/caps."""
    for player in players:
        if (player.get("orbit_until", 0) <= now or player["eliminated"]
                or player["respawn_until"] > now):
            player["orbit_cooldown"] = 0
            continue
        player["orbit_cooldown"] = max(0, player.get("orbit_cooldown", 0) - 1)
        if player["orbit_cooldown"]:
            continue
        existing = sum(isinstance(shot, dict) and shot.get("orbit_drone", False)
                       and shot.get("owner") == player["number"] for shot in player_bullets)
        available = min(max(0, ORBIT_PROJECTILES_PER_PILOT - existing),
                        max(0, SUPPORT_PROJECTILE_CAP - support_projectile_count(player_bullets)))
        for x, y in orbit_drone_positions(player, now)[:available]:
            player_bullets.append({
                "rect": pygame.Rect(max(0, min(SCREEN_WIDTH - 4, x - 2)), y - 9, 4, 10),
                "type": "normal", "owner": player["number"], "color": UI_CYAN,
                "damage": primary_shot_damage(player, now),
                "pierce_remaining": 0, "hit_enemies": set(),
                "orbit_drone": True, "support_shot": True, "chain_eligible": False,
                "lightning": False, "homing": False,
            })
        # Rapid fire, momentum and Triple Shot do not multiply support fire.
        player["orbit_cooldown"] = ORBIT_SHOT_INTERVAL_FRAMES * max(1, active_count)


def update_player_projectiles(keys, players, player_count, player_bullets, enemies=()):
    now = pygame.time.get_ticks()
    audio = ensure_audio_manager()
    active_count = max(1, sum(not p["eliminated"] and p["respawn_until"] == 0 for p in players))
    update_orbit_drones(players, player_bullets, active_count, now)

    for player in players:
        consume_support_powerups(player, players, enemies, player_bullets)
        if player["cooldown"] > 0:
            player["cooldown"] -= 1

        cooldown_frames = player_weapon_cooldown(player, active_count, now)
        weapon = "laser" if player["laser_until"] > now else "bomb" if player["bomb_until"] > now else "normal"
        player["cooldown"] = min(player["cooldown"], player_weapon_cooldown(player, active_count, now, weapon))
        is_active = not player["eliminated"] and player["respawn_until"] == 0
        pending_reflections = player.setdefault("pending_reflections", [])
        if is_active:
            available = max(0, SUPPORT_PROJECTILE_CAP - support_projectile_count(player_bullets))
            emitted = min(available, len(pending_reflections))
            player_bullets.extend(pending_reflections[:emitted])
            del pending_reflections[:emitted]
        else:
            pending_reflections.clear()
        shoot_keys = PLAYER_CONTROLS[player["number"] - 1][4]
        auto_fire = PLAYER_AUTOFIRE[player["number"] - 1] and (
            not isinstance(keys, HeldInput) or keys.focused)
        fire_pressed = is_active and (auto_fire or (keys.fire_requested(shoot_keys, now)
            if isinstance(keys, HeldInput) else any(keys[key] for key in shoot_keys)))
        if not is_active and isinstance(keys, HeldInput):
            keys.consume_fire(shoot_keys)

        if player["laser_until"] > now:
            existing_beams = [
                bullet for bullet in player_bullets
                if isinstance(bullet, dict)
                and bullet.get("type") == "laser"
                and bullet.get("owner") == player["number"]
            ]
            if fire_pressed:
                shot_offsets = (-15, 0, 15) if player["triple_shot_until"] > now else (0,)
                pulse_ready = player["cooldown"] == 0
                # Each beam deals solid damage. Triple shot adds real lanes
                # rather than reducing a great laser into weak beams.
                laser_damage = 3 + player.get("damage_bonus", 0)
                if pulse_ready:
                    animate_ship_fire(player, shot_offsets)
                    player["cooldown"] = player_weapon_cooldown(player, active_count, now, "laser")
                    if isinstance(keys, HeldInput):
                        keys.consume_fire(shoot_keys)
                pulse_lightning_used = set()
                for beam_index, shot_offset in enumerate(shot_offsets):
                    if beam_index < len(existing_beams):
                        beam = existing_beams[beam_index]
                        beam["offset"] = shot_offset
                        beam["rect"] = player_laser_rect(player, shot_offset)
                        beam["damage"] = laser_damage
                        beam["damage_ready"] = pulse_ready
                        beam["homing"] = player["homing_until"] > now
                        beam["lightning"] = player["lightning_until"] > now
                        beam["volley_lightning_used"] = pulse_lightning_used
                        beam["cryo"] = player.get("cryo_until", 0) > now
                        beam["lightning_chained"] = False if pulse_ready else beam.get("lightning_chained", False)
                    else:
                        player_bullets.append({
                            "rect": player_laser_rect(player, shot_offset),
                            "type": "laser",
                            "owner": player["number"],
                            "color": player["color"],
                            "offset": shot_offset,
                            "damage": laser_damage,
                            "damage_ready": pulse_ready,
                            "homing": player["homing_until"] > now,
                            "lightning": player["lightning_until"] > now,
                            "volley_lightning_used": pulse_lightning_used,
                            "cryo": player.get("cryo_until", 0) > now,
                            "lightning_chained": False,
                        })
                # Keep the existing full-height piercing beams AND attach a
                # living, retargetable homing arc when both pickups are active.
                active_beams = [b for b in player_bullets
                                if isinstance(b, dict) and b.get("type") == "laser"
                                and b.get("owner") == player["number"]]
                assign_laser_homing_targets(active_beams[:len(shot_offsets)], enemies, player)
                for beam in existing_beams[len(shot_offsets):]:
                    player_bullets.remove(beam)
            else:
                for beam in existing_beams:
                    player_bullets.remove(beam)
            continue

        for bullet in player_bullets[:]:
            if isinstance(bullet, dict) and bullet.get("type") == "laser" and bullet.get("owner") == player["number"]:
                player_bullets.remove(bullet)

        if is_active and player["cooldown"] == 0 and fire_pressed:
            if isinstance(keys, HeldInput):
                keys.consume_fire(shoot_keys)
            if player["bomb_until"] > now:
                shot_offsets = (-12, 0, 12) if player["triple_shot_until"] > now else (0,)
                animate_ship_fire(player, shot_offsets)
                volley_hits = set()
                volley_lightning_used = set()
                for shot_offset in shot_offsets:
                    player_bullets.append({
                        "rect": pygame.Rect(
                            player["x"] + PLAYER_WIDTH // 2 - 8 + shot_offset,
                            player["y"] - 10,
                            16,
                            18,
                        ),
                        "type": "bomb",
                        "color": player["color"],
                        "damage": 3 + player.get("damage_bonus", 0),
                        "blast_radius": BOMB_BLAST_RADIUS,
                        "volley_hits": volley_hits,
                        "volley_lightning_used": volley_lightning_used,
                        "homing": player["homing_until"] > now,
                        "lightning": player["lightning_until"] > now,
                        "cryo": player.get("cryo_until", 0) > now,
                        "owner": player["number"],
                    })
                player["cooldown"] = player_weapon_cooldown(player, active_count, now, "bomb")
                if audio is not None:
                    audio.play(audio.shoot)
            else:
                bullet_width = 8 if player["piercing_until"] > now else 6
                shot_offsets = (-10, 0, 10) if player["triple_shot_until"] > now else (0,)
                animate_ship_fire(player, shot_offsets)
                for shot_offset in shot_offsets:
                    shot = {
                        "rect": pygame.Rect(
                            player["x"] + (PLAYER_WIDTH // 2) - bullet_width // 2 + shot_offset,
                            player["y"],
                            bullet_width,
                            12,
                        ),
                        "type": "normal",
                        "color": player["color"],
                        "damage": (2 if player["piercing_until"] > now else 1)
                        + player.get("damage_bonus", 0),
                        "pierce_remaining": 3 if player["piercing_until"] > now else 0,
                        "hit_enemies": set(),
                        "homing": player["homing_until"] > now,
                        "lightning": player["lightning_until"] > now,
                        "cryo": player.get("cryo_until", 0) > now,
                        "owner": player["number"],
                    }
                    player_bullets.append(shot)
                player["cooldown"] = cooldown_frames
                if audio is not None:
                    audio.play(audio.shoot)

    homing_target_bounds = pygame.Rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT)
    for bullet in player_bullets[:]:
        if isinstance(bullet, dict) and bullet.get("type") == "laser":
            owner_num = bullet.get("owner")
            owner = next((player for player in players if player["number"] == owner_num), None)
            if owner is None:
                player_bullets.remove(bullet)
                continue
            bullet["rect"] = player_laser_rect(owner, bullet.get("offset", 0))
            continue

        bullet_rect = bullet["rect"] if isinstance(bullet, dict) else bullet
        if isinstance(bullet, dict) and "lifetime" in bullet:
            bullet["lifetime"] -= 1
            if bullet["lifetime"] <= 0:
                player_bullets.remove(bullet)
                continue
        if isinstance(bullet, dict) and ("vx" in bullet or "vy" in bullet):
            bullet["x"] = bullet.get("x", float(bullet_rect.x)) + bullet.get("vx", 0)
            bullet["y"] = bullet.get("y", float(bullet_rect.y)) + bullet.get("vy", -12)
            bullet_rect.x, bullet_rect.y = round(bullet["x"]), round(bullet["y"])
            if (bullet_rect.right < 0 or bullet_rect.left > SCREEN_WIDTH
                    or bullet_rect.bottom < 0 or bullet_rect.top > SCREEN_HEIGHT):
                player_bullets.remove(bullet)
            continue
        # Never track an already-hit target with a piercing homing shot: it
        # could orbit that invulnerable-to-this-bullet enemy forever.
        candidates = (
            [enemy for enemy in enemies if enemy["hp"] > 0 and enemy_is_visible(enemy)
             and enemy["rect"].colliderect(homing_target_bounds)
             and id(enemy) not in bullet.get("hit_enemies", ())]
            if isinstance(bullet, dict) and bullet.get("homing") else []
        )
        preferred = bullet.get("support_target") if isinstance(bullet, dict) else None
        if preferred is not None and any(enemy is preferred for enemy in candidates):
            candidates = [preferred]
        if candidates:
            target = min(
                candidates,
                key=lambda enemy: (enemy["rect"].centerx - bullet_rect.centerx) ** 2
                + (enemy["rect"].centery - bullet_rect.centery) ** 2,
            )
            direction_x = target["rect"].centerx - bullet_rect.centerx
            direction_y = target["rect"].centery - bullet_rect.centery
            distance = max(1, math.hypot(direction_x, direction_y))
            move_x = round(direction_x / distance * 12)
            move_y = round(direction_y / distance * 12)
            bullet_rect.x += move_x
            bullet_rect.y += move_y
        else:
            move_x, move_y = 0, -12
            bullet_rect.y -= 12
        if isinstance(bullet, dict) and bullet.get("homing"):
            update_homing_heading(bullet, move_x, move_y)
        if isinstance(bullet, dict) and bullet.get("type") == "bomb" and not bullet.get("homing"):
            bullet_rect.y -= 4
        if (bullet_rect.bottom < 0
                or (isinstance(bullet, dict) and bullet.get("homing")
                    and (bullet_rect.top > SCREEN_HEIGHT or bullet_rect.right < 0
                         or bullet_rect.left > SCREEN_WIDTH))):
            player_bullets.remove(bullet)


SUPPORT_PROJECTILE_CAP = 24
CHAIN_REACTION_QUEUE_CAP = 24


def support_projectile_count(player_bullets):
    return sum(isinstance(shot, dict) and shot.get("support_shot", False)
               for shot in player_bullets)


def consume_support_powerups(player, players, enemies, player_bullets):
    """Flush bounded first-generation shrapnel on the next projectile update."""
    pending = player.setdefault("pending_chain_shots", [])
    if player.get("eliminated") or player.get("respawn_until", 0) > pygame.time.get_ticks():
        pending.clear()
        return
    available = max(0, SUPPORT_PROJECTILE_CAP - support_projectile_count(player_bullets))
    player_bullets.extend(pending[:available])
    # These are short-lived death effects, not ammunition banked behind a cap.
    pending.clear()


def nova_countdown(player, now):
    """Show one second each of 3, 2 and 1 before the charged pulse fires."""
    if (not player.get("pending_nova", False) or player.get("eliminated", False)
            or player.get("respawn_until", 0) > now):
        return 0
    remaining = player.get("nova_charge_until", 0) - now
    return min(NOVA_COUNTDOWN_MS // 1000, max(0, math.ceil(remaining / 1000)))


def resolve_instant_powerups(players, enemies, enemy_bullets, player_bullets, powerups, particles):
    """Resolve charged Nova pulses and stored missiles with reward context."""
    now = pygame.time.get_ticks()
    for player in players:
        if player.get("eliminated") or player.get("respawn_until", 0) > now:
            continue
        center = (player["x"] + PLAYER_WIDTH / 2, player["y"] + PLAYER_HEIGHT / 2)
        if player.get("pending_nova"):
            if not player.get("nova_charge_until", 0):
                # Also accept an older in-memory pending flag as a fresh charge.
                player["nova_charge_until"] = now + NOVA_COUNTDOWN_MS
            if now >= player["nova_charge_until"]:
                player["pending_nova"] = False
                player["nova_charge_until"] = 0
                particles.append({"kind": "nova_pulse", "x": center[0], "y": center[1],
                                  "dx": 0, "dy": 0, "radius": NOVA_PULSE_RADIUS,
                                  "color": POWERUP_COLORS["nova_pulse"],
                                  "lifetime": 30, "max_lifetime": 30})
                # The damaging shock reaches every foe; projectile clearing
                # is local to the larger circle centered on the pilot.
                for enemy in enemies[:]:
                    if enemy["hp"] <= 0:
                        continue
                    damage_enemy(enemy, 1, player["number"], ignore_shields=True)
                    if enemy["hp"] <= 0:
                        enemy["no_chain_reaction"] = True
                        finish_defeated_enemy(enemy, enemies, players, powerups, enemy_bullets, particles)
                # Clear after rewards/death bursts so a volatile foe cannot
                # refill the safe area during this same defensive blast.
                for shot in enemy_bullets[:]:
                    if (shot.get("laser_state") is None
                            and math.dist(center, shot["rect"].center) <= NOVA_PULSE_RADIUS):
                        enemy_bullets.remove(shot)
        if player.get("pending_missiles"):
            targets = sorted((enemy for enemy in enemies
                              if enemy["hp"] > 0 and enemy_is_visible(enemy)),
                             key=lambda enemy: math.dist(center, enemy["rect"].center))
            if not targets:
                continue  # The saved charge waits for the next visible fleet.
            available = min(6, max(0, SUPPORT_PROJECTILE_CAP - support_projectile_count(player_bullets)))
            if not available:
                continue
            player["pending_missiles"] = False
            for index in range(available):
                target = targets[index % len(targets)]
                player_bullets.append({
                    "rect": pygame.Rect(round(center[0] - 4 + (index - 2.5) * 9),
                                        round(player["y"] - 12), 8, 14),
                    "type": "missile", "color": ORANGE, "owner": player["number"],
                    "damage": 1, "pierce_remaining": 0, "hit_enemies": set(),
                    "homing": True, "support_target": target, "lifetime": 150,
                    "lightning": False, "chain_eligible": False, "support_shot": True,
                })


def process_chain_reaction_defeat(enemy, enemies, players):
    """Credit the kill consistently, then queue at most one shrapnel generation."""
    contributions = enemy.get("damage_by_player", {})
    contributors = [player for player in players if contributions.get(player["number"], 0) > 0]
    owner = max(contributors, key=lambda player: contributions[player["number"]], default=None)
    blocked = enemy.pop("no_chain_reaction", False)
    if (owner is None or blocked or owner.get("chain_reaction_until", 0) <= pygame.time.get_ticks()
            or owner.get("eliminated")):
        return owner
    targets = sorted((other for other in enemies if other is not enemy and other["hp"] > 0
                      and enemy_is_visible(other)
                      and math.dist(enemy["rect"].center, other["rect"].center) <= 240),
                     key=lambda other: math.dist(enemy["rect"].center, other["rect"].center))
    if not targets:
        return owner
    pending = owner.setdefault("pending_chain_shots", [])
    origin = enemy["rect"].center
    for index in range(min(3, max(0, CHAIN_REACTION_QUEUE_CAP - len(pending)))):
        target = targets[index % len(targets)]
        dx, dy = target["rect"].centerx - origin[0], target["rect"].centery - origin[1]
        distance = max(1, math.hypot(dx, dy))
        pending.append({"rect": pygame.Rect(origin[0] - 3, origin[1] - 3, 6, 6),
                        "type": "chain_shard", "color": UI_GOLD, "damage": 1,
                        "owner": owner["number"], "vx": dx / distance * 9,
                        "vy": dy / distance * 9, "lifetime": 60,
                        "pierce_remaining": 0, "hit_enemies": set(),
                        "homing": False, "lightning": False,
                        "chain_eligible": False, "support_shot": True})
    return owner


def spawn_enemy_death_burst(enemy, enemies, players, enemy_bullets,
                           count, speed, size, color):
    """Death effects share the same projectile budget as ordinary attacks."""
    now = pygame.time.get_ticks()
    active_count = max(1, sum(not p["eliminated"] and p["respawn_until"] <= now
                              for p in players))
    bosses = [other for other in enemies if other.get("is_boss")]
    round_num = max((boss.get("attack_level", 1) * 5 for boss in bosses), default=1)
    cap = enemy_bullet_cap(active_count, bool(bosses), round_num)
    available = min(count, max(0, cap - len(enemy_bullets)))
    # Distribute a reduced burst over the whole circle, preserving its gaps.
    for index in range(available):
        angle = math.tau * index / available
        enemy_bullets.append(create_enemy_projectile(
            *enemy["rect"].center, math.cos(angle) * speed,
            math.sin(angle) * speed, size, color))


def finish_defeated_enemy(enemy, enemies, players, powerups, enemy_bullets, particles):
    """The ONLY defeat reward path, regardless of projectile type."""
    if enemy not in enemies or enemy["hp"] > 0:
        return
    owner = process_chain_reaction_defeat(enemy, enemies, players)
    now = pygame.time.get_ticks()
    if owner is not None and owner.get("cryo_until", 0) > now:
        grant_shatter(owner, now, enemy["rect"].center, particles)
    supply_boost = owner is not None and owner.get("supply_kills_left", 0) > 0
    if supply_boost:
        owner["supply_kills_left"] -= 1
    origin_x, origin_y = enemy["rect"].center
    spawn_pop_particles(origin_x, origin_y, enemy["color"], particles)
    if enemy.get("is_boss", False):
        # Guardians grant their themed reward directly to every pilot. Regular
        # bosses retain one shared pickup. Life rewards happen at wave completion.
        if sum(bool(other.get("is_boss", False)) for other in enemies) == 1:
            milestone = next((profile for profile in MILESTONE_BOSSES.values()
                              if profile["kind"] == enemy.get("milestone_kind")), None)
            if milestone is None:
                maybe_drop_powerup(powerups, origin_x, origin_y, guaranteed=True)
                spawn_enemy_death_burst(enemy, enemies, players, enemy_bullets,
                                       12, 5, 10, WHITE)
            else:
                # A cleared guardian cannot immediately consume a freshly
                # awarded defense or take away a timed reward on its last shot.
                enemy_bullets.clear()
                grant_milestone_rewards(players, milestone["reward"], enemy_bullets, particles)
    else:
        chance = (MUTATED_POWERUP_DROP_CHANCE if enemy.get("mutation")
                  else NORMAL_POWERUP_DROP_CHANCE)
        if supply_boost:
            chance = min(0.25, chance * 1.6)
        maybe_drop_powerup(powerups, origin_x, origin_y, chance)
    if enemy.get("mutation") == "volatile":
        spawn_enemy_death_burst(enemy, enemies, players, enemy_bullets,
                               8, 4.5, 8, PINK)
    defeat_enemy(enemy, enemies, players)


def grant_milestone_rewards(players, reward, enemy_bullets, particles):
    """Every pilot earns a guardian reward; no race for a falling pickup."""
    now = pygame.time.get_ticks()
    for player in players:
        # A stored Warp cannot stack. Match ordinary pickup overflow behavior
        # and clearly name the actual fallback awarded to an already charged pilot.
        actual = "score_boost" if reward == "emergency_warp" and player.get("warp_ready") else reward
        grant_powerup(player, reward, enemy_bullets)
        player["powerup_notice"] = f"GUARDIAN REWARD: {POWERUP_LABELS[actual]}"
        player["powerup_notice_until"] = now + 3000
        spawn_powerup_pickup_effect(player, actual, particles)


def lightning_chain(bullet, origin_enemy, enemies, players, powerups,
                    enemy_bullets, particles):
    """Guaranteed first arc, then diminishing chances to reach new foes."""
    if not isinstance(bullet, dict) or not bullet.get("lightning"):
        return
    if bullet.get("lightning_chained"):
        return
    shared = bullet.get("volley_lightning_used")
    if shared is not None and shared:
        return
    radius = 210 if bullet.get("homing") else 145
    source = origin_enemy["rect"].center
    visited = set(bullet.get("hit_enemies", ()))
    visited.add(id(origin_enemy))
    for hop, chance in enumerate(LIGHTNING_HOP_CHANCES):
        choices = [e for e in enemies if id(e) not in visited and e["hp"] > 0
                   and math.dist(source, e["rect"].center) <= radius]
        if not choices or (hop > 0 and random.random() >= chance):
            break
        # A piercing shot can try again at its next hit if its first target
        # had nobody within reach. Once an arc happens, the discharge is spent.
        bullet["lightning_chained"] = True
        if shared is not None:
            shared.add("used")
        target = min(choices, key=lambda e: math.dist(source, e["rect"].center))
        visited.add(id(target))
        dest = target["rect"].center
        # Each connector persists independently even when its target dies.
        points = [source]
        for t in (0.25, 0.50, 0.75):
            sway = random.randint(-11, 11)
            points.append((round(source[0] + (dest[0] - source[0]) * t + sway),
                           round(source[1] + (dest[1] - source[1]) * t - sway)))
        points.append(dest)
        particles.append({"kind": "lightning_arc", "x": float(source[0]),
                          "y": float(source[1]), "dx": 0, "dy": 0, "radius": 2,
                          "points": tuple(points), "color": UI_CYAN,
                          "lifetime": 9, "max_lifetime": 9})
        actual_damage = damage_enemy(target, max(1, int(bullet.get("damage", 1) * 0.45)),
                                    bullet.get("owner"))
        if actual_damage > 0:
            apply_cryo_hit(target, bullet)
        if target["hp"] <= 0:
            finish_defeated_enemy(target, enemies, players, powerups,
                                  enemy_bullets, particles)
        source = dest


def powerup_impact_damage(bullet, enemy, base_damage):
    """Heavy pickup attacks execute ordinary foes, respecting boss armor/shields."""
    if (isinstance(bullet, dict) and bullet.get("type") in ("bomb", "missile")
            and not enemy.get("is_boss", False)
            and enemy.get("shield_charges", 0) <= 0):
        return enemy["hp"]
    return base_damage


def check_player_bullet_collisions(player_bullets, enemies, particles, enemy_bullets, powerups, players):
    """Uniform collision rules for normal/piercing/bomb/laser + Lightning."""
    audio = ensure_audio_manager()
    player_colors = {player["number"]: player["color"] for player in players}
    # Three laser lanes widen coverage, but one pilot's pulse hits each boss
    # once. Pick the strongest available lane before resolving any guided arc,
    # so a weaker side arc cannot consume a full-strength direct hit.
    laser_boss_damage = {}
    laser_boss_hits = set()
    bosses = [enemy for enemy in enemies if enemy.get("is_boss", False)]
    for beam in player_bullets:
        if (not isinstance(beam, dict) or beam.get("type") != "laser"
                or not beam.get("damage_ready", False)):
            continue
        for boss in bosses:
            direct = beam["rect"].colliderect(boss["rect"])
            guided = beam.get("homing") and beam.get("homing_target") is boss
            if direct or guided:
                damage = beam.get("damage", 3)
                if guided and not direct:
                    damage = max(1, damage - 1)
                key = (beam.get("owner"), id(boss))
                laser_boss_damage[key] = max(laser_boss_damage.get(key, 0), damage)
    for bullet in player_bullets[:]:
        if bullet not in player_bullets:
            continue
        rect = bullet["rect"] if isinstance(bullet, dict) else bullet
        color = player_projectile_color(bullet, player_colors)
        kind = bullet.get("type", "normal") if isinstance(bullet, dict) else "normal"
        if kind == "laser":
            if not bullet.get("damage_ready", False):
                continue
            bullet["damage_ready"] = False
        for enemy in enemies[:]:
            if enemy not in enemies:
                continue
            if isinstance(bullet, dict) and id(enemy) in bullet.get("hit_enemies", ()):
                continue
            guided = (kind == "laser" and bullet.get("homing")
                      and bullet.get("homing_target") is enemy)
            direct = rect.colliderect(enemy["rect"])
            if not direct and not guided:
                continue
            if kind == "bomb":
                center = rect.center
                if bullet in player_bullets:
                    player_bullets.remove(bullet)
                spawn_pop_particles(*center, color, particles)
                hit_ids = bullet.setdefault("volley_hits", set())
                for other in enemies[:]:
                    if other not in enemies or id(other) in hit_ids:
                        continue
                    if math.dist(center, other["rect"].center) > bullet.get("blast_radius", BOMB_BLAST_RADIUS):
                        continue
                    hit_ids.add(id(other))
                    damage = powerup_impact_damage(bullet, other, bullet.get("damage", 3))
                    actual_damage = damage_enemy(other, damage, bullet.get("owner"))
                    if actual_damage > 0:
                        apply_cryo_hit(other, bullet)
                    spawn_pop_particles(*other["rect"].center, color, particles)
                    # The electric discharge belongs to a whole bomb, not every
                    # enemy in its area; no amplification from three bombs.
                    if not bullet.get("lightning_chained"):
                        lightning_chain(bullet, other, enemies, players, powerups,
                                        enemy_bullets, particles)
                    finish_defeated_enemy(other, enemies, players, powerups,
                                          enemy_bullets, particles)
                break
            damage = bullet.get("damage", 3) if isinstance(bullet, dict) else (2 if rect.width >= 8 else 1)
            if kind == "laser" and guided and not direct:
                damage = max(1, damage - 1)
            if kind == "laser" and enemy.get("is_boss", False):
                key = (bullet.get("owner"), id(enemy))
                if key in laser_boss_hits:
                    continue
                laser_boss_hits.add(key)
                damage = laser_boss_damage[key]
            damage = powerup_impact_damage(bullet, enemy, damage)
            actual_damage = damage_enemy(enemy, damage, bullet.get("owner") if isinstance(bullet, dict) else None)
            if actual_damage > 0:
                apply_cryo_hit(enemy, bullet)
            if (enemy["hp"] <= 0 and isinstance(bullet, dict)
                    and not bullet.get("chain_eligible", True)):
                enemy["no_chain_reaction"] = True
            spawn_pop_particles(*enemy["rect"].center if kind == "laser" else rect.center,
                                color, particles)
            lightning_chain(bullet, enemy, enemies, players, powerups,
                            enemy_bullets, particles)
            finish_defeated_enemy(enemy, enemies, players, powerups,
                                  enemy_bullets, particles)
            if kind == "laser":
                # Laser hits every enemy once per pulse and stays on screen.
                continue
            if isinstance(bullet, dict):
                bullet.setdefault("hit_enemies", set()).add(id(enemy))
            if audio is not None:
                audio.play(audio.hit)
            if isinstance(bullet, dict) and bullet.get("pierce_remaining", 0) > 0:
                bullet["pierce_remaining"] -= 1
                if bullet["pierce_remaining"] > 0:
                    continue
            if bullet in player_bullets:
                player_bullets.remove(bullet)
            break


def draw_exit_button(screen, exit_button_rect, font):
    draw_neon_button(screen, exit_button_rect, "SAVE FILES", font, UI_CORAL)


def draw_pause_button(screen, pause_button_rect, font, paused):
    label = "RESUME" if paused else "PAUSE"
    draw_neon_button(screen, pause_button_rect, label, font, UI_MINT if paused else UI_CYAN)


@ui_scene
def draw_pause_overlay(screen, font, save_error=None):
    overlay = pygame.Surface((SCREEN_WIDTH, SCREEN_HEIGHT), pygame.SRCALPHA)
    overlay.fill((3, 4, 18, 185))
    screen.blit(overlay, (0, 0))
    panel = pygame.Rect(0, 0, min(560, SCREEN_WIDTH - 40), 172)
    panel.center = (SCREEN_WIDTH // 2, max(panel.height // 2 + 12, SCREEN_HEIGHT // 2 - 32))
    draw_neon_panel(screen, panel, UI_VIOLET)
    draw_neon_title(screen, "PAUSED", font, (panel.centerx, panel.y + 46), UI_CYAN)
    note_font = pygame.font.SysFont(None, 24)
    draw_fitted_text(screen, "Autosave failed. Progress may not be saved." if save_error
                     else "Auto-saved at wave start. CONTINUE restarts the wave.",
                     note_font, UI_CORAL if save_error else UI_MUTED,
                     pygame.Rect(panel.x + 16, panel.y + 82, panel.width - 32, 28))
    draw_fitted_text(screen, "Check disk space and folder permissions before quitting." if save_error
                     else "Select RESUME below to return to the fight.", note_font, UI_TEXT,
                     pygame.Rect(panel.x + 16, panel.y + 118, panel.width - 32, 28))


def draw_fitted_text(screen, text, font, color, rect, align="center"):
    """Fit a short label without cropping its contents or its click target."""
    rendered = font.render(str(text), True, color)
    factor = min(1.0, rect.width / max(1, rendered.get_width()),
                 rect.height / max(1, rendered.get_height()))
    if factor < 1:
        rendered = pygame.transform.smoothscale(rendered,
            (max(1, round(rendered.get_width() * factor)),
             max(1, round(rendered.get_height() * factor))))
    destination = rendered.get_rect(center=rect.center)
    if align == "left":
        destination.left = rect.left
    screen.blit(rendered, destination)
    return destination


def compact_menu_layout():
    return SCREEN_WIDTH < 1100 or SCREEN_HEIGHT < 720


def compact_start_layout():
    margin = 20 if SCREEN_WIDTH >= 700 else 14
    low = SCREEN_HEIGHT < 500
    top = 70 if low else 138
    launch = pygame.Rect(margin, top, SCREEN_WIDTH - margin * 2, 104 if low else 142)
    choices = []
    gap = 10
    width = (launch.width - 32 - gap) // 2
    height = 28 if low else 34
    for index in range(4):
        choices.append(pygame.Rect(launch.x + 16 + index % 2 * (width + gap),
            launch.y + (26 if low else 44) + index // 2 * (height + 9), width, height))
    controls = pygame.Rect(margin, launch.bottom + 12, launch.width,
                           min(150, SCREEN_HEIGHT - launch.bottom - 80))
    actions_width = (launch.width - 20) // 3
    actions = [pygame.Rect(margin + i * (actions_width + 10), SCREEN_HEIGHT - 50,
                           actions_width, 34) for i in range(3)]
    return {"controls": controls, "launch": launch, "choices": choices,
            "continue": actions[0], "start": actions[1], "journal": actions[2]}


@ui_layout
def start_screen_panels():
    if compact_menu_layout():
        layout = compact_start_layout()
        return layout["controls"], layout["launch"]
    margin = max(36, int(SCREEN_WIDTH * 0.045))
    gap = 24
    panel_y = int(SCREEN_HEIGHT * 0.365)
    panel_height = min(430, SCREEN_HEIGHT - panel_y - 82)
    left_width = int((SCREEN_WIDTH - margin * 2 - gap) * 0.59)
    controls = pygame.Rect(margin, panel_y, left_width, panel_height)
    launch = pygame.Rect(controls.right + gap, panel_y, SCREEN_WIDTH - margin - controls.right - gap, panel_height)
    return controls, launch


@ui_layout
def menu_control_layout():
    """One source of geometry for menu drawing and pointer hit testing."""
    cx = SCREEN_WIDTH // 2
    _, launch = start_screen_panels()
    if compact_menu_layout():
        compact = compact_start_layout()
        choices = compact["choices"]
        start, saves, journal = compact["start"], compact["continue"], compact["journal"]
    else:
        choice_width = (launch.width - 64) // 2
        choices = [pygame.Rect(launch.x + 24 + index % 2 * (choice_width + 16),
                   launch.y + 70 + index // 2 * 56, choice_width, 44) for index in range(4)]
        start = pygame.Rect(0, 0, launch.width - 48, 52)
        start.center = (launch.centerx, launch.bottom - 109)
        saves = pygame.Rect(0, 0, launch.width - 48, 45)
        saves.center = (launch.centerx, launch.bottom - 173)
        journal = pygame.Rect(0, 0, launch.width - 48, 44)
        journal.center = (launch.centerx, launch.bottom - 45)
    nav_height = 34 if SCREEN_HEIGHT < 500 else 42
    nav_width = min(150, (SCREEN_WIDTH - 64) // 3)
    journal_back = pygame.Rect(0, 0, nav_width, nav_height)
    journal_back.center = (cx, SCREEN_HEIGHT - (26 if SCREEN_HEIGHT < 500 else 48))
    previous = journal_back.move(-nav_width - 12, 0)
    following = journal_back.move(nav_width + 12, 0)
    exit_rect = pygame.Rect(0, 0, 124, 32)
    exit_rect.midtop = (cx, SCREEN_HEIGHT - 124)
    pause = pygame.Rect(cx - 62, SCREEN_HEIGHT - 44, 124, 32)
    if SCREEN_WIDTH < 700:
        pause.width = 48
        pause.centerx = cx
    play_again = pygame.Rect(0, 0, min(230, SCREEN_WIDTH - 40), 47)
    checkpoint = pygame.Rect(0, 0, min(380, SCREEN_WIDTH - 40), 50)
    infinite = pygame.Rect(0, 0, min(240, SCREEN_WIDTH - 40), 50)
    if compact_menu_layout():
        play_again.height = 34
        checkpoint.height = infinite.height = 36
        play_again.center = (cx, SCREEN_HEIGHT - 31)
        checkpoint.center = infinite.center = (cx, SCREEN_HEIGHT - 78)
    else:
        play_again.center = (cx, round(SCREEN_HEIGHT * .92))
        checkpoint.center = (cx, round(SCREEN_HEIGHT * .84))
        infinite.center = (cx, round(SCREEN_HEIGHT * .78))
    return {"start_button_rect": start, "continue_button_rect": saves,
            "journal_button_rect": journal, "choice_button_rects": choices,
            "journal_previous_rect": previous, "journal_next_rect": following,
            "journal_back_rect": journal_back, "exit_button_rect": exit_rect,
            "pause_button_rect": pause, "play_again_rect": play_again,
            "checkpoint_rect": checkpoint, "infinite_mode_rect": infinite,
            "display_button_rect": pygame.Rect(SCREEN_WIDTH - (62 if SCREEN_WIDTH < 900 else 112),
                                                12, 48 if SCREEN_WIDTH < 900 else 98, 28)}


_SELECTED_SAVE_SLOT = 1


def set_selected_save_slot(slot):
    global _SELECTED_SAVE_SLOT
    _SELECTED_SAVE_SLOT = max(1, min(SAVE_SLOT_COUNT, int(slot)))


@ui_layout
def save_browser_layout():
    """Shared card and modal geometry for rendering and pointer hit testing."""
    margin = max(28, round(SCREEN_WIDTH * 0.06))
    gap = max(16, round(SCREEN_WIDTH * 0.015))
    card_width = (SCREEN_WIDTH - margin * 2 - gap * 2) // 3
    card_top = round(SCREEN_HEIGHT * 0.24)
    card_height = min(430, round(SCREEN_HEIGHT * 0.54))
    compact = compact_menu_layout()
    slot_tabs = []
    if compact:
        margin = 16
        card_width = SCREEN_WIDTH - margin * 2
        tab_gap = 10
        tab_width = (card_width - 2 * tab_gap) // 3
        tab_y = 76 if SCREEN_HEIGHT < 500 else 100
        slot_tabs = [pygame.Rect(margin + i * (tab_width + tab_gap), tab_y, tab_width, 32)
                     for i in range(SAVE_SLOT_COUNT)]
        card_top = slot_tabs[0].bottom + 12
        card_height = SCREEN_HEIGHT - card_top - 100
    cards = []
    indices = [_SELECTED_SAVE_SLOT - 1] if compact else range(SAVE_SLOT_COUNT)
    for index in indices:
        panel = pygame.Rect(margin + index * (card_width + gap), card_top,
                            card_width, card_height)
        if compact:
            panel.x = margin
        new = pygame.Rect(panel.x + 20, panel.bottom - 94, panel.width - 40, 34)
        resume = new.move(0, -42)
        if compact:
            primary_width = (panel.width - 48) // 2
            resume = pygame.Rect(panel.x + 20, panel.bottom - 88, primary_width, 32)
            new = resume.move(primary_width + 8, 0)
        action_width = (panel.width - 56) // 3
        actions = [pygame.Rect(panel.x + 20 + i * (action_width + 8),
                               panel.bottom - 48, action_width, 30) for i in range(3)]
        cards.append({"slot": index + 1, "panel": panel,
                      "continue": resume, "new": new,
                      "delete": actions[0], "export": actions[1], "import": actions[2]})
    back = pygame.Rect(0, 0, 220, 44)
    back.midbottom = (SCREEN_WIDTH // 2 - 122, SCREEN_HEIGHT - 32)
    quit_button = back.move(244, 0)
    dialog = pygame.Rect(0, 0, min(740, SCREEN_WIDTH - 80), 300)
    dialog.center = (SCREEN_WIDTH // 2, SCREEN_HEIGHT // 2)
    button_width = (dialog.width - 72) // 2
    confirm = pygame.Rect(dialog.x + 28, dialog.bottom - 76, button_width, 46)
    cancel = pygame.Rect(confirm.right + 16, confirm.y, button_width, 46)
    path_input = pygame.Rect(dialog.x + 28, dialog.y + 94, dialog.width - 174, 42)
    browse = pygame.Rect(path_input.right + 10, path_input.y, 108, 42)
    return {"cards": cards, "back": back, "quit": quit_button, "dialog": dialog,
            "confirm": confirm, "cancel": cancel, "path_input": path_input,
            "browse": browse, "slot_tabs": slot_tabs, "compact": compact}


def saved_run_can_continue(snapshot):
    """An ongoing last attempt can continue; an exhausted defeated run cannot."""
    return snapshot is not None and (
        not snapshot.get("run_defeated", False)
        or snapshot.get("retries_remaining", MAX_RUN_RETRIES) > 0
    )


@ui_scene
def draw_save_browser(screen, saved_slots, title_font, button_font, font,
                      pending_replace_slot=None, save_error=None, pending_save_action=None,
                      save_status=None):
    """Independent save cards with confirmed replacement, deletion and transfers."""
    draw_space_background(screen, "menu")
    layout = save_browser_layout()
    if layout["compact"]:
        draw_compact_save_browser(screen, saved_slots, layout, title_font, button_font, font,
                                  save_error, save_status)
        if pending_replace_slot is not None:
            action = {"kind": "import", "slot": pending_replace_slot,
                      "stage": "overwrite", "path": "", "error": None,
                      "replace_run": True}
            draw_save_action_dialog(screen, action, layout, button_font, font)
        if pending_save_action is not None:
            draw_save_action_dialog(screen, pending_save_action, layout, button_font, font)
        return
    draw_neon_title(screen, "SAVED RUNS", title_font,
                    (SCREEN_WIDTH // 2, round(SCREEN_HEIGHT * 0.10)), UI_CYAN)
    subtitle = font.render(f"{SAVE_SLOT_COUNT} slots. Each run autosaves to its own file.", True, UI_TEXT)
    screen.blit(subtitle, subtitle.get_rect(center=(SCREEN_WIDTH // 2, round(SCREEN_HEIGHT * 0.18))))
    detail_font = pygame.font.SysFont(None, 23 if SCREEN_WIDTH >= 1400 else 21)
    date_font = pygame.font.SysFont(None, 21 if SCREEN_WIDTH >= 1400 else 19)
    player_count_font = pygame.font.SysFont(None, 28 if SCREEN_WIDTH >= 1400 else 26)
    action_font = pygame.font.SysFont(None, 22)
    for card in layout["cards"]:
        slot, panel = card["slot"], card["panel"]
        snapshot = saved_slots[slot - 1] if slot <= len(saved_slots) else None
        occupied = snapshot is not None or save_slot_occupied(slot)
        accent = UI_CYAN if snapshot else UI_CORAL if occupied else UI_VIOLET
        draw_neon_panel(screen, panel, accent, radius=15)
        heading = button_font.render(f"SLOT {slot:02d}", True, accent)
        screen.blit(heading, heading.get_rect(midtop=(panel.centerx, panel.top + 22)))
        if snapshot is not None:
            wave_text = button_font.render(f"WAVE {snapshot['wave']}", True, UI_TEXT)
            screen.blit(wave_text, wave_text.get_rect(midtop=(panel.centerx, panel.top + 67)))
            mode = "INFINITE" if snapshot["infinite_mode"] else "CAMPAIGN"
            count = snapshot["player_count"]
            player_label = player_count_font.render(
                f"{count} PLAYER{'S' if count != 1 else ''}", True, UI_CYAN)
            screen.blit(player_label, player_label.get_rect(midtop=(panel.centerx, panel.top + 101)))
            lines = (
                (f"SECTOR {sector_for_round(snapshot['wave']):02d}  /  {mode}", UI_GOLD),
                (f"TEAM SCORE {sum(p['score'] for p in snapshot['pilots']):,}", UI_TEXT),
                ("LIVES  " + "   ".join(f"P{i + 1}: {p['lives']}" for i, p in enumerate(snapshot["pilots"])), UI_MINT),
            )
            for index, (text, color) in enumerate(lines):
                surface = detail_font.render(text, True, color)
                if surface.get_width() > panel.width - 36:
                    surface = pygame.transform.smoothscale(surface,
                        (panel.width - 36, surface.get_height()))
                screen.blit(surface, surface.get_rect(midtop=(panel.centerx, panel.top + 133 + index * 25)))
            try:
                saved_time = datetime.fromisoformat(snapshot["saved_at"]).astimezone()
                date_text = saved_time.strftime("Saved %b %d, %Y  %I:%M %p")
            except (KeyError, ValueError, TypeError, OverflowError):
                date_text = "Save time unavailable"
            date = date_font.render(date_text, True, UI_MUTED)
            screen.blit(date, date.get_rect(midtop=(panel.centerx, panel.top + 216)))
            retries = snapshot.get("retries_remaining", MAX_RUN_RETRIES)
            continue_label = (f"RETRY MENU ({retries})" if snapshot.get("run_defeated", False)
                              else f"CONTINUE ({retries} RETRIES)")
            if not saved_run_can_continue(snapshot):
                continue_label = "NO RETRIES LEFT"
            draw_neon_button(screen, card["continue"], continue_label, font, UI_MINT,
                             enabled=saved_run_can_continue(snapshot))
            draw_neon_button(screen, card["new"], "NEW RUN", font, UI_VIOLET)
        else:
            state = "UNREADABLE SAVE" if occupied else "EMPTY SLOT"
            state_label = font.render(state, True, accent)
            screen.blit(state_label, state_label.get_rect(center=(panel.centerx, panel.top + 133)))
            notes = (("This file could not be loaded.", "It stays until you replace it.")
                     if occupied else ("Start a new defense run here.", "Your other saves stay separate."))
            for index, text in enumerate(notes):
                label = detail_font.render(text, True, UI_MUTED)
                screen.blit(label, label.get_rect(center=(panel.centerx, panel.top + 180 + index * 29)))
            draw_neon_button(screen, card["new"], "REPLACE SAVE" if occupied else "NEW RUN",
                             font, UI_CORAL if occupied else UI_MINT)
        draw_neon_button(screen, card["delete"], "DELETE", action_font, UI_CORAL, enabled=occupied)
        draw_neon_button(screen, card["export"], "EXPORT", action_font, UI_CYAN, enabled=snapshot is not None)
        draw_neon_button(screen, card["import"], "IMPORT", action_font, UI_GOLD)
    footer = detail_font.render(save_error or save_status or "Active saves restart the wave. Defeated runs use retries. Export/import JSON; deletion asks first.",
                                True, UI_CORAL if save_error else UI_MINT if save_status else UI_MUTED)
    footer_y = min(layout["back"].top - 24, layout["cards"][0]["panel"].bottom + 30)
    screen.blit(footer, footer.get_rect(center=(SCREEN_WIDTH // 2, footer_y)))
    draw_neon_button(screen, layout["back"], "MAIN MENU", font, UI_VIOLET)
    draw_neon_button(screen, layout["quit"], "QUIT GAME", font, UI_CORAL)
    if pending_replace_slot is not None:
        overlay = pygame.Surface((SCREEN_WIDTH, SCREEN_HEIGHT), pygame.SRCALPHA)
        overlay.fill((3, 4, 18, 220))
        screen.blit(overlay, (0, 0))
        dialog = layout["dialog"]
        draw_neon_panel(screen, dialog, UI_CORAL, radius=15)
        heading = button_font.render(f"REPLACE SLOT {pending_replace_slot}?", True, UI_CORAL)
        screen.blit(heading, heading.get_rect(midtop=(dialog.centerx, dialog.top + 28)))
        for index, text in enumerate(("The saved run in this slot will be replaced.",
                                      "Your other save slots stay unchanged.")):
            label = font.render(text, True, UI_TEXT if index == 0 else UI_MUTED)
            screen.blit(label, label.get_rect(center=(dialog.centerx, dialog.top + 96 + index * 29)))
        draw_neon_button(screen, layout["confirm"], "CONFIRM REPLACE", font, UI_CORAL)
        draw_neon_button(screen, layout["cancel"], "CANCEL", font, UI_CYAN)
    if pending_save_action is not None:
        draw_save_action_dialog(screen, pending_save_action, layout, button_font, font)


def draw_compact_save_browser(screen, saved_slots, layout, title_font, button_font, font,
                               save_error=None, save_status=None):
    low = SCREEN_HEIGHT < 500
    draw_fitted_text(screen, "SAVED RUNS", title_font, UI_CYAN,
                     pygame.Rect(20, 12, SCREEN_WIDTH - 40, 42 if low else 60))
    draw_fitted_text(screen, "Choose a slot. Runs and retry budgets stay separate.", font, UI_TEXT,
                     pygame.Rect(20, 53 if low else 72, SCREEN_WIDTH - 40, 20))
    for index, tab in enumerate(layout["slot_tabs"], start=1):
        draw_neon_button(screen, tab, f"SLOT {index}", font, UI_CYAN,
                         selected=index == _SELECTED_SAVE_SLOT)
    card = layout["cards"][0]
    slot, panel = card["slot"], card["panel"]
    snapshot = saved_slots[slot - 1] if slot <= len(saved_slots) else None
    occupied = snapshot is not None or save_slot_occupied(slot)
    accent = UI_CYAN if snapshot else UI_CORAL if occupied else UI_VIOLET
    draw_neon_panel(screen, panel, accent, radius=12)
    content_bottom = card["continue"].top - 8
    content = pygame.Rect(panel.x + 16, panel.y + 8, panel.width - 32,
                          max(20, content_bottom - panel.y - 8))
    if snapshot:
        heading = f"SLOT {slot}  ·  WAVE {snapshot['wave']}  ·  {snapshot['player_count']} PLAYERS"
        lines = [heading,
                 f"{'INFINITE' if snapshot['infinite_mode'] else 'CAMPAIGN'}  |  TEAM SCORE {sum(p['score'] for p in snapshot['pilots']):,}",
                 "LIVES  " + "   ".join(f"P{i+1}: {p['lives']}" for i, p in enumerate(snapshot["pilots"]))]
        if content.height < 58:
            lines = [heading, f"TEAM {sum(p['score'] for p in snapshot['pilots']):,}  |  " +
                     "  ".join(f"P{i+1}: {p['lives']} LIVES" for i, p in enumerate(snapshot["pilots"]))]
        if content.height >= 125:
            try:
                saved_time = datetime.fromisoformat(snapshot["saved_at"]).astimezone()
                lines.append(saved_time.strftime("Saved %b %d, %Y  %I:%M %p"))
            except (KeyError, ValueError, TypeError, OverflowError):
                lines.append("Save time unavailable")
        row = max(16, min(36, content.height // len(lines)))
        for index, text in enumerate(lines):
            draw_fitted_text(screen, text, button_font if index == 0 else font,
                             UI_TEXT if index < 2 else UI_MINT,
                             pygame.Rect(content.x, content.y + index * row, content.width, row - 2))
        retries = snapshot.get("retries_remaining", MAX_RUN_RETRIES)
        resume = f"RETRY MENU ({retries})" if snapshot.get("run_defeated") else f"CONTINUE ({retries} RETRIES)"
        draw_neon_button(screen, card["continue"], resume if saved_run_can_continue(snapshot) else "NO RETRIES LEFT",
                         font, UI_MINT, enabled=saved_run_can_continue(snapshot))
    else:
        draw_fitted_text(screen, "UNREADABLE SAVE" if occupied else "EMPTY SLOT", button_font, accent,
                         content)
        draw_neon_button(screen, card["continue"], "NO SAVED RUN", font, UI_MUTED, enabled=False)
    draw_neon_button(screen, card["new"], "REPLACE SAVE" if occupied else "NEW RUN", font, UI_VIOLET)
    for key, label, color, enabled in (("delete", "DELETE", UI_CORAL, occupied),
                                      ("export", "EXPORT", UI_CYAN, snapshot is not None),
                                      ("import", "IMPORT", UI_GOLD, True)):
        draw_neon_button(screen, card[key], label, font, color, enabled=enabled)
    draw_neon_button(screen, layout["back"], "MAIN MENU", font, UI_VIOLET)
    draw_neon_button(screen, layout["quit"], "QUIT GAME", font, UI_CORAL)
    if save_error or save_status:
        draw_fitted_text(screen, save_error or save_status, font, UI_CORAL if save_error else UI_MINT,
                         pygame.Rect(16, layout["back"].top - 22, SCREEN_WIDTH - 32, 18))


def begin_save_action(kind, slot):
    """Prepare a non-blocking dialog; no file changes happen until confirmation."""
    path = str(Path.home() / "Downloads" / f"Neon-Frontier-slot-{slot}.json") if kind == "export" else ""
    action = {"kind": kind, "slot": slot, "stage": "confirm" if kind == "delete" else "path",
              "path": path, "error": None, "select_all": bool(path)}
    if kind != "delete":
        pygame.key.start_text_input()
    return action


def browse_save_transfer(action):
    """Use an optional native picker; the in-game path entry works without Tk."""
    window = None
    try:
        import tkinter
        from tkinter import filedialog
        window = tkinter.Tk()
        window.withdraw()
        window.attributes("-topmost", True)
        options = {"parent": window, "filetypes": [("JSON saves", "*.json"), ("All files", "*.*")]}
        if action["kind"] == "export":
            chosen = filedialog.asksaveasfilename(
                **options, defaultextension=".json", initialfile=f"Neon-Frontier-slot-{action['slot']}.json")
        else:
            chosen = filedialog.askopenfilename(**options)
        if chosen:
            action["path"] = chosen
            action["select_all"] = True
            action["error"] = None
    except Exception:
        action["error"] = "Picker unavailable: type/paste a path or drop a JSON file."
    finally:
        if window is not None:
            try:
                window.destroy()
            except Exception:
                pass


def update_save_action_input(action, event):
    """Handle text, pasted paths and file drops without blocking the game loop."""
    if action["stage"] != "path":
        return
    text = None
    if event.type == pygame.DROPFILE:
        text = event.file
        action["select_all"] = True
    elif event.type == pygame.TEXTINPUT:
        text = event.text
    elif event.type == pygame.KEYDOWN:
        modifiers = getattr(event, "mod", pygame.key.get_mods())
        if event.key == pygame.K_a and modifiers & pygame.KMOD_CTRL:
            action["select_all"] = True
        elif event.key == pygame.K_v and modifiers & pygame.KMOD_CTRL:
            try:
                if hasattr(pygame.scrap, "get_text"):
                    text = pygame.scrap.get_text()
                else:
                    pygame.scrap.init()
                    value = pygame.scrap.get(pygame.SCRAP_TEXT)
                    text = value.decode("utf-8", errors="replace") if value else ""
            except (pygame.error, UnicodeError):
                action["error"] = "Paste unavailable: type the path or drop the JSON file."
        elif event.key == pygame.K_BACKSPACE:
            action["path"] = "" if action.get("select_all") else action["path"][:-1]
            action["select_all"] = False
            action["error"] = None
    if text is not None:
        text = "".join(character for character in str(text) if character >= " " and character != "\x7f")
        action["path"] = (("" if action.get("select_all") else action["path"]) + text)[:4096]
        action["select_all"] = False
        action["error"] = None


def confirm_save_action(action):
    """Return (finished, message); failed actions keep their dialog open."""
    kind, slot = action["kind"], action["slot"]
    if kind == "delete":
        success, message = delete_saved_slot(slot)
    else:
        try:
            path = save_transfer_path(action["path"])
        except (OSError, ValueError, TypeError, RuntimeError) as error:
            action["error"] = str(error)
            return False, None
        if action["stage"] == "path":
            if kind == "import" and load_saved_run(path) is None:
                action["error"] = "This file is unreadable or is not a supported game save."
                return False, None
            try:
                needs_confirmation = save_slot_occupied(slot) if kind == "import" else path.exists()
            except OSError:
                action["error"] = "Cannot access that path. Choose another file or folder."
                return False, None
            if needs_confirmation:
                action["stage"] = "overwrite"
                action["error"] = None
                pygame.key.stop_text_input()
                return False, None
        if kind == "import":
            snapshot, message = import_saved_slot(slot, path, overwrite=action["stage"] == "overwrite")
            success = snapshot is not None
        else:
            success, message = export_saved_slot(slot, path, overwrite=action["stage"] == "overwrite")
    if success:
        pygame.key.stop_text_input()
        return True, message
    action["error"] = message
    return False, None


@ui_scene
def draw_save_action_dialog(screen, action, layout, button_font, font):
    overlay = pygame.Surface((SCREEN_WIDTH, SCREEN_HEIGHT), pygame.SRCALPHA)
    overlay.fill((3, 4, 18, 225))
    screen.blit(overlay, (0, 0))
    dialog = layout["dialog"]
    kind, stage, slot = action["kind"], action["stage"], action["slot"]
    accent = UI_CORAL if kind == "delete" or stage == "overwrite" else UI_CYAN
    draw_neon_panel(screen, dialog, accent, radius=15)
    heading = (f"REPLACE SLOT {slot}?" if action.get("replace_run") else
               f"DELETE SLOT {slot}?" if kind == "delete" else f"{kind.upper()} SLOT {slot}")
    title = button_font.render(heading, True, accent)
    screen.blit(title, title.get_rect(midtop=(dialog.centerx, dialog.y + 24)))
    if kind == "delete":
        lines = ("This save file will be permanently deleted.", "Your other slots and exported files stay unchanged.")
    elif stage == "overwrite":
        lines = (("The current save in this slot will be replaced.", "Your other slots stay unchanged.")
                 if kind == "import" else ("A file already exists at this path.", "Overwrite it with the selected save?"))
    else:
        lines = ("Choose a JSON file on this computer.",)
    for index, text in enumerate(lines):
        line = font.render(text, True, UI_TEXT)
        screen.blit(line, line.get_rect(center=(dialog.centerx, dialog.y + 76 + index * 30)))
    if stage == "path":
        field = layout["path_input"]
        pygame.draw.rect(screen, (15, 24, 47), field, border_radius=5)
        pygame.draw.rect(screen, UI_CYAN, field, 1, border_radius=5)
        path_text = action["path"] or "Type a path or drop a JSON file here"
        rendered = font.render(path_text, True, UI_TEXT if action["path"] else UI_MUTED)
        previous_clip = screen.get_clip()
        screen.set_clip(field.inflate(-12, -4))
        x = field.x + 8 if rendered.get_width() <= field.width - 16 else field.right - 8 - rendered.get_width()
        screen.blit(rendered, (x, field.centery - rendered.get_height() // 2))
        screen.set_clip(previous_clip)
        draw_neon_button(screen, layout["browse"], "BROWSE", font, UI_VIOLET)
        draw_fitted_text(screen, "Ctrl+A selects; Ctrl+V pastes. Enter confirms; Esc cancels.",
                         font, UI_MUTED, pygame.Rect(dialog.x + 20, dialog.y + 150, dialog.width - 40, 26))
    if action.get("error"):
        error_font = pygame.font.SysFont(None, 21)
        error = error_font.render(action["error"], True, UI_CORAL)
        if error.get_width() > dialog.width - 40:
            error = pygame.transform.smoothscale(error, (dialog.width - 40, error.get_height()))
        screen.blit(error, error.get_rect(center=(dialog.centerx, dialog.bottom - 98)))
    label = "DELETE SAVE" if kind == "delete" else "CONFIRM REPLACE" if stage == "overwrite" else kind.upper()
    draw_neon_button(screen, layout["confirm"], label, font, accent)
    draw_neon_button(screen, layout["cancel"], "CANCEL", font, UI_CYAN)


@ui_scene
def draw_start_screen(
    screen,
    start_button_rect,
    journal_button_rect,
    choice_button_rects,
    title_font,
    button_font,
    player_choice_font,
    player_count,
    saved_run=None,
    continue_button_rect=None,
    save_error=None,
    saved_slots=None,
):
    draw_space_background(screen, "menu")
    if compact_menu_layout():
        draw_compact_start_screen(screen, title_font, button_font, player_choice_font,
                                  player_count, save_error, saved_slots)
        return
    cx = SCREEN_WIDTH // 2
    micro_title = player_choice_font.render("NEON FRONTIER  /  PLANETARY DEFENSE", True, UI_PINK)
    screen.blit(micro_title, micro_title.get_rect(center=(cx, int(SCREEN_HEIGHT * 0.052))))
    draw_neon_title(screen, "SPACE INVADERS", title_font, (cx, int(SCREEN_HEIGHT * 0.13)), UI_CYAN)
    tagline = player_choice_font.render(f"{MAX_CAMPAIGN_ROUND} WAVES. ONE PLANET. YOUR SQUAD.", True, UI_GOLD)
    screen.blit(tagline, tagline.get_rect(center=(cx, int(SCREEN_HEIGHT * 0.205))))
    controls_panel, launch_panel = start_screen_panels()
    objective_panel = pygame.Rect(controls_panel.x, int(SCREEN_HEIGHT * 0.25), SCREEN_WIDTH - controls_panel.x * 2, 64)
    draw_neon_panel(screen, objective_panel, UI_VIOLET)
    objective = (
        "Clear the fleet, survive enemy fire, and face a boss every fifth wave. "
        f"Retry from the start of each {WAVES_PER_SECTOR}-wave sector. Regular enemy HP increases "
        "only once, after wave 50; bosses scale separately. "
        f"Clear all {MAX_CAMPAIGN_ROUND} waves to save Earth!"
    )
    objective_lines = []
    current_line = ""
    max_objective_width = objective_panel.width - 36
    for word in objective.split():
        candidate = f"{current_line} {word}".strip()
        if current_line and player_choice_font.size(candidate)[0] > max_objective_width:
            objective_lines.append(current_line)
            current_line = word
        else:
            current_line = candidate
    if current_line:
        objective_lines.append(current_line)

    line_height = player_choice_font.get_linesize()
    first_line_y = objective_panel.centery - (len(objective_lines) - 1) * line_height // 2
    for index, line in enumerate(objective_lines):
        objective_text = player_choice_font.render(line, True, UI_TEXT)
        screen.blit(objective_text, objective_text.get_rect(center=(cx, first_line_y + index * line_height)))

    draw_neon_panel(screen, controls_panel, UI_CYAN)
    draw_neon_panel(screen, launch_panel, UI_PINK)
    controls_heading = player_choice_font.render("FLIGHT CONTROLS", True, UI_CYAN)
    screen.blit(controls_heading, (controls_panel.x + 24, controls_panel.y + 21))
    launch_heading = player_choice_font.render("ASSEMBLE YOUR SQUAD", True, UI_PINK)
    screen.blit(launch_heading, launch_heading.get_rect(center=(launch_panel.centerx, launch_panel.y + 31)))
    control_labels = tuple(player_control_labels(index) for index in range(4))
    control_font = pygame.font.SysFont(None, 21 if SCREEN_WIDTH < 1400 else 23)
    row_height = min(76, (controls_panel.height - 82) // 4)
    for index, (movement, firing) in enumerate(control_labels):
        row_y = controls_panel.y + 61 + index * row_height
        color = PLAYER_COLORS[index]
        active = index < player_count
        pygame.draw.rect(screen, color if active else (50, 59, 83), (controls_panel.x + 20, row_y, 4, row_height - 12), border_radius=2)
        badge = player_choice_font.render(f"P{index + 1}", True, color if active else UI_MUTED)
        screen.blit(badge, (controls_panel.x + 36, row_y + 1))
        draw_fitted_text(screen, f"MOVE   {movement}", control_font, UI_TEXT if active else UI_MUTED,
                         pygame.Rect(controls_panel.x + 86, row_y, controls_panel.width - 106, 24), "left")
        draw_fitted_text(screen, f"FIRE     {firing}", control_font, color if active else UI_MUTED,
                         pygame.Rect(controls_panel.x + 86, row_y + 24, controls_panel.width - 106, 24), "left")
    for index, choice_rect in enumerate(choice_button_rects, start=1):
        label = "1 PLAYER" if index == 1 else f"{index} PLAYERS"
        draw_neon_button(screen, choice_rect, label, player_choice_font, PLAYER_COLORS[index - 1], selected=player_count == index)
    if (saved_run is not None or saved_slots is not None) and continue_button_rect is not None:
        label = (f"SAVE FILES  ({sum(snapshot is not None for snapshot in saved_slots)} VALID)"
                 if saved_slots is not None else
                 f"CONTINUE  WAVE {saved_run['wave']}  /  SECTOR {sector_for_round(saved_run['wave'])}")
        draw_neon_button(screen, continue_button_rect, label, player_choice_font, UI_GOLD)
    draw_neon_button(screen, start_button_rect, "NEW RUN" if saved_slots is not None or saved_run else "START", button_font, UI_MINT)
    draw_neon_button(screen, journal_button_rect, "JOURNAL", player_choice_font, UI_VIOLET)
    footer_label = ("AUTOSAVE: CONTINUE RESTARTS AT WAVE START  |  ENEMY JOURNAL"
                    if saved_run else "ENEMY INTEL + EVERY POWERUP IN THE JOURNAL")
    footer = player_choice_font.render(save_error or footer_label, True,
                                      UI_CORAL if save_error else UI_MUTED)
    screen.blit(footer, footer.get_rect(center=(cx, SCREEN_HEIGHT - 38)))


def draw_compact_start_screen(screen, title_font, button_font, font, player_count,
                              save_error=None, saved_slots=None):
    low = SCREEN_HEIGHT < 500
    draw_fitted_text(screen, "SPACE INVADERS", title_font, UI_CYAN,
                     pygame.Rect(20, 12 if low else 28, SCREEN_WIDTH - (152 if low else 40), 44 if low else 68))
    if not low:
        draw_fitted_text(screen, f"{MAX_CAMPAIGN_ROUND} WAVES. ONE PLANET. YOUR SQUAD.", font, UI_GOLD,
                         pygame.Rect(20, 102, SCREEN_WIDTH - 40, 24))
    layout = compact_start_layout()
    draw_neon_panel(screen, layout["launch"], UI_PINK)
    draw_fitted_text(screen, "ASSEMBLE YOUR SQUAD", font, UI_PINK,
                     pygame.Rect(layout["launch"].x + 12, layout["launch"].y + 4,
                                 layout["launch"].width - 24, 21 if low else 30))
    for index, rect in enumerate(layout["choices"], start=1):
        draw_neon_button(screen, rect, "1 PLAYER" if index == 1 else f"{index} PLAYERS",
                         font, PLAYER_COLORS[index - 1], selected=index == player_count)
    controls = layout["controls"]
    draw_neon_panel(screen, controls, UI_CYAN)
    row_height = max(15, (controls.height - 30) // 4)
    small_font = pygame.font.SysFont(None, 19 if low else 22)
    draw_fitted_text(screen, "FLIGHT CONTROLS — MOVE / FIRE", small_font, UI_CYAN,
                     pygame.Rect(controls.x + 12, controls.y + 4, controls.width - 24, 21))
    controls_text = tuple(f"P{index + 1}  {move}  /  {fire}"
                          for index in range(4)
                          for move, fire in (player_control_labels(index),))
    for index, text in enumerate(controls_text):
        draw_fitted_text(screen, text, small_font,
                         PLAYER_COLORS[index] if index < player_count else UI_MUTED,
                         pygame.Rect(controls.x + 12, controls.y + 26 + index * row_height,
                                     controls.width - 24, row_height - 2), "left")
    valid = sum(snapshot is not None for snapshot in saved_slots) if saved_slots is not None else 0
    draw_neon_button(screen, layout["continue"], f"SAVES ({valid})", font, UI_GOLD)
    draw_neon_button(screen, layout["start"], "NEW RUN", button_font, UI_MINT)
    draw_neon_button(screen, layout["journal"], "JOURNAL", font, UI_VIOLET)
    if save_error:
        draw_fitted_text(screen, save_error, small_font, UI_CORAL,
                         pygame.Rect(16, SCREEN_HEIGHT - 72, SCREEN_WIDTH - 32, 18))


@ui_layout
def journal_layout_metrics():
    margin = 20 if SCREEN_WIDTH < 1100 else 40
    gap = 16
    columns = 2 if SCREEN_WIDTH >= 1100 else 1
    low = SCREEN_HEIGHT < 500
    start_y = 108 if low else 158
    nav = menu_control_layout()
    bottom = min(nav[key].top for key in ("journal_previous_rect", "journal_next_rect", "journal_back_rect")) - 12
    available = max(100, bottom - start_y)
    rows = max(1, min(5, (available + 10) // 122))
    card_height = max(90, (available - (rows - 1) * 10) // rows)
    return {"margin": margin, "columns": columns, "rows": rows,
            "per_page": columns * rows, "card_width": (SCREEN_WIDTH - 2 * margin - (columns - 1) * gap) // columns,
            "card_height": card_height, "gap": gap, "row_gap": 10, "start_y": start_y,
            "content_bottom": bottom}


@ui_layout
def journal_page_model(page):
    metrics = journal_layout_metrics()
    per_page = metrics["per_page"]
    sections = (("ENEMY TYPES", ENEMY_JOURNAL), ("MUTATIONS", ENEMY_MUTATIONS),
                ("POWERUPS", POWERUP_JOURNAL))
    total = sum(math.ceil(len(entries) / per_page) for _, entries in sections)
    page = max(0, min(max(0, total - 1), page))
    section_page = page
    for section, entries in sections:
        count = math.ceil(len(entries) / per_page)
        if section_page < count:
            first = section_page * per_page
            return dict(metrics, section=section, entries=entries[first:first + per_page],
                        page=page, page_count=total)
        section_page -= count
    raise ValueError("Journal has no sections")


def draw_journal_description(screen, description, font, x, y, width):
    lines = []
    current_line = ""
    for word in description.split():
        candidate = f"{current_line} {word}".strip()
        if current_line and font.size(candidate)[0] > width:
            lines.append(current_line)
            current_line = word
        else:
            current_line = candidate
    if current_line:
        lines.append(current_line)
    for line_index, line in enumerate(lines):
        screen.blit(font.render(line, True, UI_TEXT), (x, y + line_index * font.get_linesize()))


@ui_scene
def draw_enemy_journal(
    screen,
    page,
    title_font,
    button_font,
    entry_font,
    description_font,
    journal_sprites,
    previous_rect,
    next_rect,
    back_rect,
):
    if journal_layout_metrics()["per_page"] != JOURNAL_ENTRIES_PER_PAGE or compact_menu_layout():
        draw_responsive_journal(screen, page, title_font, button_font, entry_font,
                                description_font, journal_sprites,
                                previous_rect, next_rect, back_rect)
        return
    draw_space_background(screen, style="journal")
    draw_neon_title(screen, "JOURNAL", title_font, (SCREEN_WIDTH // 2, 56), UI_CYAN)
    type_page_count = math.ceil(len(ENEMY_JOURNAL) / JOURNAL_ENTRIES_PER_PAGE)
    page_count = journal_page_count()
    is_mutation_page = page == type_page_count
    is_powerup_page = page > type_page_count
    section = "POWERUPS" if is_powerup_page else "MUTATIONS" if is_mutation_page else "ENEMY TYPES"
    page_label = entry_font.render(
        f"{section}  {page + 1} / {page_count}",
        True,
        UI_CYAN,
    )
    screen.blit(page_label, page_label.get_rect(center=(SCREEN_WIDTH // 2, 110)))
    if is_powerup_page:
        note_text = "Repeated timed pickups extend buffs up to twice their duration. Weapon rates scale with active pilots."
    elif is_mutation_page:
        note_text = "Colored outlines identify mutations. Body colors are cosmetic."
    else:
        note_text = "Body colors are cosmetic. Outlines identify mutations; boss colors follow attacks."
    note = description_font.render(note_text, True, UI_MUTED)
    screen.blit(note, note.get_rect(center=(SCREEN_WIDTH // 2, 136)))

    if is_mutation_page:
        card_height = min(132, (SCREEN_HEIGHT - 250 - 28) // len(ENEMY_MUTATIONS))
        for index, (name, description, color) in enumerate(ENEMY_MUTATIONS):
            card = pygame.Rect(
                70,
                170 + index * (card_height + 14),
                SCREEN_WIDTH - 140,
                card_height,
            )
            draw_neon_panel(screen, card, color, fill=(10, 16, 38), radius=12)
            sample = generate_pixel_sprite(STANDARD_ART_V1, UI_VIOLET, 48, 36)
            sample_rect = sample.get_rect(center=(card.x + 51, card.centery - 4))
            screen.blit(sample, sample_rect)
            pygame.draw.rect(screen, color, sample_rect.inflate(12, 12), 2)
            name_surface = entry_font.render(name, True, color)
            screen.blit(name_surface, (card.x + 102, card.y + 20))
            draw_journal_description(
                screen, description, description_font,
                card.x + 102, card.y + 52, card.width - 128,
            )
    else:
        margin = 40
        column_gap = 18
        card_width = (SCREEN_WIDTH - margin * 2 - column_gap) // 2
        row_gap = 10
        start_y = 160
        content_bottom = min(previous_rect.top, next_rect.top, back_rect.top) - 12
        card_height = min(112, (content_bottom - start_y - row_gap * 4) // 5)
        section_page = page - type_page_count - 1 if is_powerup_page else page
        entries = POWERUP_JOURNAL if is_powerup_page else ENEMY_JOURNAL
        first_entry = section_page * JOURNAL_ENTRIES_PER_PAGE
        page_entries = entries[first_entry:first_entry + JOURNAL_ENTRIES_PER_PAGE]
        for local_index, (name, description) in enumerate(page_entries):
            column = local_index % 2
            row = local_index // 2
            card = pygame.Rect(
                margin + column * (card_width + column_gap),
                start_y + row * (card_height + row_gap),
                card_width,
                card_height,
            )
            if is_powerup_page:
                color = POWERUP_COLORS[name]
                draw_neon_panel(screen, card, color, fill=(10, 16, 38), radius=10)
                icon_center = (card.x + 27, card.y + 20)
                pygame.draw.circle(screen, color, icon_center, 15)
                pygame.draw.circle(screen, (10, 16, 38), icon_center, 12)
                draw_powerup_icon(screen, name, icon_center)
                label_color = UI_CYAN if color == BLUE else color
                name_surface = entry_font.render(POWERUP_LABELS[name], True, label_color)
                screen.blit(name_surface, (card.x + 50, card.y + 8))
                duration = (
                    f"{POWERUP_DURATIONS[name] // 1000} SECONDS"
                    if name in POWERUP_DURATIONS else "RUN UPGRADE" if name in ("damage_up", "health_up")
                    else "STORED UNTIL USED" if name in ("emergency_warp", "reflector", "supply_beacon", "missile_swarm")
                    else "3-2-1 COUNTDOWN" if name == "nova_pulse"
                    else "INSTANT"
                )
                duration_surface = description_font.render(duration, True, UI_MUTED)
                screen.blit(duration_surface, duration_surface.get_rect(topright=(card.right - 12, card.y + 10)))
            else:
                enemy_type = name.lower().replace(" ", "_")
                accent = UI_GOLD if enemy_type == "boss" else VISUAL_VARIATIONS[enemy_type][0]["color"]
                draw_neon_panel(screen, card, accent, fill=(10, 16, 38), radius=10)
                variations = journal_sprites[name]
                for variation_index, frames in enumerate(variations):
                    sprite = frames[(pygame.time.get_ticks() // 150 + variation_index) % len(frames)]
                    screen.blit(sprite, (card.x + 12 + variation_index * 36, card.y + 8))
                text_x = card.x + 20 + len(variations) * 36
                name_surface = entry_font.render(name, True, accent)
                screen.blit(name_surface, (text_x, card.y + 8))
                if enemy_type == "boss":
                    colors = tuple(dict.fromkeys(color for color, _ in BOSS_ATTACKS.values()))
                    for color_index, color in enumerate(colors):
                        pygame.draw.circle(
                            screen, color,
                            (card.right - 12 - (len(colors) - color_index - 1) * 11, card.y + 19),
                            3,
                        )

            draw_journal_description(
                screen, description, description_font,
                card.x + 12, card.y + 36, card.width - 24,
            )

    for rect, label, enabled in (
        (previous_rect, "PREVIOUS", page > 0),
        (next_rect, "NEXT", page < page_count - 1),
        (back_rect, "BACK", True),
    ):
        accent = UI_PINK if label == "BACK" else UI_CYAN
        draw_neon_button(
            screen, rect, label, button_font, accent=accent,
            enabled=enabled,
        )


def draw_responsive_journal(screen, page, title_font, button_font, entry_font,
                            description_font, journal_sprites, previous_rect, next_rect, back_rect):
    model = journal_page_model(page)
    draw_space_background(screen, style="journal")
    low = SCREEN_HEIGHT < 500
    draw_fitted_text(screen, "JOURNAL", title_font, UI_CYAN,
                     pygame.Rect(20, 8 if low else 18, SCREEN_WIDTH - 40, 48 if low else 70))
    draw_fitted_text(screen, f"{model['section']}  {model['page'] + 1} / {model['page_count']}",
                     entry_font, UI_CYAN, pygame.Rect(20, 60 if low else 99, SCREEN_WIDTH - 40, 23))
    note = "Enemy colors vary. Outlines show mutations." if model["section"] != "POWERUPS" else "Timed pickups extend effects up to twice their duration."
    draw_fitted_text(screen, note, description_font, UI_MUTED,
                     pygame.Rect(20, 84 if low else 128, SCREEN_WIDTH - 40, 18))
    for index, entry in enumerate(model["entries"]):
        column, row = index % model["columns"], index // model["columns"]
        card = pygame.Rect(model["margin"] + column * (model["card_width"] + model["gap"]),
                           model["start_y"] + row * (model["card_height"] + model["row_gap"]),
                           model["card_width"], model["card_height"])
        name, description = entry[:2]
        powerup = model["section"] == "POWERUPS"
        mutation = model["section"] == "MUTATIONS"
        if powerup:
            accent = POWERUP_COLORS[name]
            label = POWERUP_LABELS[name]
        elif mutation:
            accent, label = entry[2], name
        else:
            kind = name.lower().replace(" ", "_")
            accent = UI_GOLD if kind == "boss" else VISUAL_VARIATIONS[kind][0]["color"]
            label = name
        draw_neon_panel(screen, card, accent, fill=(10, 16, 38), radius=9)
        icon_x = card.x + 24
        if powerup:
            draw_powerup_icon(screen, name, (icon_x, card.y + 20))
        elif mutation:
            sprite = generate_pixel_sprite(STANDARD_ART_V1, UI_VIOLET, 28, 22)
            screen.blit(sprite, (card.x + 10, card.y + 9))
            pygame.draw.rect(screen, accent, (card.x + 7, card.y + 6, 34, 28), 1)
        else:
            frames = journal_sprites[name][0]
            sprite = frames[(pygame.time.get_ticks() // 150) % len(frames)]
            screen.blit(sprite, (card.x + 10, card.y + 7))
        draw_fitted_text(screen, label, entry_font, accent,
                         pygame.Rect(card.x + 49, card.y + 7, card.width - 62, 26), "left")
        draw_journal_description(screen, description, description_font,
                                 card.x + 12, card.y + 40, card.width - 24)
    for rect, text, enabled in ((previous_rect, "PREVIOUS", model["page"] > 0),
                                 (next_rect, "NEXT", model["page"] + 1 < model["page_count"]),
                                 (back_rect, "BACK", True)):
        draw_neon_button(screen, rect, text, button_font, UI_CYAN if text != "BACK" else UI_PINK,
                         enabled=enabled)


def player_spawn_y():
    """Place new, restored and respawning pilots close to the playable bottom."""
    return max(GAMEPLAY_TOP + 2, SCREEN_HEIGHT - PLAYER_HEIGHT - PLAYER_SPAWN_BOTTOM_MARGIN)


def create_player_states(player_count, player_sprites):
    total_width = player_count * PLAYER_WIDTH + (player_count - 1) * 70
    start_x = (SCREEN_WIDTH - total_width) // 2
    players = []

    for index in range(player_count):
        spawn_x = start_x + index * (PLAYER_WIDTH + 70)
        players.append({
            "number": index + 1,
            "color": PLAYER_COLORS[index],
            "score": 0,
            "kills": 0,
            "sprite": player_sprites[index],
            "x": spawn_x,
            "spawn_x": spawn_x,
            "y": player_spawn_y(),
            "lives": STARTING_LIVES,
            "cooldown": 0,
            "ram_bounce_x": 0.0,
            "ram_bounce_y": 0.0,
            "ram_bounce_frames": 0,
            "move_dx": 0.0,
            "move_dy": 0.0,
            "respawn_until": 0,
            "shield_until": 0,
            "rapid_fire_until": 0,
            "speed_boost_until": 0,
            "triple_shot_until": 0,
            "laser_until": 0,
            "magnet_until": 0,
            "bomb_until": 0,
            "bullet_time_until": 0,
            "momentum_stacks": 0,
            "shatter_stacks": 0,
            "shatter_flash_until": 0,
            "momentum_generation": 0,
            "momentum_flash_until": 0,
            "piercing_until": 0,
            "homing_until": 0,
            "lightning_until": 0,
            "score_boost_until": 0,
            "damage_bonus": 0,
            "durability_bonus": 0,
            "durability_damage": 0,
            "durability_regen_until": 0,
            "durability_invuln_until": 0,
            "warp_ready": False,
            "reflector_charges": 0,
            "supply_kills_left": 0,
            "cryo_until": 0,
            "orbit_until": 0,
            "gravity_until": 0,
            "chain_reaction_until": 0,
            "pending_nova": False,
            "nova_charge_until": 0,
            "pending_missiles": False,
            "pending_reflections": [],
            "pending_chain_shots": [],
            "powerup_notice": "",
            "powerup_notice_until": 0,
            "eliminated": False,
        })
        attach_ship_animation(players[-1], PLAYER_ART, PLAYER_COLORS[index],
                              PLAYER_WIDTH, PLAYER_HEIGHT, "player")
        reset_player_animation(players[-1])

    return players


def reset_player_positions(players):
    total_width = len(players) * PLAYER_WIDTH + (len(players) - 1) * 70
    start_x = (SCREEN_WIDTH - total_width) // 2
    for index, player in enumerate(players):
        player["spawn_x"] = start_x + index * (PLAYER_WIDTH + 70)
        player["x"] = player["spawn_x"]
        player["y"] = player_spawn_y()
        player["ram_bounce_x"] = 0
        player["ram_bounce_y"] = 0
        player["ram_bounce_frames"] = 0
        reset_player_animation(player)


def update_player_movement(keys, players):
    now = pygame.time.get_ticks()
    for player in players:
        previous_x = player["x"]
        previous_y = player["y"]
        if player["eliminated"] or player["respawn_until"] > now:
            player["ram_bounce_x"] = 0
            player["ram_bounce_y"] = 0
            player["ram_bounce_frames"] = 0
            player["move_dx"] = 0
            player["move_dy"] = 0
            continue

        left_key, right_key, up_key, down_key, _ = PLAYER_CONTROLS[player["number"] - 1]
        move_speed = (PLAYER_SPEED + (2 if player["speed_boost_until"] > now else 0)
                      + powerup_speed_bonus(player, now))
        if player["ram_bounce_frames"] > 0:
            player["x"] = max(0, min(SCREEN_WIDTH - PLAYER_WIDTH, player["x"] + player["ram_bounce_x"]))
            player["y"] = max(GAMEPLAY_TOP + 2, min(SCREEN_HEIGHT - PLAYER_HEIGHT, player["y"] + player["ram_bounce_y"]))
            player["ram_bounce_x"] *= 0.72
            player["ram_bounce_y"] *= 0.72
            player["ram_bounce_frames"] -= 1
        input_x = int(bool(keys[right_key])) - int(bool(keys[left_key]))
        input_y = int(bool(keys[down_key])) - int(bool(keys[up_key]))
        distance = max(1, math.hypot(input_x, input_y))
        player["x"] = max(0, min(SCREEN_WIDTH - PLAYER_WIDTH, player["x"] + input_x / distance * move_speed))
        player["y"] = max(GAMEPLAY_TOP + 2, min(SCREEN_HEIGHT - PLAYER_HEIGHT, player["y"] + input_y / distance * move_speed))
        player["move_dx"] = player["x"] - previous_x
        player["move_dy"] = player["y"] - previous_y


def check_player_ram_collisions(enemies, particles, enemy_bullets, powerups, players):
    now = pygame.time.get_ticks()
    audio = ensure_audio_manager()

    for player in players:
        if (player["eliminated"] or player["respawn_until"] > now
                or player["shield_until"] <= now or player["ram_bounce_frames"] > 0):
            continue

        player_rect = pygame.Rect(player["x"], player["y"], PLAYER_WIDTH, PLAYER_HEIGHT)
        for enemy in enemies[:]:
            if not player_rect.colliderect(enemy["rect"]):
                continue

            spawn_pop_particles(enemy["rect"].centerx, enemy["rect"].centery, enemy["color"], particles)
            if enemy.get("is_boss", False):
                damage_enemy(enemy, min(1, max(0, enemy["hp"] - 1)), player["number"])
            else:
                damage_enemy(enemy, enemy["hp"], player["number"])
                finish_defeated_enemy(enemy, enemies, players, powerups,
                                      enemy_bullets, particles)

            direction_x = player_rect.centerx - enemy["rect"].centerx
            direction_y = player_rect.centery - enemy["rect"].centery
            distance = math.hypot(direction_x, direction_y)
            if distance == 0:
                direction_y = 1
                distance = 1
            player["ram_bounce_x"] = direction_x / distance * 10
            player["ram_bounce_y"] = direction_y / distance * 10
            player["ram_bounce_frames"] = 10
            player["animation_hit"] = 8
            if audio is not None:
                audio.play(audio.ram)
            break


def draw_spawn_shield(screen, x, y, spark_color, now):
    center = (int(x + PLAYER_WIDTH / 2), int(y + PLAYER_HEIGHT / 2))
    phase = now / 250
    radius = 24 + int((math.sin(phase) + 1) * 2)
    pygame.draw.circle(screen, CYAN, center, radius, 2)
    pygame.draw.circle(screen, LIGHT_BLUE, center, radius - 5, 1)

    for index in range(3):
        angle = phase + index * (2 * math.pi / 3)
        spark_x = center[0] + round(math.cos(angle) * radius)
        spark_y = center[1] + round(math.sin(angle) * radius)
        pygame.draw.circle(screen, spark_color, (spark_x, spark_y), 3)


def draw_powerup_icon(screen, powerup_type, center):
    x, y = center
    if powerup_type == "life":
        pygame.draw.circle(screen, WHITE, (x - 4, y - 3), 5)
        pygame.draw.circle(screen, WHITE, (x + 4, y - 3), 5)
        pygame.draw.polygon(screen, WHITE, [
            (x - 9, y - 1), (x, y + 9), (x + 9, y - 1),
            (x + 7, y - 6), (x + 3, y - 7), (x, y - 3),
            (x - 3, y - 7), (x - 7, y - 6),
        ])
    elif powerup_type == "shield":
        pygame.draw.polygon(screen, WHITE, [
            (x, y - 9), (x + 8, y - 5), (x + 7, y + 2),
            (x, y + 9), (x - 7, y + 2), (x - 8, y - 5),
        ])
    elif powerup_type == "rapid_fire":
        for offset in (-6, 0, 6):
            pygame.draw.line(screen, WHITE, (x - 8, y + offset), (x + 2, y + offset), 2)
            pygame.draw.polygon(screen, WHITE, [
                (x + 1, y + offset - 3),
                (x + 8, y + offset),
                (x + 1, y + offset + 3),
            ])
    elif powerup_type == "triple_shot":
        for offset in (-9, 0, 9):
            pygame.draw.line(screen, WHITE, (x + offset, y + 7), (x + offset, y - 2), 2)
            pygame.draw.polygon(screen, WHITE, [
                (x + offset - 3, y + 1), (x + offset, y - 8), (x + offset + 3, y + 1),
            ])
        pygame.draw.circle(screen, WHITE, (x, y - 11), 3, 1)
    elif powerup_type == "laser":
        pygame.draw.rect(screen, WHITE, (x - 2, y - 9, 4, 18))
        pygame.draw.line(screen, WHITE, (x - 7, y - 1), (x + 7, y - 1), 2)
    elif powerup_type == "magnet":
        pygame.draw.lines(screen, WHITE, False, [
            (x - 7, y - 7), (x - 7, y + 2), (x - 4, y + 7),
            (x + 4, y + 7), (x + 7, y + 2), (x + 7, y - 7),
        ], 3)
        pygame.draw.line(screen, YELLOW, (x - 9, y - 8), (x - 5, y - 8), 3)
        pygame.draw.line(screen, CYAN, (x + 5, y - 8), (x + 9, y - 8), 3)
    elif powerup_type == "bomb":
        pygame.draw.circle(screen, WHITE, (x - 1, y + 2), 6)
        pygame.draw.line(screen, WHITE, (x + 3, y - 3), (x + 7, y - 8), 2)
        pygame.draw.circle(screen, YELLOW, (x + 8, y - 9), 2)
    elif powerup_type == "bullet_time":
        pygame.draw.polygon(screen, WHITE, [
            (x - 7, y - 9), (x + 7, y - 9), (x + 6, y - 5),
            (x + 2, y - 1), (x + 6, y + 5), (x + 7, y + 9),
            (x - 7, y + 9), (x - 6, y + 5), (x - 2, y - 1), (x - 6, y - 5),
        ])
    elif powerup_type == "speed":
        pygame.draw.polygon(screen, WHITE, [
            (x + 2, y - 10), (x - 6, y + 1), (x - 1, y + 1),
            (x - 3, y + 10), (x + 7, y - 3), (x + 2, y - 3),
        ])
    elif powerup_type == "piercing":
        pygame.draw.line(screen, WHITE, (x - 8, y), (x + 8, y), 3)
        pygame.draw.line(screen, WHITE, (x + 2, y - 5), (x + 8, y), 3)
        pygame.draw.line(screen, WHITE, (x + 2, y + 5), (x + 8, y), 3)
    elif powerup_type == "damage_up":
        pygame.draw.line(screen, WHITE, (x - 6, y), (x + 6, y), 3)
        pygame.draw.line(screen, WHITE, (x, y - 6), (x, y + 6), 3)
        pygame.draw.polygon(screen, WHITE, [(x, y - 11), (x - 3, y - 7), (x + 3, y - 7)])
    elif powerup_type == "health_up":
        pygame.draw.polygon(screen, WHITE, [(x - 9, y - 9), (x + 9, y - 9),
                                           (x + 8, y + 3), (x, y + 12), (x - 8, y + 3)], 2)
        pygame.draw.lines(screen, WHITE, False,
                          [(x - 5, y), (x - 1, y + 4), (x + 6, y - 4)], 2)
    elif powerup_type == "lightning":
        pygame.draw.lines(screen, WHITE, False, [
            (x + 2, y - 11), (x - 6, y), (x, y),
            (x - 3, y + 11), (x + 8, y - 3), (x + 2, y - 3),
        ], 3)
    elif powerup_type == "homing":
        pygame.draw.circle(screen, WHITE, (x, y), 7, 2)
        pygame.draw.circle(screen, WHITE, (x, y), 2)
        pygame.draw.line(screen, WHITE, (x + 4, y - 4), (x + 9, y - 9), 2)
    elif powerup_type == "cryo":
        for angle in (0, math.pi / 3, 2 * math.pi / 3):
            dx, dy = round(math.cos(angle) * 10), round(math.sin(angle) * 10)
            pygame.draw.line(screen, WHITE, (x - dx, y - dy), (x + dx, y + dy), 2)
        pygame.draw.circle(screen, WHITE, (x, y), 3, 1)
    elif powerup_type == "orbit_drones":
        pygame.draw.ellipse(screen, WHITE, (x - 10, y - 6, 20, 12), 1)
        pygame.draw.circle(screen, WHITE, (x - 8, y - 4), 3)
        pygame.draw.circle(screen, WHITE, (x + 8, y + 4), 3)
        pygame.draw.circle(screen, WHITE, (x, y), 3)
    elif powerup_type == "supply_beacon":
        pygame.draw.rect(screen, WHITE, (x - 8, y - 7, 16, 14), 2)
        pygame.draw.line(screen, WHITE, (x - 4, y), (x + 4, y), 2)
        pygame.draw.line(screen, WHITE, (x, y - 4), (x, y + 4), 2)
    elif powerup_type == "gravity_well":
        pygame.draw.circle(screen, WHITE, (x, y), 9, 1)
        pygame.draw.circle(screen, WHITE, (x, y), 5, 2)
        pygame.draw.circle(screen, WHITE, (x, y), 1)
    elif powerup_type == "emergency_warp":
        pygame.draw.ellipse(screen, WHITE, (x - 7, y - 10, 14, 20), 2)
        pygame.draw.lines(screen, WHITE, False, [(x - 3, y), (x + 7, y),
                                               (x + 3, y - 4), (x + 7, y), (x + 3, y + 4)], 2)
    elif powerup_type == "nova_pulse":
        for index in range(8):
            angle = index * math.pi / 4
            pygame.draw.line(screen, WHITE, (x + round(math.cos(angle) * 4), y + round(math.sin(angle) * 4)),
                             (x + round(math.cos(angle) * 11), y + round(math.sin(angle) * 11)), 2)
        pygame.draw.circle(screen, WHITE, (x, y), 3)
    elif powerup_type == "missile_swarm":
        for dx, dy in ((-7, 3), (0, -2), (7, 3)):
            pygame.draw.polygon(screen, WHITE, [(x + dx, y + dy - 8),
                (x + dx - 3, y + dy + 4), (x + dx + 3, y + dy + 4)])
    elif powerup_type == "reflector":
        pygame.draw.arc(screen, WHITE, (x - 10, y - 10, 20, 20), -1.25, 1.25, 3)
        pygame.draw.lines(screen, WHITE, False, [(x - 8, y - 5), (x + 3, y), (x - 8, y + 5)], 2)
    elif powerup_type == "chain_reaction":
        pygame.draw.lines(screen, WHITE, False, [(x - 8, y + 5), (x, y - 5), (x + 8, y + 5)], 2)
        for point in ((x - 8, y + 5), (x, y - 5), (x + 8, y + 5)):
            pygame.draw.circle(screen, WHITE, point, 3)
    elif powerup_type == "score_boost":
        points = []
        for index in range(10):
            angle = -math.pi / 2 + index * math.pi / 5
            radius = 9 if index % 2 == 0 else 4
            points.append((x + round(math.cos(angle) * radius),
                           y + round(math.sin(angle) * radius)))
        pygame.draw.polygon(screen, WHITE, points)


POWERUP_VISUAL_PROFILES = {
    "life": ("petal", 5, 0.8),
    "shield": ("hex", 6, -0.7),
    "rapid_fire": ("dash", 3, 2.4),
    "speed": ("comet", 4, 2.0),
    "triple_shot": ("triad", 3, 1.1),
    "laser": ("scan", 2, 1.8),
    "magnet": ("orbit", 2, -0.9),
    "bomb": ("spark", 7, 0.7),
    "bullet_time": ("clock", 8, -0.55),
    "piercing": ("lances", 4, 1.3),
    "damage_up": ("crown", 4, 0.65),
    "health_up": ("health_cross", 4, -0.8),
    "homing": ("reticle", 4, 0.9),
    "lightning": ("zigzag", 5, 2.0),
    "score_boost": ("star", 5, 1.0),
    "cryo": ("frost", 6, -0.6),
    "orbit_drones": ("satellite", 2, 0.8),
    "supply_beacon": ("signal", 3, 1.2),
    "gravity_well": ("spiral", 3, -0.7),
    "emergency_warp": ("portal", 2, -1.5),
    "nova_pulse": ("burst", 8, 0.9),
    "missile_swarm": ("rockets", 3, 1.7),
    "reflector": ("reflect", 3, -0.8),
    "chain_reaction": ("links", 3, 1.1),
}
POWERUP_COLLECTION_PARTICLE_CAP = 96


def draw_powerup_aura(surface, center, color, motif, count, phase, radius=24):
    """Thin, deterministic silhouettes distinguish pickups beyond their colors."""
    cx, cy = center

    def point(angle, distance):
        return (round(cx + math.cos(angle) * distance),
                round(cy + math.sin(angle) * distance))

    if motif in ("hex", "triad", "crown", "star"):
        alternating = motif in ("star", "crown")
        vertices = count * (2 if alternating else 1)
        points = [point(phase + math.tau * index / vertices,
                        radius * (0.76 if alternating and index % 2 else 1))
                  for index in range(vertices)]
        pygame.draw.polygon(surface, color, points, 1)
    elif motif in ("dash", "comet", "lances", "rockets"):
        for index in range(count):
            angle = phase + math.tau * index / count
            end = point(angle, radius)
            start = point(angle - (0.32 if motif in ("dash", "comet") else 0), radius - 7)
            pygame.draw.line(surface, color, start, end, 2 if motif == "dash" else 1)
            if motif in ("rockets", "lances"):
                pygame.draw.lines(surface, color, False,
                                  [point(angle - 0.11, radius - 4), end,
                                   point(angle + 0.11, radius - 4)], 1)
    elif motif == "health_cross":
        for index in range(count):
            x, y = point(phase + math.tau * index / count, radius - 2)
            pygame.draw.line(surface, color, (x - 3, y), (x + 3, y), 1)
            pygame.draw.line(surface, color, (x, y - 3), (x, y + 3), 1)
    elif motif == "frost":
        for index in range(count):
            angle = phase + math.tau * index / count
            pygame.draw.line(surface, color, point(angle, radius - 8), point(angle, radius), 1)
            elbow = point(angle, radius - 4)
            for side in (-1, 1):
                pygame.draw.line(surface, color, elbow,
                                 point(angle + side * 0.15, radius - 7), 1)
    elif motif == "zigzag":
        for index in range(count):
            angle = phase + math.tau * index / count
            pygame.draw.lines(surface, color, False,
                              [point(angle - 0.16, radius - 6), point(angle, radius),
                               point(angle + 0.08, radius - 5), point(angle + 0.20, radius)], 1)
    elif motif == "spiral":
        for arm in range(count):
            points = [point(phase + arm * math.tau / count + step * 0.16,
                            radius - 8 + step * 0.8) for step in range(11)]
            pygame.draw.lines(surface, color, False, points, 1)
    elif motif in ("burst", "spark"):
        for index in range(count):
            angle = phase + math.tau * index / count
            length = 5 + (index % 3 if motif == "spark" else 2)
            pygame.draw.line(surface, color, point(angle, radius - length), point(angle, radius), 1)
            if motif == "spark":
                pygame.draw.circle(surface, color, point(angle + 0.12, radius + 2), 1)
    elif motif == "scan":
        offset = math.sin(phase) * (radius - 4)
        for side in (-1, 1):
            y = round(cy + side * offset)
            half_width = round(math.sqrt(max(0, radius * radius - offset * offset)))
            pygame.draw.line(surface, color, (cx - half_width, y), (cx + half_width, y), 1)
    elif motif in ("portal", "reflect", "signal"):
        for index in range(count):
            angle = phase + math.tau * index / count
            ring = pygame.Rect(cx - radius, cy - radius, radius * 2, radius * 2)
            sweep = 0.95 if motif == "reflect" else 1.55 if motif == "portal" else 0.65
            pygame.draw.arc(surface, color, ring, angle, angle + sweep, 2 if motif == "portal" else 1)
            if motif == "signal":
                inner = ring.inflate(-8, -8)
                pygame.draw.arc(surface, color, inner, angle, angle + sweep, 1)
    elif motif == "clock":
        for index in range(count):
            angle = math.tau * index / count
            pygame.draw.line(surface, color, point(angle, radius - 3), point(angle, radius), 1)
        pygame.draw.line(surface, color, point(phase, radius - 7), point(phase, radius - 1), 2)
    elif motif == "reticle":
        for index in range(count):
            angle = phase * 0.2 + math.tau * index / count
            pygame.draw.lines(surface, color, False,
                              [point(angle - 0.15, radius - 4), point(angle - 0.15, radius),
                               point(angle + 0.15, radius)], 1)
    else:
        # Orbital bodies, linked rings and life petals each have a different orbit.
        for index in range(count):
            angle = phase + math.tau * index / count
            position = point(angle, radius - (2 if motif == "petal" else 0))
            satellite_radius = 4 if motif in ("petal", "links") else 3
            pygame.draw.circle(surface, color, position, satellite_radius, 1)
            if motif == "satellite":
                pygame.draw.line(surface, color, point(angle - 0.30, radius), position, 1)
            elif motif == "orbit":
                pygame.draw.arc(surface, color,
                                (cx - radius, cy - radius, radius * 2, radius * 2),
                                angle - 0.65, angle, 1)


def draw_world_powerup(screen, powerup, now):
    """Render an identifiable animated pickup without changing its hitbox or RNG."""
    key = powerup["type"]
    color = POWERUP_COLORS.get(key, UI_CYAN)
    motif, count, speed = POWERUP_VISUAL_PROFILES.get(key, ("hex", 6, 1.0))
    visual_phase = powerup.get("visual_phase", POWERUP_TYPES.index(key) * 0.73
                              if key in POWERUP_TYPES else 0)
    phase = now / 650 * speed + visual_phase
    surface = pygame.Surface((72, 72), pygame.SRCALPHA)
    center = (36, 36)
    pulse = 0.5 + 0.5 * math.sin(now / 240 + visual_phase)
    pygame.draw.circle(surface, (*color, round(10 + pulse * 9)), center, 26)
    pygame.draw.circle(surface, (*UI_BG, 172), center, 14)
    pygame.draw.circle(surface, (*color, 190), center, 14, 1)
    draw_powerup_aura(surface, center, (*color, 150), motif, count, phase,
                      radius=round(23 + pulse * 2))
    draw_powerup_icon(surface, key, center)
    screen.blit(surface, (powerup["rect"].centerx - 36,
                          powerup["rect"].centery - 36))


def spawn_powerup_pickup_effect(player, powerup_type, particles):
    """A small capped celebration, using the pickup's own visual identity."""
    available = max(0, POWERUP_COLLECTION_PARTICLE_CAP
                    - sum(p.get("kind") == "powerup_pickup" for p in particles))
    if not available:
        return 0
    color = POWERUP_COLORS.get(powerup_type, UI_CYAN)
    motif, count, _ = POWERUP_VISUAL_PROFILES.get(powerup_type, ("hex", 6, 1.0))
    center = (player["x"] + PLAYER_WIDTH / 2, player["y"] + PLAYER_HEIGHT / 2)
    number = min(7, available)
    for index in range(number):
        angle = math.tau * max(0, index - 1) / max(1, number - 1)
        particles.append({
            "kind": "powerup_pickup", "powerup_type": powerup_type,
            "motif": motif, "count": count, "role": "ring" if index == 0 else "spark",
            "x": center[0], "y": center[1],
            "dx": 0 if index == 0 else math.cos(angle) * 2.1,
            "dy": 0 if index == 0 else math.sin(angle) * 2.1,
            "angle": angle, "radius": 6 if index == 0 else 3,
            "color": color, "lifetime": 24 if index == 0 else 20,
            "max_lifetime": 24 if index == 0 else 20,
        })
    return number


def draw_powerup_collection_particle(screen, particle):
    """Lightweight alpha effects, including Frostbite's separate icy Shatter."""
    fraction = max(0, particle["lifetime"] / max(1, particle["max_lifetime"]))
    progress = 1 - fraction
    color = particle["color"]
    if particle.get("kind") == "shatter":
        surface = pygame.Surface((18, 18), pygame.SRCALPHA)
        angle = particle.get("angle", 0) + progress * 1.8
        points = []
        for index, radius in enumerate((7, 2, 7, 2)):
            theta = angle + index * math.pi / 2
            points.append((round(9 + math.cos(theta) * radius * fraction),
                           round(9 + math.sin(theta) * radius * fraction)))
        pygame.draw.polygon(surface, (*color, round(185 * fraction)), points, 1)
        pygame.draw.line(surface, (*UI_TEXT, round(120 * fraction)), points[0], points[2], 1)
        screen.blit(surface, (round(particle["x"]) - 9, round(particle["y"]) - 9))
    elif particle.get("role") == "ring":
        surface = pygame.Surface((80, 80), pygame.SRCALPHA)
        radius = round(8 + 26 * progress)
        draw_powerup_aura(surface, (40, 40), (*color, round(145 * fraction)),
                          particle["motif"], particle["count"],
                          particle.get("angle", 0) + progress * 0.8, radius)
        screen.blit(surface, (round(particle["x"]) - 40, round(particle["y"]) - 40))
    else:
        surface = pygame.Surface((14, 14), pygame.SRCALPHA)
        angle = particle.get("angle", 0)
        end = (round(7 + math.cos(angle) * 4 * fraction),
               round(7 + math.sin(angle) * 4 * fraction))
        pygame.draw.line(surface, (*color, round(175 * fraction)), (7, 7), end, 1)
        pygame.draw.circle(surface, (*UI_TEXT, round(135 * fraction)), end, 1)
        screen.blit(surface, (round(particle["x"]) - 7, round(particle["y"]) - 7))


_HUD_BACKPLATES = {}
_HUD_PANEL_SURFACES = {}
_HUD_FONTS = {}
_GAMEPLAY_UI_SCALE_TARGET = None
_GAMEPLAY_UI_REGION_TARGET = None


def hud_font(size):
    if size not in _HUD_FONTS:
        _HUD_FONTS[size] = pygame.font.SysFont(None, size)
    return _HUD_FONTS[size]


def draw_gameplay_hud_panel(screen, rect, color, radius=6):
    """Cached translucent plates keep both resizing and busy fights inexpensive."""
    key = (rect.size, tuple(color), radius)
    overlay = _HUD_BACKPLATES.get(key)
    if overlay is None:
        if len(_HUD_BACKPLATES) >= 64:
            _HUD_BACKPLATES.clear()
        overlay = pygame.Surface(rect.size, pygame.SRCALPHA)
        pygame.draw.rect(overlay, (*UI_BG, 42), overlay.get_rect(), border_radius=radius)
        pygame.draw.rect(overlay, (*color, 82), overlay.get_rect(), 1, border_radius=radius)
        _HUD_BACKPLATES[key] = overlay
    screen.blit(overlay, rect.topleft)


def draw_hud_label(screen, font, text, color, rect, align="left", max_height=None):
    """Fit text inside its allocated cell without changing the original label."""
    surface = font.render(text, True, color)
    factor = min(1.0, rect.width / max(1, surface.get_width()),
                 (max_height or rect.height) / max(1, surface.get_height()))
    if factor < 1:
        surface = pygame.transform.smoothscale(surface, (
            max(1, round(surface.get_width() * factor)),
            max(1, round(surface.get_height() * factor))))
    position = surface.get_rect(midleft=rect.midleft)
    if align == "right":
        position.midright = rect.midright
    elif align == "center":
        position.center = rect.center
    screen.blit(surface, position)
    return position


def scoreboard_layout(player_number, upgraded=False):
    compact = SCREEN_WIDTH < 1000 or SCREEN_HEIGHT < 600
    margin = 8 if compact else 16
    width = min(286, max(160, (SCREEN_WIDTH - margin * 3) // 2))
    height = (82 if upgraded else 64) if compact else (100 if upgraded else 78)
    x = margin if player_number in (1, 3) else SCREEN_WIDTH - margin - width
    y = margin if player_number in (1, 2) else SCREEN_HEIGHT - margin - height
    return pygame.Rect(x, y, width, height)


def draw_scoreboard(screen, players, font, now=None, background_only=False, foreground_only=False):
    sorted_players = sorted(players, key=lambda player: player["score"], reverse=True)
    ranks = {}
    previous_score = None
    current_rank = 0
    for index, player in enumerate(sorted_players, start=1):
        if player["score"] != previous_score:
            current_rank = index
            previous_score = player["score"]
        ranks[player["number"]] = current_rank
    if now is None:
        now = pygame.time.get_ticks()
    compact = SCREEN_WIDTH < 1000 or SCREEN_HEIGHT < 600
    for player in players:
        upgraded = player.get("durability_bonus", 0) > 0
        panel = scoreboard_layout(player["number"], upgraded)
        if not foreground_only:
            draw_gameplay_hud_panel(screen, panel, player["color"], radius=8)
        if background_only:
            continue
        inset = 8 if compact else 10
        text_height = 15 if compact else 18
        first_y = panel.y + (14 if compact else 19)
        score_cell = pygame.Rect(panel.x + inset, first_y - 10, panel.width * 2 // 3 - inset, 20)
        damage_cell = pygame.Rect(score_cell.right + 3, first_y - 10,
                                  panel.right - inset - score_cell.right - 3, 20)
        draw_hud_label(screen, font,
                       f"P{player['number']}  #{ranks[player['number']]}  {player['score']:08d}",
                       UI_TEXT, score_cell, max_height=text_height)
        draw_hud_label(screen, font, f"DMG UP +{player.get('damage_bonus', 0)}",
                       UI_GOLD, damage_cell, align="right", max_height=text_height)
        if player["eliminated"]:
            status_text, status_color = "OUT", UI_CORAL
        elif player["respawn_until"] > now:
            seconds_left = math.ceil((player["respawn_until"] - now) / 1000)
            status_text, status_color = f"RESPAWN {seconds_left}s", UI_GOLD
        else:
            status_text, status_color = "", WHITE
        lives_y = panel.y + (39 if compact else 55)
        lives_cell = pygame.Rect(panel.x + inset, lives_y - 9, min(100, panel.width // 3), 18)
        lives_rect = draw_hud_label(screen, font, f"LIVES {player['lives']}/{player_life_capacity(player)}",
                                    player["color"], lives_cell, max_height=text_height)
        status_width = min(100, panel.width // 3) if status_text else 0
        status_cell = pygame.Rect(panel.right - inset - status_width, lives_y - 9, status_width, 18)
        capacity = player_life_capacity(player)
        pip_start = lives_rect.right + 6
        available = max(capacity * 3, status_cell.left - pip_start - 5)
        step = min(13, max(3, available // capacity))
        for index in range(capacity):
            pip = pygame.Rect(pip_start + index * step, lives_y - 6, max(2, step - 3), 12)
            color = player["color"] if index < player["lives"] else (25, 36, 58)
            pygame.draw.rect(screen, color, pip, border_radius=2)
        if status_text:
            draw_hud_label(screen, font, status_text, status_color, status_cell,
                           align="right", max_height=text_height)
        if upgraded:
            armor_y = panel.bottom - (12 if compact else 13)
            remaining, capacity = durability_remaining(player), durability_capacity(player)
            name = "DUR" if compact else "DURABILITY"
            label_cell = pygame.Rect(panel.x + inset, armor_y - 8,
                                      min(145, panel.width // 2), 16)
            armor_rect = draw_hud_label(screen, font, f"{name} {remaining}/{capacity}",
                                        UI_CYAN, label_cell, max_height=13 if compact else 15)
            regen = (math.ceil(max(0, player.get("durability_regen_until", 0) - now) / 1000)
                     if player.get("durability_damage", 0) else None)
            regen_text = f"REPAIR {regen}s" if regen is not None else ""
            regen_width = 66 if regen_text else 0
            pip_end = panel.right - inset - regen_width
            pip_start = armor_rect.right + 5
            step = min(12, max(4, (pip_end - pip_start) // capacity))
            for index in range(capacity):
                pip = pygame.Rect(pip_start + index * step, armor_y - 4, max(3, step - 3), 8)
                color = UI_CYAN if index < remaining else (25, 36, 58)
                pygame.draw.rect(screen, color, pip, border_radius=2)
                pygame.draw.rect(screen, UI_CYAN, pip, 1, border_radius=2)
            if regen_text:
                draw_hud_label(screen, font, regen_text, UI_MUTED,
                               pygame.Rect(panel.right - inset - regen_width, armor_y - 8,
                                           regen_width, 16), align="right", max_height=12)


def draw_boss_laser_warning(screen, bullet, now):
    """Show the exact locked beam footprint throughout its harmless windup."""
    rect = bullet["rect"]
    remaining = bullet["remaining_frames"]
    progress = 1 - min(1.0, remaining / bullet.get("warning_frames", BOSS_LASER_WARNING_FRAMES))
    pulse = (math.sin(now / 70) + 1) / 2
    danger = pygame.Surface(rect.size, pygame.SRCALPHA)
    danger.fill((*bullet["color"], round(30 + 40 * progress + 20 * pulse)))
    screen.blit(danger, rect.topleft)
    pygame.draw.rect(screen, UI_GOLD, rect, 2)
    for y in range(rect.top + 8, rect.bottom, 36):
        pygame.draw.line(screen, bullet["color"], (rect.centerx, y),
                         (rect.centerx, min(y + 18, rect.bottom)), 2)
        # Outward chevrons reinforce where to move, even without reading text.
        for side in (-1, 1):
            edge_x = rect.centerx + side * (rect.width // 2 + 9)
            pygame.draw.lines(screen, UI_GOLD, False,
                              [(edge_x - side * 5, y - 4), (edge_x, y),
                               (edge_x - side * 5, y + 4)], 2)
    label = pygame.font.SysFont(None, 24).render(
        f"LASER {remaining / 60:.1f}s", True, UI_GOLD)
    label_rect = label.get_rect(midtop=(rect.centerx, rect.top + 18))
    label_rect.x = max(4, min(SCREEN_WIDTH - label_rect.width - 4, label_rect.x))
    pygame.draw.rect(screen, UI_BG, label_rect.inflate(12, 8), border_radius=4)
    screen.blit(label, label_rect)


def powerup_hud_entries(player, now):
    """Return every active effect; the HUD never silently truncates the list."""
    entries = []
    for key, until_key in POWERUP_TIMER_KEYS.items():
        until = player.get(until_key, 0)
        if until > now:
            seconds = max(1, math.ceil((until - now) / 1000))
            entries.append((key, f"{POWERUP_TIMER_LABELS[key]} {seconds}s", POWERUP_COLORS[key]))
    for key, value, label in (
        ("emergency_warp", player.get("warp_ready", False), "WARP READY"),
        ("reflector", player.get("reflector_charges", 0), f"REFLECT {player.get('reflector_charges', 0)}"),
        ("supply_beacon", player.get("supply_kills_left", 0), f"SUPPLY {player.get('supply_kills_left', 0)}"),
        ("missile_swarm", player.get("pending_missiles", False), "MISSILES READY"),
    ):
        if value:
            entries.append((key, label, POWERUP_COLORS[key]))
    nova_seconds = nova_countdown(player, now)
    if nova_seconds:
        entries.append(("nova_pulse", f"NOVA {nova_seconds}", POWERUP_COLORS["nova_pulse"]))
    stacks = momentum_stacks(player, now)
    if stacks:
        entries.append(("momentum", f"MOMENTUM x{stacks}", UI_CYAN))
    frost_stacks = shatter_stacks(player, now)
    if frost_stacks:
        entries.append(("shatter", f"SHATTER x{frost_stacks}", POWERUP_COLORS["cryo"]))
    return entries


def powerup_hud_metrics(player_number, entry_count, has_notice=False):
    """Choose readable columns, then cycle pages only on very small canvases."""
    compact = SCREEN_WIDTH < 1000 or SCREEN_HEIGHT < 600
    reserved_score = scoreboard_layout(player_number, upgraded=True)
    margin = 8 if compact else 16
    width = min(360, max(180, (SCREEN_WIDTH - margin * 3) // 2))
    top = margin + reserved_score.height + 8
    maximum_height = max(44, SCREEN_HEIGHT // 2 - 8 - top)
    row_height = 13 if SCREEN_HEIGHT < 450 else 14 if compact else 18
    header_height = 20 if compact else 26
    notice_height = (14 if compact else 18) if has_notice else 0
    maximum_columns = min(4, max(2, (width - 16) // (82 if compact else 100)))
    columns = 2
    for columns in range(2, maximum_columns + 1):
        rows = math.ceil(entry_count / columns)
        if header_height + rows * row_height + notice_height <= maximum_height:
            break
    rows_available = max(1, (maximum_height - header_height - notice_height) // row_height)
    capacity = max(columns, rows_available * columns)
    shown_count = min(entry_count, capacity)
    height = header_height + math.ceil(shown_count / columns) * row_height + notice_height
    x = margin if player_number in (1, 3) else SCREEN_WIDTH - margin - width
    y = top if player_number in (1, 2) else SCREEN_HEIGHT - top - height
    return {"panel": pygame.Rect(x, y, width, height), "columns": columns,
            "row_height": row_height, "header_height": header_height,
            "capacity": capacity, "compact": compact}


def powerup_hud_layout(player_number, entry_count, has_notice=False):
    metrics = powerup_hud_metrics(player_number, entry_count, has_notice)
    return metrics["panel"], metrics["columns"], metrics["row_height"]


def powerup_hud_page(player, now, metrics=None):
    entries = powerup_hud_entries(player, now)
    metrics = metrics or powerup_hud_metrics(player["number"], len(entries))
    page_count = max(1, math.ceil(len(entries) / metrics["capacity"]))
    page = (now // 2600) % page_count
    first = page * metrics["capacity"]
    return entries[first:first + metrics["capacity"]], page, page_count


def compact_powerup_label(key, text):
    aliases = {"bullet_time": "TIME", "chain_reaction": "CHAIN", "orbit_drones": "DRONES",
               "score_boost": "2X", "triple_shot": "TRIPLE", "lightning": "LIGHTNING",
               "emergency_warp": "WARP", "supply_beacon": "SUPPLY", "missile_swarm": "MISSILES",
               "momentum": "MOM", "shatter": "SHATTER", "cryo": "FROST"}
    if key in POWERUP_TIMER_LABELS:
        original = POWERUP_TIMER_LABELS[key]
        return aliases.get(key, original) + text[len(original):]
    if key == "momentum":
        return text.replace("MOMENTUM", "MOM")
    if key == "emergency_warp":
        return "WARP READY"
    if key == "missile_swarm":
        return "MISSILES"
    return text


def draw_powerup_hud(screen, player, now, font):
    """Readable edge docks adapt columns; compact cycling never loses an effect."""
    entries = powerup_hud_entries(player, now)
    notice = (player.get("powerup_notice", "")
              if player.get("powerup_notice_until", 0) > now else "")
    if not entries and not notice:
        return None
    metrics = powerup_hud_metrics(player["number"], len(entries), bool(notice))
    panel = metrics["panel"]
    key = (player["number"], panel.size)
    overlay = _HUD_PANEL_SURFACES.get(key)
    if overlay is None:
        if len(_HUD_PANEL_SURFACES) >= 16:
            _HUD_PANEL_SURFACES.clear()
        overlay = pygame.Surface(panel.size, pygame.SRCALPHA)
        _HUD_PANEL_SURFACES[key] = overlay
    overlay.fill((0, 0, 0, 0))
    pygame.draw.rect(overlay, (*UI_BG, 42), overlay.get_rect(), border_radius=6)
    pygame.draw.rect(overlay, (*player["color"], 82), overlay.get_rect(), 1, border_radius=6)
    shown, page, page_count = powerup_hud_page(player, now, metrics)
    title = f"P{player['number']} POWERUPS ({len(entries)})"
    if page_count > 1:
        title += f"  {page + 1}/{page_count}"
    draw_hud_label(overlay, font, title, player["color"],
                   pygame.Rect(8, 3, panel.width - 16, 16), max_height=13)
    cell_width = (panel.width - 16) // metrics["columns"]
    for index, (effect_key, text, color) in enumerate(shown):
        column, row = index % metrics["columns"], index // metrics["columns"]
        if metrics["compact"]:
            text = compact_powerup_label(effect_key, text)
        draw_hud_label(overlay, font, text, color,
                       pygame.Rect(8 + column * cell_width,
                                   metrics["header_height"] + row * metrics["row_height"],
                                   cell_width - 5, metrics["row_height"]),
                       max_height=metrics["row_height"] - 2)
    if notice:
        draw_hud_label(overlay, font, notice, UI_TEXT,
                       pygame.Rect(8, panel.height - (14 if metrics["compact"] else 17),
                                   panel.width - 16, 14), max_height=12 if metrics["compact"] else 13)
    screen.blit(overlay, panel.topleft)
    return panel


def draw_nova_countdown(screen, player, now):
    """A faint clear-radius guide and readable countdown follow the pilot."""
    seconds = nova_countdown(player, now)
    if not seconds:
        return
    center = (round(player["x"] + PLAYER_WIDTH / 2), round(player["y"] + PLAYER_HEIGHT / 2))
    radius = NOVA_PULSE_RADIUS
    size = radius * 2 + 8
    effects = pygame.Surface((size, size), pygame.SRCALPHA)
    local_center = (size // 2, size // 2)
    accent = POWERUP_COLORS["nova_pulse"]
    pygame.draw.circle(effects, (*accent, 4), local_center, radius)
    ring = pygame.Rect(4, 4, radius * 2, radius * 2)
    for index in range(12):
        angle = index * math.tau / 12 + now / 2200
        pygame.draw.arc(effects, (*accent, 90), ring, angle, angle + 0.15, 1)
    progress = 1 - max(0, player["nova_charge_until"] - now) / NOVA_COUNTDOWN_MS
    pygame.draw.circle(effects, (*accent, 110), local_center, round(24 + progress * 23), 1)
    screen.blit(effects, (center[0] - local_center[0], center[1] - local_center[1]))
    font = pygame.font.SysFont(None, 38)
    label = font.render(f"NOVA {seconds}", True, accent)
    outline = font.render(f"NOVA {seconds}", True, UI_BG)
    label_rect = label.get_rect(midbottom=(center[0], center[1] - 35))
    label_rect.clamp_ip(pygame.Rect(4, GAMEPLAY_TOP + 4, SCREEN_WIDTH - 8,
                                  SCREEN_HEIGHT - GAMEPLAY_TOP - 8))
    for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
        screen.blit(outline, label_rect.move(dx, dy))
    screen.blit(label, label_rect)


def draw_support_powerups(screen, player, now):
    """Distinct, restrained active effects; all are below hostile shots."""
    draw_nova_countdown(screen, player, now)
    center = (round(player["x"] + PLAYER_WIDTH / 2), round(player["y"] + PLAYER_HEIGHT / 2))
    radius = max(64,
                 GRAVITY_FIELD_RADIUS + 4 if player.get("gravity_until", 0) > now else 0,
                 BULLET_TIME_RADIUS + 4 if player.get("bullet_time_until", 0) > now else 0)
    effects = pygame.Surface((radius * 2 + 4, radius * 2 + 4), pygame.SRCALPHA)
    cx = cy = radius + 2
    phase = now / 650 + player["number"] * 0.8

    def color(key, alpha=135):
        return (*POWERUP_COLORS[key], alpha)

    def point(angle, distance):
        return round(cx + math.cos(angle) * distance), round(cy + math.sin(angle) * distance)

    if player.get("gravity_until", 0) > now:
        field_radius = GRAVITY_FIELD_RADIUS
        pygame.draw.circle(effects, color("gravity_well", 7), (cx, cy), field_radius)
        ring = pygame.Rect(cx - field_radius, cy - field_radius, field_radius * 2, field_radius * 2)
        for index in range(4):
            start = now / 700 + index * math.pi / 2
            pygame.draw.arc(effects, color("gravity_well", 115), ring, start, start + 0.62, 1)
            pygame.draw.circle(effects, color("gravity_well", 155), point(-start, field_radius - 7), 2)
    if player.get("bullet_time_until", 0) > now:
        field_radius = BULLET_TIME_RADIUS
        pygame.draw.circle(effects, color("bullet_time", 6), (cx, cy), field_radius)
        pygame.draw.circle(effects, color("bullet_time", 100), (cx, cy), field_radius, 1)
        for index in range(12):
            angle = index * math.tau / 12 - now / 2600
            pygame.draw.line(effects, color("bullet_time", 145),
                             point(angle, field_radius - 5), point(angle, field_radius), 1)
        hand_angle = -math.pi / 2 + now / 1400
        pygame.draw.line(effects, color("bullet_time", 75), (cx, cy), point(hand_angle, 20), 1)
    if player.get("cryo_until", 0) > now:
        frost_stacks = shatter_stacks(player, now)
        # Tiny snow flecks identify Frostbite even before its first kill.
        for index in range(6):
            angle = -phase + index * math.tau / 6
            x, y = point(angle, 31)
            pygame.draw.line(effects, color("cryo", 100), (x - 2, y), (x + 2, y), 1)
            pygame.draw.line(effects, color("cryo", 100), (x, y - 2), (x, y + 2), 1)
        # Each earned Shatter stack adds a separate orbiting ice crystal.
        for index in range(frost_stacks):
            angle = phase * 0.65 + index * math.tau / max(1, frost_stacks)
            x, y = point(angle, 43)
            pygame.draw.polygon(effects, color("cryo", 180),
                                ((x, y - 5), (x + 3, y), (x, y + 5), (x - 3, y)), 1)
            pygame.draw.line(effects, (*UI_TEXT, 150), (x, y - 2), (x, y + 2), 1)
        if player.get("shatter_flash_until", 0) > now:
            flash_radius = 23 + round((player["shatter_flash_until"] - now) / 40)
            pygame.draw.circle(effects, color("cryo", 100), (cx, cy), flash_radius, 1)
    if player.get("rapid_fire_until", 0) > now:
        travel = (now // 35) % 15
        for side in (-1, 1):
            for step in range(3):
                y = cy - 5 - (travel + step * 5) % 18
                pygame.draw.line(effects, color("rapid_fire", 160 - step * 25),
                                 (cx + side * 19, y), (cx + side * 19, y - 3), 1)
    if player.get("speed_boost_until", 0) > now:
        for side in (-1, 1):
            pygame.draw.lines(effects, color("speed", 120), False,
                              ((cx + side * 16, cy + 5),
                               (cx + side * 21, cy + 20),
                               (cx + side * 18, cy + 30)), 1)
    if player.get("triple_shot_until", 0) > now:
        for offset in (-12, 0, 12):
            pygame.draw.line(effects, color("triple_shot", 120),
                             (cx + offset, cy - 18), (cx + offset, cy - 24), 1)
    if player.get("laser_until", 0) > now:
        for offset in (-4, 4):
            pygame.draw.line(effects, color("laser", 145),
                             (cx + offset, cy - 11), (cx + offset, cy - 26), 1)
    if player.get("magnet_until", 0) > now:
        ring = pygame.Rect(cx - 34, cy - 26, 68, 52)
        for offset in (0, math.pi):
            pygame.draw.arc(effects, color("magnet", 100), ring,
                            phase + offset, phase + offset + 0.65, 1)
    if player.get("bomb_until", 0) > now:
        for side in (-1, 1):
            pygame.draw.circle(effects, color("bomb", 140), (cx + side * 23, cy + 8), 4, 1)
            pygame.draw.line(effects, color("bomb", 140),
                             (cx + side * 23, cy + 3), (cx + side * 25, cy), 1)
    if player.get("piercing_until", 0) > now:
        pygame.draw.lines(effects, color("piercing", 165), False,
                          ((cx - 4, cy - 24), (cx, cy - 31), (cx + 4, cy - 24)), 1)
    if player.get("homing_until", 0) > now:
        target = (cx, cy - 34)
        pygame.draw.circle(effects, color("homing", 125), target, 5, 1)
        pygame.draw.line(effects, color("homing", 125), (cx - 8, cy - 34), (cx - 4, cy - 34), 1)
        pygame.draw.line(effects, color("homing", 125), (cx + 4, cy - 34), (cx + 8, cy - 34), 1)
    if player.get("lightning_until", 0) > now:
        flicker = round(math.sin(now / 90) * 2)
        for side in (-1, 1):
            pygame.draw.lines(effects, color("lightning", 145), False,
                              ((cx + side * 14, cy - 8), (cx + side * (22 + flicker), cy - 4),
                               (cx + side * 18, cy + 2), (cx + side * 25, cy + 8)), 1)
    if player.get("score_boost_until", 0) > now:
        for offset in (0, math.pi):
            x, y = point(phase * 0.7 + offset, 39)
            pygame.draw.polygon(effects, color("score_boost", 145),
                                ((x, y - 3), (x + 3, y), (x, y + 3), (x - 3, y)), 1)
    if player.get("chain_reaction_until", 0) > now:
        points = [(cx - 18, cy + 25), (cx, cy + 32), (cx + 18, cy + 25)]
        pygame.draw.lines(effects, color("chain_reaction", 110), False, points, 1)
        for position in points:
            pygame.draw.circle(effects, color("chain_reaction", 145), position, 2, 1)
    if player.get("warp_ready", False):
        pygame.draw.arc(effects, color("emergency_warp", 110),
                        pygame.Rect(cx - 23, cy - 31, 46, 62), 0.1, 1.2, 1)
        pygame.draw.arc(effects, color("emergency_warp", 110),
                        pygame.Rect(cx - 23, cy - 31, 46, 62), math.pi + 0.1, math.pi + 1.2, 1)
    for index in range(min(3, player.get("reflector_charges", 0))):
        angle = -math.pi / 2 + (index - 1) * 0.55
        x, y = point(angle, 26)
        pygame.draw.polygon(effects, color("reflector", 155),
                            ((x, y - 4), (x + 3, y), (x, y + 4), (x - 3, y)), 1)
    if player.get("supply_kills_left", 0):
        for index in range(3):
            pygame.draw.line(effects, color("supply_beacon", 125 - index * 20),
                             (cx - 5 + index * 5, cy + 21), (cx - 5 + index * 5, cy + 25), 1)
    if player.get("pending_missiles", False):
        for side in (-1, 1):
            pygame.draw.lines(effects, color("missile_swarm", 145), False,
                              ((cx + side * 27, cy + 15), (cx + side * 27, cy + 7),
                               (cx + side * 24, cy + 11)), 1)
    for index in range(min(MAX_DAMAGE_BONUS, player.get("damage_bonus", 0))):
        pygame.draw.circle(effects, color("damage_up", 160), (cx - 5 + index * 5, cy + 6), 1)
    stacks = momentum_stacks(player, now)
    if stacks:
        momentum_color = blend_color(UI_CYAN, UI_VIOLET, min(1, stacks / BULLET_TIME_MAX_STACKS))
        for segment in range(min(5, 1 + stacks // 4)):
            travel = ((now // 48 + segment * 11) % 24)
            pygame.draw.circle(effects, (*momentum_color, 150),
                               (cx, cy + PLAYER_HEIGHT // 2 + 10 + travel),
                               max(1, 3 - segment // 2), 1)
        if player.get("momentum_flash_until", 0) > now:
            flash_radius = 20 + round((player["momentum_flash_until"] - now) / 45)
            pygame.draw.circle(effects, (*UI_CYAN, 100), (cx, cy), flash_radius, 1)
    screen.blit(effects, (center[0] - cx, center[1] - cy))
    if player.get("orbit_until", 0) > now:
        drone_color = POWERUP_COLORS.get("orbit_drones", UI_CYAN)
        for position in orbit_drone_positions(player, now):
            pygame.draw.line(screen, blend_color(drone_color, UI_BG, 0.65), center, position, 1)
            draw_soft_glow(screen, position, drone_color, radius=12, strength=35)
            drone = pygame.Rect(0, 0, 11, 9)
            drone.center = position
            pygame.draw.rect(screen, UI_BG, drone.inflate(4, 4), border_radius=3)
            pygame.draw.rect(screen, drone_color, drone, 2, border_radius=2)
            pygame.draw.circle(screen, UI_TEXT, position, 2)


def draw_aimed_projectile_trail(screen, bullet):
    """A short direction cue uses existing geometry, without extra particles."""
    if not bullet.get("aimed_shot") or bullet.get("laser_state") is not None:
        return
    dx, dy = bullet.get("dx", 0), bullet.get("dy", 0)
    if bullet.get("wave"):
        dx += math.sin(bullet.get("wave_phase", 0)) * bullet.get("wave_amplitude", 3.5)
    speed = math.hypot(dx, dy)
    if speed < 0.001:
        return
    center = bullet["rect"].center
    length = 12 + min(10, bullet["rect"].width / 2)
    tail = (round(center[0] - dx / speed * length),
            round(center[1] - dy / speed * length))
    pygame.draw.line(screen, blend_color(bullet["color"], UI_BG, 0.55), tail, center, 2)
    pygame.draw.line(screen, bullet["color"],
                     (round((tail[0] + center[0]) / 2), round((tail[1] + center[1]) / 2)),
                     center, 1)


def draw_homing_projectile(screen, bullet, color, hostile=False):
    """Rotate a guided shot toward its velocity without advancing its state."""
    rect = bullet["rect"]
    heading = bullet.get("heading")
    if heading is None:
        velocity_x = bullet.get("dx", bullet.get("vx", 0))
        velocity_y = bullet.get("dy", bullet.get("vy", -1))
        heading = math.atan2(velocity_y, velocity_x)
    if hostile:
        # Enemy seekers retain their existing square collision footprint.
        # The arrow fits inside that square even at diagonal headings.
        width = max(4, round(rect.width * 0.70))
        height = max(5, round(rect.height * 0.70))
    else:
        width, height = bullet.get("projectile_base_size", rect.size)
    sprite = pygame.Surface((width, height), pygame.SRCALPHA)
    if bullet.get("type") == "bomb" and not hostile:
        draw_soft_glow(screen, rect.center, color, radius=17, strength=65)
        pygame.draw.ellipse(sprite, color, sprite.get_rect())
        if width > 6 and height > 6:
            pygame.draw.ellipse(sprite, UI_GOLD, sprite.get_rect().inflate(-6, -6), 2)
        pygame.draw.line(sprite, UI_TEXT, (width // 2, 0), (width // 2, max(2, height // 3)), 2)
    else:
        nose = (width // 2, 0)
        pygame.draw.polygon(sprite, color, (
            nose, (width - 1, max(1, height // 3)),
            (max(0, width - 2), height - 1), (width // 2, max(1, height - 3)),
            (min(width - 1, 1), height - 1), (0, max(1, height // 3)),
        ))
        core_color = blend_color(color, UI_TEXT, 0.65) if hostile else UI_TEXT
        pygame.draw.line(sprite, core_color, (width // 2, max(1, height // 4)),
                         (width // 2, max(1, height - 3)), 2 if width >= 6 else 1)
        if bullet.get("type") == "missile":
            pygame.draw.line(sprite, UI_GOLD, (width // 2, height - 3),
                             (width // 2, height - 1), 2)
    rotated = pygame.transform.rotate(sprite, -math.degrees(heading) - 90)
    draw_rect = rotated.get_rect(center=rect.center)
    screen.blit(rotated, draw_rect)
    return draw_rect


def draw_gameplay_ui_underlay(screen, players, font, now, round_num, save_error=None):
    """Render status UI in its own coordinate space before the arena objects."""
    with ui_dimensions(screen.get_size()):
        sector_color = SECTOR_COLORS[(sector_for_round(round_num) - 1) % len(SECTOR_COLORS)]
        round_color = UI_CORAL if round_num % 5 == 0 else sector_color
        compact = SCREEN_WIDTH < 900 or SCREEN_HEIGHT < 500
        round_label = f"W{round_num}" if compact else (
            f"BOSS WAVE {round_num}" if round_num % 5 == 0 else f"WAVE {round_num}")
        profile = milestone_boss_profile(round_num)
        if profile is not None and not compact:
            round_label = f"{profile['name']} / W{round_num}"
        round_font = hud_font(21) if compact else font
        round_text = round_font.render(round_label, True, round_color)
        round_badge = round_text.get_rect(midtop=(SCREEN_WIDTH // 2, 10)).inflate(
            14 if compact else 34, 8 if compact else 16)
        sector_font = hud_font(17 if compact else 23)
        sector_label = f"S{sector_for_round(round_num)}" if compact else f"SECTOR {sector_for_round(round_num):02d}"
        sector_text = sector_font.render(sector_label, True, UI_GOLD)
        sector_badge = sector_text.get_rect(midtop=(SCREEN_WIDTH // 2, round_badge.bottom + 3)).inflate(
            10 if compact else 24, 4 if compact else 6)
        draw_gameplay_hud_panel(screen, round_badge, round_color, radius=5 if compact else 9)
        draw_gameplay_hud_panel(screen, sector_badge, UI_GOLD, radius=4)
        screen.blit(round_text, round_text.get_rect(center=round_badge.center))
        screen.blit(sector_text, sector_text.get_rect(center=sector_badge.center))
        tick_width, tick_gap = (7, 3) if compact else (25, 6)
        meter_width = 5 * tick_width + 4 * tick_gap
        meter_y = sector_badge.bottom + 4
        for index in range(5):
            dot = pygame.Rect(SCREEN_WIDTH // 2 - meter_width // 2 + index * (tick_width + tick_gap),
                              meter_y, tick_width, 3)
            reached = index <= ((round_num - 1) % WAVES_PER_SECTOR)
            meter_color = UI_CORAL if round_num % WAVES_PER_SECTOR == 0 else UI_MINT
            pygame.draw.rect(screen, meter_color if reached else (42, 62, 94), dot, border_radius=2)
        draw_scoreboard(screen, players, font, now)
        if save_error:
            cell = pygame.Rect(12, meter_y + 10, SCREEN_WIDTH - 24, 18)
            draw_hud_label(screen, font, save_error, UI_CORAL, cell, align="center", max_height=16)
        for player in players:
            if not player["eliminated"]:
                draw_powerup_hud(screen, player, now, font)


def draw_gameplay_ui_overlay(screen, exit_button_rect, pause_button_rect, font, paused,
                              save_error=None):
    """Pause controls use the same GUI coordinates as pointer hit testing."""
    with ui_dimensions(screen.get_size()):
        if paused:
            draw_pause_overlay(screen, font, save_error)
            draw_exit_button(screen, exit_button_rect, font)
        draw_pause_button(screen, pause_button_rect, font, paused)


def composite_gameplay_ui(screen, ui_surface, bounds=None):
    """Scale into reusable destinations; sparse foregrounds may supply a crop."""
    global _GAMEPLAY_UI_SCALE_TARGET, _GAMEPLAY_UI_REGION_TARGET
    if bounds is not None:
        bounds = pygame.Rect(bounds).clip(ui_surface.get_rect())
        if not bounds.width or not bounds.height:
            return
        if screen.get_size() == ui_surface.get_size():
            screen.blit(ui_surface, bounds.topleft, bounds)
            return
        factor_x = screen.get_width() / ui_surface.get_width()
        factor_y = screen.get_height() / ui_surface.get_height()
        target_rect = pygame.Rect(round(bounds.x * factor_x), round(bounds.y * factor_y),
                                  max(1, round(bounds.width * factor_x)),
                                  max(1, round(bounds.height * factor_y)))
        if (_GAMEPLAY_UI_REGION_TARGET is None
                or _GAMEPLAY_UI_REGION_TARGET.get_size() != target_rect.size):
            _GAMEPLAY_UI_REGION_TARGET = pygame.Surface(target_rect.size, pygame.SRCALPHA)
        pygame.transform.smoothscale(ui_surface.subsurface(bounds), target_rect.size,
                                     _GAMEPLAY_UI_REGION_TARGET)
        screen.blit(_GAMEPLAY_UI_REGION_TARGET, target_rect.topleft)
        return
    if screen.get_size() == ui_surface.get_size():
        screen.blit(ui_surface, (0, 0))
        return
    if (_GAMEPLAY_UI_SCALE_TARGET is None
            or _GAMEPLAY_UI_SCALE_TARGET.get_size() != screen.get_size()):
        _GAMEPLAY_UI_SCALE_TARGET = pygame.Surface(screen.get_size(), pygame.SRCALPHA)
    pygame.transform.smoothscale(ui_surface, screen.get_size(), _GAMEPLAY_UI_SCALE_TARGET)
    screen.blit(_GAMEPLAY_UI_SCALE_TARGET, (0, 0))


def draw_hostile_projectiles(screen, enemy_bullets, now, enemies=()):
    """Draw threats without updating them, so native HUDs cannot obscure shots."""
    for enemy in enemies:
        if enemy.get("milestone_kind"):
            draw_milestone_attack_warning(screen, enemy)
    for bullet in enemy_bullets:
        draw_aimed_projectile_trail(screen, bullet)
        if bullet.get("laser_state") == "warning":
            draw_boss_laser_warning(screen, bullet, now)
        elif bullet.get("laser_state") == "active":
            beam_surface = pygame.Surface(bullet["rect"].size, pygame.SRCALPHA)
            beam_surface.fill((*bullet["color"], 105))
            screen.blit(beam_surface, bullet["rect"].topleft)
            pygame.draw.rect(screen, bullet["color"], bullet["rect"], 2)
        elif bullet.get("homing"):
            draw_homing_projectile(screen, bullet, bullet["color"], hostile=True)
        else:
            pygame.draw.rect(screen, bullet["color"], bullet["rect"], border_radius=3)
            if bullet["rect"].width >= 5 and bullet["rect"].height >= 5:
                pygame.draw.rect(screen, blend_color(bullet["color"], UI_TEXT, 0.65),
                                 bullet["rect"].inflate(-3, -3), border_radius=2)


def draw_gameplay(screen, enemies, enemy_bullets, player_bullets, bunkers, particles, powerups, players, exit_button_rect, pause_button_rect, font, paused=False, paused_at=None, time_override=None, round_num=1, save_error=None, ui_surface=None, defer_ui_overlay=False, defer_native_ui=False):
    now = paused_at if paused and paused_at is not None else pygame.time.get_ticks()
    if time_override is not None:
        now = time_override
    draw_space_background(screen, "gameplay", now)
    if ui_surface is None:
        if not defer_native_ui:
            draw_gameplay_ui_underlay(screen, players, font, now, round_num, save_error)
    else:
        ui_surface.fill((0, 0, 0, 0))
        draw_gameplay_ui_underlay(ui_surface, players, font, now, round_num, save_error)
        if not defer_native_ui:
            composite_gameplay_ui(screen, ui_surface)
    for enemy in enemies:
        draw_animated_enemy(screen, enemy)
        if enemy_cryo_multiplier(enemy, now) < 1:
            pygame.draw.rect(screen, POWERUP_COLORS["cryo"], enemy["rect"].inflate(5, 5), 1)
        mutation_color = MUTATION_COLORS.get(enemy.get("mutation"))
        if mutation_color:
            pygame.draw.rect(screen, mutation_color, enemy["rect"].inflate(6, 6), 2)
        if enemy.get("shield_charges", 0) > 0:
            pygame.draw.rect(
                screen,
                enemy.get("shield_color", LIGHT_BLUE),
                enemy["rect"].inflate(8, 8),
                2,
            )

        # Render Boss Health Bar
        if enemy.get("is_boss", False):
            bar_w = enemy["rect"].width
            bar_h = 6
            bar_x = enemy["rect"].x
            bar_y = enemy["rect"].y - 12
            health_ratio = enemy["hp"] / enemy["max_hp"]

            pygame.draw.rect(screen, (51, 23, 49), (bar_x, bar_y, bar_w, bar_h), border_radius=3)
            health_color = blend_color(UI_CORAL, UI_MINT, health_ratio)
            pygame.draw.rect(screen, health_color,
                             (bar_x, bar_y, max(0, int(bar_w * health_ratio)), bar_h), border_radius=3)
            pygame.draw.rect(screen, UI_TEXT, (bar_x, bar_y, bar_w, bar_h), 1, border_radius=3)
            boss_phase = 3 if health_ratio <= 0.35 else 2 if health_ratio <= 0.65 else 1
            phase_label = pygame.font.SysFont(None, 16).render(
                f"PHASE {boss_phase}" if bar_w > 72 else f"P{boss_phase}",
                True, UI_CORAL if boss_phase == 3 else UI_GOLD if boss_phase == 2 else UI_TEXT)
            screen.blit(phase_label, phase_label.get_rect(midbottom=(bar_x + bar_w // 2, bar_y - 3)))
            if enemy.get("boss_name"):
                name = hud_font(22).render(enemy["boss_name"], True, enemy["color"])
                name_rect = name.get_rect(midbottom=(enemy["rect"].centerx, bar_y - 20))
                name_rect.clamp_ip(screen.get_rect().inflate(-8, -8))
                screen.blit(name, name_rect)

    # Projectiles and effects remain visible across the entire screen.
    player_colors = {player["number"]: player["color"] for player in players}
    for bullet in player_bullets:
        rect = bullet["rect"] if isinstance(bullet, dict) else bullet
        shot_color = player_projectile_color(bullet, player_colors)
        if isinstance(bullet, dict):
            if bullet.get("type") == "laser":
                pygame.draw.rect(screen, blend_color(shot_color, UI_GOLD, 0.4), rect, 2)
                pygame.draw.line(screen, UI_TEXT, rect.midtop, rect.midbottom, 2)
                # HOMING + LASER still adds an aiming tendril. LIGHTNING is
                # a separate optional chain effect with its own damage/visuals.
                # A normal
                # beam still pierces vertically through every enemy in its path.
                points = laser_homing_points(bullet, now)
                if len(points) >= 2:
                    pygame.draw.lines(screen, shot_color, False, points, 6)
                    pygame.draw.lines(screen, UI_TEXT, False, points, 2)
                    pygame.draw.circle(screen, shot_color, points[-1], 9, 2)
            elif bullet.get("homing"):
                draw_homing_projectile(screen, bullet, shot_color)
            elif bullet.get("type") == "bomb":
                draw_soft_glow(screen, rect.center, shot_color, radius=17, strength=65)
                pygame.draw.ellipse(screen, shot_color, rect)
                pygame.draw.ellipse(screen, UI_GOLD, rect.inflate(-6, -6), 2)
            else:
                pygame.draw.rect(screen, shot_color, rect, border_radius=2)
                pygame.draw.line(screen, UI_TEXT, (rect.centerx, rect.top + 2),
                                 (rect.centerx, rect.bottom - 2), 2)
        else:
            pygame.draw.rect(screen, shot_color, rect, border_radius=2)

    for powerup in powerups:
        draw_world_powerup(screen, powerup, now)

    for block in bunkers:
        bunker_index = min(3, max(0, block.centerx * 4 // SCREEN_WIDTH))
        bunker_color = (UI_MINT, UI_CYAN, UI_VIOLET, UI_PINK)[bunker_index]
        shade = 0.25 if (block.x // BLOCK_SIZE + block.y // BLOCK_SIZE) % 2 else 0.08
        pygame.draw.rect(screen, blend_color(bunker_color, UI_BG, shade), block, border_radius=1)
        pygame.draw.line(screen, blend_color(bunker_color, UI_TEXT, 0.4), block.topleft, block.topright)

    update_and_draw_particles(screen, particles, advance=not paused)

    for player in players:
        if player["eliminated"] or player["respawn_until"] > now:
            continue
        draw_support_powerups(screen, player, now)
        draw_animated_player(screen, player, now)
        if player["shield_until"] > now:
            draw_spawn_shield(screen, player["x"], player["y"], player["color"], now)
    # Native presentation adds threats above the native status layer, avoiding
    # a GUI-to-world-to-window round trip. Legacy direct draws keep their order.
    if not defer_native_ui:
        draw_hostile_projectiles(screen, enemy_bullets, now, enemies)
    if ui_surface is None and not defer_native_ui:
        draw_gameplay_ui_overlay(screen, exit_button_rect, pause_button_rect, font, paused, save_error)
    elif ui_surface is not None and not defer_ui_overlay and not defer_native_ui:
        ui_surface.fill((0, 0, 0, 0))
        draw_gameplay_ui_overlay(ui_surface, exit_button_rect, pause_button_rect, font, paused, save_error)
        composite_gameplay_ui(screen, ui_surface, ui_surface.get_bounding_rect())


def draw_round_transition(screen, round_num, round_font, transition_timer):
    alpha = int((transition_timer / TRANSITION_DURATION) * 255)
    alpha = max(0, min(255, alpha))

    profile = milestone_boss_profile(round_num)
    text_str = (profile["name"] if profile is not None else
                f"BOSS WAVE {round_num}" if round_num % 5 == 0 else f"WAVE {round_num}")
    color = UI_CORAL if round_num % 5 == 0 else UI_CYAN
    text_surf = round_font.render(text_str, True, color)
    panel_width = max(420, text_surf.get_width() + 86)
    fade_surf = pygame.Surface((panel_width, text_surf.get_height() + 82), pygame.SRCALPHA)
    panel = fade_surf.get_rect().inflate(-12, -12)
    draw_neon_panel(fade_surf, panel, color)
    fade_surf.blit(text_surf, text_surf.get_rect(center=panel.center))
    for offset in (-1, 1):
        marker_x = panel.centerx + offset * (text_surf.get_width() // 2 + 24)
        pygame.draw.polygon(fade_surf, UI_GOLD if round_num % 5 == 0 else UI_VIOLET,
                            ((marker_x, panel.centery - 9), (marker_x + offset * 9, panel.centery), (marker_x, panel.centery + 9)))
    fade_surf.set_alpha(alpha)

    text_rect = fade_surf.get_rect(center=(SCREEN_WIDTH // 2, SCREEN_HEIGHT // 2))
    screen.blit(fade_surf, text_rect)
    caption = (f"CHECKPOINT REACHED  |  SECTOR {sector_for_round(round_num):02d}"
               if round_num == sector_start_round(round_num)
               else f"SECTOR {sector_for_round(round_num):02d}  |  ENEMY HP TIER {enemy_health_tier(round_num)}")
    if profile is not None:
        caption = f"WAVE {round_num}  |  {profile['subtitle']}"
    caption_font = pygame.font.SysFont(None, 27)
    caption_surface = caption_font.render(caption, True, UI_GOLD)
    caption_surface.set_alpha(alpha)
    screen.blit(caption_surface, caption_surface.get_rect(center=(SCREEN_WIDTH // 2, text_rect.bottom + 20)))


def show_player_lives_text(player, lives_font, died=False):
    if died:
        text_str = f"PLAYER {player['number']} DIED"
    else:
        text_str = f"PLAYER {player['number']} LIVES LEFT: {player['lives']}"
    color = player["color"]
    return lives_font.render(text_str, True, color), pygame.time.get_ticks()


def draw_lives_text(screen, lives_message):
    if lives_message is None:
        return None

    text_surf, start_time = lives_message
    elapsed = pygame.time.get_ticks() - start_time
    hold_duration = 1200
    fade_duration = 800
    if elapsed >= hold_duration + fade_duration:
        return None

    alpha = 255 if elapsed < hold_duration else int(255 * (1 - (elapsed - hold_duration) / fade_duration))
    text_surf.set_alpha(alpha)
    text_rect = text_surf.get_rect(center=(SCREEN_WIDTH // 2, SCREEN_HEIGHT // 2))
    screen.blit(text_surf, text_rect)
    return lives_message


def safest_warp_position(player, enemies=(), enemy_bullets=()):
    """Choose an in-bounds escape with the most clearance from visible threats."""
    threats = [enemy["rect"] for enemy in enemies if enemy.get("hp", 1) > 0]
    for bullet in enemy_bullets:
        rect = bullet["rect"]
        threats.append(rect)
        if not bullet.get("laser_state"):
            # Include nearby future positions so an empty spot in front of an
            # approaching bolt is less attractive than a genuinely open lane.
            for frames in (12, 24):
                threats.append(rect.move(round(bullet.get("dx", 0) * frames),
                                         round(bullet.get("dy", 0) * frames)))

    def clearance(candidate, threat):
        if candidate.colliderect(threat):
            return -min(candidate.right - threat.left, threat.right - candidate.left,
                        candidate.bottom - threat.top, threat.bottom - candidate.top)
        return math.hypot(max(threat.left - candidate.right, candidate.left - threat.right, 0),
                          max(threat.top - candidate.bottom, candidate.top - threat.bottom, 0))

    left, right = 24, max(24, SCREEN_WIDTH - PLAYER_WIDTH - 24)
    top = max(GAMEPLAY_TOP + 36, round(SCREEN_HEIGHT * 0.56))
    bottom = max(top, SCREEN_HEIGHT - PLAYER_HEIGHT - 30)
    origin = (player["x"], player["y"])
    choices = []
    for row in range(5):
        y = round(top + (bottom - top) * row / 4)
        for column in range(13):
            x = round(left + (right - left) * column / 12)
            rect = pygame.Rect(x, y, PLAYER_WIDTH, PLAYER_HEIGHT).inflate(24, 24)
            space = min((clearance(rect, threat) for threat in threats), default=float("inf"))
            choices.append(((space, math.dist(origin, (x, y))), (float(x), float(y))))
    return max(choices)[1]


def absorb_stored_defense(player, player_rect, particles, enemies=(), enemy_bullets=()):
    """Spend stored protection before a damaging hit can take a life."""
    now = pygame.time.get_ticks()
    if player.get("reflector_charges", 0) > 0:
        player["reflector_charges"] -= 1
        origin_x, origin_y = player_rect.center
        target = min((enemy for enemy in enemies if enemy.get("hp", 1) > 0),
                     key=lambda enemy: math.dist(player_rect.center, enemy["rect"].center),
                     default=None)
        direction_x = target["rect"].centerx - origin_x if target else 0
        direction_y = target["rect"].centery - origin_y if target else -1
        distance = max(1, math.hypot(direction_x, direction_y))
        reflected = {
            "rect": pygame.Rect(origin_x - 3, origin_y - 6, 6, 12),
            "type": "normal", "owner": player["number"], "color": POWERUP_COLORS["reflector"],
            "damage": 1, "pierce_remaining": 0, "hit_enemies": set(),
            "homing": False, "lightning": False, "cryo": False,
            "vx": direction_x / distance * 12, "vy": direction_y / distance * 12,
            "lifetime": 150, "reflected": True, "chain_eligible": False, "support_shot": True,
        }
        pending = player.setdefault("pending_reflections", [])
        if len(pending) < 3:
            pending.append(reflected)
        player["shield_until"] = max(player["shield_until"], now + 120)
        player["powerup_notice"] = f"REFLECTOR {player['reflector_charges']} LEFT"
        player["powerup_notice_until"] = now + 1200
        spawn_pop_particles(origin_x, origin_y, POWERUP_COLORS["reflector"], particles)
        return True
    if not player.get("warp_ready", False):
        return False
    player["warp_ready"] = False
    origin = player_rect.center
    player["x"], player["y"] = safest_warp_position(player, enemies, enemy_bullets)
    player_rect.topleft = (round(player["x"]), round(player["y"]))
    player["move_dx"] = player["move_dy"] = 0
    player["ram_bounce_x"] = player["ram_bounce_y"] = 0
    player["ram_bounce_frames"] = 0
    player["shield_until"] = max(player["shield_until"], now + EMERGENCY_WARP_SHIELD_MS)
    player["powerup_notice"] = "EMERGENCY WARP"
    player["powerup_notice_until"] = now + 1800
    spawn_pop_particles(*origin, POWERUP_COLORS["emergency_warp"], particles)
    spawn_pop_particles(*player_rect.center, POWERUP_COLORS["emergency_warp"], particles)
    reset_player_animation(player)
    return True


def register_player_hit(player, player_rect, particles, lives_font, lives_message,
                        enemies=(), enemy_bullets=()):
    now = pygame.time.get_ticks()
    if (player.get("eliminated", False) or player.get("respawn_until", 0) > now
            or player.get("shield_until", 0) > now
            or player.get("durability_invuln_until", 0) > now):
        return lives_message
    if absorb_stored_defense(player, player_rect, particles, enemies, enemy_bullets):
        return lives_message
    spawn_pop_particles(player_rect.centerx, player_rect.centery, player["color"], particles)
    update_durability([player], now)
    if player.get("durability_damage", 0) < durability_capacity(player) - 1:
        player["durability_damage"] = player.get("durability_damage", 0) + 1
        player["durability_regen_until"] = now + DURABILITY_REGEN_DELAY_MS
        player["durability_invuln_until"] = now + DURABILITY_HIT_INVULN_MS
        player["powerup_notice"] = f"DURABILITY {durability_remaining(player)}/{durability_capacity(player)}"
        player["powerup_notice_until"] = now + 1400
        return lives_message
    reset_durability(player)
    player["momentum_stacks"] = 0  # Losing a ship dumps its captured energy.
    player["shatter_stacks"] = 0
    player["shatter_flash_until"] = 0
    player["pending_nova"] = False
    player["nova_charge_until"] = 0
    if player["lives"] > 0:
        player["lives"] -= 1
        if player["lives"] > 0:
            player["respawn_until"] = now + RESPAWN_DURATION
            return show_player_lives_text(player, lives_font)

    player["eliminated"] = True
    return show_player_lives_text(player, lives_font, died=True)


def death(enemies, enemy_bullets, particles, players, lives_font, lives_message):
    now = pygame.time.get_ticks()
    player_rects = []
    for player in players:
        is_vulnerable = (
            not player["eliminated"]
            and player["respawn_until"] <= now
            and player["shield_until"] <= now
            and player.get("durability_invuln_until", 0) <= now
        )
        player_rects.append(
            pygame.Rect(player["x"], player["y"], PLAYER_WIDTH, PLAYER_HEIGHT)
            if is_vulnerable else None
        )

    for enemy in enemies:
        rect = enemy["rect"]
        for index, player_rect in enumerate(player_rects):
            if player_rect is not None and rect.colliderect(player_rect):
                lives_message = register_player_hit(
                    players[index], player_rect, particles, lives_font, lives_message,
                    enemies, enemy_bullets
                )
                player_rects[index] = None

        invasion_y = enemy["rect"].y
        if enemy["type"] == "diver":
            invasion_y = enemy["dive_origin_y"]
        elif enemy["type"] == "weaver":
            invasion_y = enemy["weave_origin_y"]
        if invasion_y + rect.height >= SCREEN_HEIGHT - ENEMY_HEIGHT:
            return True, lives_message

        if all(player["eliminated"] for player in players):
            return True, lives_message

    for bullet in enemy_bullets[:]:
        if bullet.get("laser_state") == "warning":
            continue
        bullet_rect = bullet["rect"]
        shield_broken_bullet = False
        for player in players:
            if player["eliminated"] or player["respawn_until"] > now or player["shield_until"] <= now:
                continue
            shield_center_x = player["x"] + PLAYER_WIDTH / 2
            shield_center_y = player["y"] + PLAYER_HEIGHT / 2
            closest_x = min(max(shield_center_x, bullet_rect.left), bullet_rect.right)
            closest_y = min(max(shield_center_y, bullet_rect.top), bullet_rect.bottom)
            if math.hypot(closest_x - shield_center_x, closest_y - shield_center_y) <= 26:
                spawn_pop_particles(
                    bullet_rect.centerx,
                    bullet_rect.centery,
                    bullet["color"],
                    particles,
                )
                enemy_bullets.remove(bullet)
                shield_broken_bullet = True
                break
        if shield_broken_bullet:
            continue

        for index, player_rect in enumerate(player_rects):
            if player_rect is not None and bullet_rect.colliderect(player_rect):
                spawn_pop_particles(
                    bullet_rect.centerx,
                    bullet_rect.centery,
                    bullet["color"],
                    particles,
                )
                enemy_bullets.remove(bullet)
                lives_message = register_player_hit(
                    players[index], player_rect, particles, lives_font, lives_message,
                    enemies, enemy_bullets
                )
                player_rects[index] = None
                break

        if all(player["eliminated"] for player in players):
            return True, lives_message

    return all(player["eliminated"] for player in players), lives_message


DEFEAT_CUTSCENE_DURATION = 4600
VICTORY_CUTSCENE_DURATION = 11000


def draw_invasion_stars(screen):
    star_colors = (UI_CYAN, UI_PINK, UI_GOLD, UI_VIOLET, UI_MINT, UI_TEXT)
    for star_index in range(90):
        star_x = (star_index * 197 + 41) % SCREEN_WIDTH
        star_y = (star_index * 307 + 19) % SCREEN_HEIGHT
        brightness = 0.38 + ((star_index * 37) % 80) / 130
        star_size = 2 if star_index % 7 == 0 else 1
        tint = star_colors[star_index % len(star_colors)]
        color = tuple(int(channel * brightness) for channel in tint)
        pygame.draw.rect(
            screen,
            color,
            (star_x, star_y, star_size, star_size),
        )
        if star_index % 23 == 0:
            pygame.draw.line(screen, color, (star_x - 3, star_y), (star_x + 3, star_y))
            pygame.draw.line(screen, color, (star_x, star_y - 3), (star_x, star_y + 3))


def draw_invasion_earth(screen, center, radius, damaged=False):
    center_x, center_y = center
    ocean_color = (16, 29, 65) if damaged else (12, 60, 121)
    land_color = (62, 75, 91) if damaged else (57, 180, 158)
    atmosphere = UI_CORAL if damaged else UI_CYAN
    pygame.draw.circle(screen, (24, 18, 48) if damaged else (10, 30, 58), center, radius + 19)
    pygame.draw.circle(screen, (51, 30, 65) if damaged else (18, 62, 94), center, radius + 11)
    pygame.draw.circle(screen, ocean_color, center, radius)

    continents = (
        ((-0.78, -0.22), (-0.55, -0.52), (-0.28, -0.40), (-0.20, -0.18), (-0.42, -0.02), (-0.33, 0.22), (-0.58, 0.16)),
        ((-0.24, 0.03), (-0.06, 0.12), (-0.12, 0.40), (-0.25, 0.54), (-0.34, 0.25)),
        ((0.03, -0.44), (0.30, -0.48), (0.48, -0.27), (0.34, -0.07), (0.22, 0.06), (0.31, 0.28), (0.18, 0.55), (0.00, 0.33), (0.10, 0.04)),
        ((0.34, -0.43), (0.65, -0.31), (0.80, -0.10), (0.61, 0.10), (0.43, -0.08)),
    )
    for continent in continents:
        points = [
            (int(center_x + offset_x * radius), int(center_y + offset_y * radius))
            for offset_x, offset_y in continent
        ]
        pygame.draw.polygon(screen, land_color, points)

    for band in (-0.46, 0.0, 0.46):
        latitude = pygame.Rect(center_x - radius, int(center_y + band * radius - radius * 0.13), radius * 2, int(radius * 0.26))
        pygame.draw.ellipse(screen, (35, 64, 90) if damaged else (21, 92, 134), latitude, 1)
    pygame.draw.circle(screen, atmosphere, center, radius, 3)
    pygame.draw.arc(screen, UI_GOLD if damaged else (149, 252, 255), (center_x - radius - 5, center_y - radius - 5, 2 * radius + 10, 2 * radius + 10), 0.38, 2.68, 3)

    if damaged:
        for crack_index in range(5):
            crack_x = center_x - radius // 2 + crack_index * radius // 4
            crack_y = center_y - radius // 3 + crack_index * 9
            pygame.draw.line(
                screen,
                UI_CORAL,
                (crack_x, crack_y),
                (crack_x + radius // 12, crack_y + radius // 5),
                3,
            )
        for light_index in range(28):
            light_x = center_x - radius + (light_index * 47) % (radius * 2)
            light_y = center_y - radius // 5 + (light_index * 29) % max(1, radius // 2)
            if math.hypot(light_x - center_x, light_y - center_y) < radius - 8:
                pygame.draw.circle(screen, UI_GOLD, (light_x, light_y), 3)
                pygame.draw.circle(screen, UI_CORAL, (light_x, light_y), 7, 1)


def draw_invasion_ship(screen, center_x, center_y, size, color):
    ship_points = [
        (center_x - size, center_y),
        (center_x - size // 2, center_y - size // 2),
        (center_x + size // 2, center_y - size // 2),
        (center_x + size, center_y),
        (center_x + size // 2, center_y + size // 3),
        (center_x - size // 2, center_y + size // 3),
    ]
    glow_points = [(center_x + int((x - center_x) * 1.17), center_y + int((y - center_y) * 1.17)) for x, y in ship_points]
    pygame.draw.polygon(screen, tuple(int(channel * 0.22) for channel in color), glow_points)
    pygame.draw.polygon(screen, tuple(int(channel * 0.46) for channel in color), ship_points)
    pygame.draw.polygon(screen, color, ship_points, 2)
    pygame.draw.rect(
        screen,
        UI_TEXT,
        (center_x - size // 4, center_y - size // 3, size // 2, max(3, size // 5)),
    )
    pygame.draw.line(
        screen,
        UI_GOLD,
        (center_x - size // 2, center_y + size // 3),
        (center_x + size // 2, center_y + size // 3),
        3,
    )
    for engine_offset in (-size // 2, size // 2):
        pygame.draw.circle(screen, UI_CYAN, (center_x + engine_offset, center_y + size // 3), max(2, size // 8))


@ui_scene
def draw_alien_invasion_cutscene(screen, elapsed_ms, title_font, button_font):
    draw_space_background(screen, "defeat", elapsed_ms)
    draw_invasion_stars(screen)
    progress = min(1, elapsed_ms / DEFEAT_CUTSCENE_DURATION)
    earth_radius = int(SCREEN_HEIGHT * 0.36)
    earth_center = (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 1.04))
    draw_invasion_earth(screen, earth_center, earth_radius)

    ship_positions = (0.28, 0.5, 0.72)
    fleet_colors = (UI_PINK, UI_VIOLET, UI_CORAL)
    for ship_index, horizontal_position in enumerate(ship_positions):
        ship_x = int(SCREEN_WIDTH * horizontal_position + math.sin(elapsed_ms / 430 + ship_index) * SCREEN_WIDTH * 0.012)
        ship_y = int(SCREEN_HEIGHT * (0.19 + progress * 0.09) + math.sin(elapsed_ms / 520 + ship_index * 2) * 8)
        ship_size = max(16, int(SCREEN_HEIGHT * 0.025))
        impact_y = earth_center[1] - earth_radius + int(earth_radius * 0.35)
        if elapsed_ms > 950:
            beam_color = fleet_colors[ship_index]
            pygame.draw.line(screen, tuple(int(channel * 0.36) for channel in beam_color), (ship_x, ship_y + ship_size // 3), (ship_x, impact_y), 11)
            pygame.draw.line(screen, beam_color, (ship_x, ship_y + ship_size // 3), (ship_x, impact_y), 5)
            pygame.draw.line(screen, UI_TEXT, (ship_x, ship_y + ship_size // 3), (ship_x, impact_y), 1)
            impact_radius = 5 + int((elapsed_ms // 90 + ship_index * 3) % 9)
            pygame.draw.circle(screen, UI_GOLD, (ship_x, impact_y), impact_radius, 2)
        draw_invasion_ship(screen, ship_x, ship_y, ship_size, fleet_colors[ship_index])

    pygame.draw.rect(screen, BLACK, (0, 0, SCREEN_WIDTH, 18))
    pygame.draw.rect(screen, BLACK, (0, SCREEN_HEIGHT - 18, SCREEN_WIDTH, 18))
    draw_neon_title(screen, "ALIEN FLEET INBOUND", title_font, (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.075)), UI_PINK)
    caption = "EARTH'S DEFENSES ARE FAILING" if progress > 0.42 else "PLANETARY SHIELDS BREACHED"
    caption_surface = button_font.render(caption, True, UI_CORAL if progress > 0.42 else UI_GOLD)
    screen.blit(caption_surface, caption_surface.get_rect(center=(SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.89))))


@ui_layout
def end_screen_card_layout(count, completion=False):
    if not compact_menu_layout():
        gap = 14
        width = min(280, (SCREEN_WIDTH - 64 - gap * (max(1, count) - 1)) // max(1, count))
        start = (SCREEN_WIDTH - width * count - gap * max(0, count - 1)) // 2
        return [pygame.Rect(start + index * (width + gap), round(SCREEN_HEIGHT * (.38 if completion else .52)),
                            width, 190 if completion else 142) for index in range(count)]
    columns = min(2, max(1, count))
    rows = math.ceil(count / columns)
    gap, margin = 12, 20
    width = min(370, (SCREEN_WIDTH - 2 * margin - gap * (columns - 1)) // columns)
    y = 120 if SCREEN_HEIGHT < 500 else round(SCREEN_HEIGHT * .38)
    available = max(52, SCREEN_HEIGHT - 114 - y)
    height = min(190 if completion else 142, (available - gap * (rows - 1)) // rows)
    start = (SCREEN_WIDTH - columns * width - gap * (columns - 1)) // 2
    return [pygame.Rect(start + index % columns * (width + gap), y + index // columns * (height + gap),
                        width, height) for index in range(count)]


def draw_compact_end_screen(screen, title_font, button_font, font, players,
                            play_again_rect, other_rect=None, round_num=1,
                            checkpoint_wave=1, retries_remaining=MAX_RUN_RETRIES,
                            save_error=None, completion=False):
    draw_space_background(screen, "victory" if completion else "defeat")
    draw_invasion_stars(screen)
    low = SCREEN_HEIGHT < 500
    draw_fitted_text(screen, "CAMPAIGN COMPLETE" if completion else "EARTH HAS FALLEN",
                     title_font, UI_MINT if completion else UI_CORAL,
                     pygame.Rect(16, 10 if low else 30,
                                 SCREEN_WIDTH - (144 if low else 32), 48 if low else 72))
    score = sum(player["score"] for player in players)
    summary = f"{MAX_CAMPAIGN_ROUND} WAVES CLEARED  |  TEAM {score:08d}" if completion else f"WAVE {round_num}  |  TEAM {score:08d}"
    draw_fitted_text(screen, summary, button_font, UI_GOLD if completion else UI_TEXT,
                     pygame.Rect(20, 77 if low else round(SCREEN_HEIGHT * .26), SCREEN_WIDTH - 40, 30))
    rankings = {}
    previous = None
    rank = 0
    for index, player in enumerate(sorted(players, key=lambda p: p["score"], reverse=True), start=1):
        if player["score"] != previous:
            rank = index
            previous = player["score"]
        rankings[player["number"]] = rank
    small_font = pygame.font.SysFont(None, 18 if low else 22)
    for player, card in zip(players, end_screen_card_layout(len(players), completion)):
        draw_neon_panel(screen, card, player["color"], radius=8)
        lines = [f"P{player['number']}  ·  RANK #{rankings[player['number']]}",
                 f"SCORE {player['score']:08d}",
                 f"LIVES {player['lives']}  ·  DMG +{player.get('damage_bonus', 0)}" if completion else
                 f"{'OUT' if player['eliminated'] else 'SURVIVED'}  ·  DMG +{player.get('damage_bonus', 0)}"]
        if card.height > 110:
            lines.insert(2, f"ENEMIES DEFEATED {player['kills']}")
        row = (card.height - 10) // len(lines)
        for index, text in enumerate(lines):
            draw_fitted_text(screen, text, small_font, player["color"] if index == 0 else UI_TEXT,
                             pygame.Rect(card.x + 9, card.y + 5 + index * row, card.width - 18, row - 1), "left")
    if other_rect is not None:
        label = "INFINITE MODE" if completion else (f"RETRY W{checkpoint_wave} ({retries_remaining} LEFT)"
                                                    if retries_remaining else "NO RETRIES LEFT")
        draw_neon_button(screen, other_rect, label, font, UI_GOLD,
                         enabled=completion or retries_remaining > 0)
    draw_neon_button(screen, play_again_rect, "NEW RUN", font, UI_CYAN)
    if save_error:
        draw_fitted_text(screen, save_error, small_font, UI_CORAL,
                         pygame.Rect(16, SCREEN_HEIGHT - 116, SCREEN_WIDTH - 32, 16))


@ui_scene
def draw_death_screen(screen, death_title_font, button_font, player_choice_font,
                      play_again_rect, players, round_num, checkpoint_rect=None, checkpoint_wave=1,
                      retries_remaining=MAX_RUN_RETRIES, save_error=None):
    if compact_menu_layout():
        draw_compact_end_screen(screen, death_title_font, button_font, player_choice_font,
                                players, play_again_rect, checkpoint_rect, round_num,
                                checkpoint_wave, retries_remaining, save_error)
        return
    draw_space_background(screen, "defeat")
    draw_invasion_stars(screen)
    earth_radius = int(SCREEN_HEIGHT * 0.39)
    draw_invasion_earth(
        screen,
        (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 1.02)),
        earth_radius,
        damaged=True,
    )

    draw_neon_title(screen, "EARTH HAS FALLEN", death_title_font, (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.17)), UI_CORAL)
    subtitle = button_font.render("DEFENSE GRID OVERRUN", True, UI_PINK)
    screen.blit(subtitle, subtitle.get_rect(center=(SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.29))))

    team_score = sum(player["score"] for player in players)
    summary = button_font.render(f"WAVE {round_num}    |    TEAM SCORE {team_score:08d}", True, UI_TEXT)
    summary_panel = pygame.Rect(0, 0, summary.get_width() + 54, 58)
    summary_panel.center = (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.41))
    draw_neon_panel(screen, summary_panel, UI_VIOLET)
    screen.blit(summary, summary.get_rect(center=(SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.41))))

    card_gap = 14
    card_count = max(1, len(players))
    card_width = min(280, (SCREEN_WIDTH - 64 - card_gap * (card_count - 1)) // card_count)
    card_height = 142
    cards_width = card_width * len(players) + card_gap * max(0, len(players) - 1)
    card_start_x = (SCREEN_WIDTH - cards_width) // 2
    card_y = int(SCREEN_HEIGHT * 0.52)
    ranked_players = sorted(players, key=lambda player: player["score"], reverse=True)
    player_ranks = {}
    previous_score = None
    current_rank = 0
    for position, ranked_player in enumerate(ranked_players, start=1):
        if ranked_player["score"] != previous_score:
            current_rank = position
            previous_score = ranked_player["score"]
        player_ranks[ranked_player["number"]] = current_rank

    for player_index, player in enumerate(players):
        card = pygame.Rect(card_start_x + player_index * (card_width + card_gap), card_y, card_width, card_height)
        draw_neon_panel(screen, card, player["color"])
        pygame.draw.rect(screen, player["color"], (card.x + 12, card.y + 34, 36, 3), border_radius=1)
        player_title = player_choice_font.render(f"PLAYER {player['number']}", True, player["color"])
        screen.blit(player_title, (card.x + 12, card.y + 12))
        rank_text = player_choice_font.render(f"RANK #{player_ranks[player['number']]}", True, UI_GOLD)
        screen.blit(rank_text, rank_text.get_rect(midright=(card.right - 12, card.y + 24)))
        score_line = player_choice_font.render(f"SCORE {player['score']:08d}", True, UI_TEXT)
        screen.blit(score_line, (card.x + 12, card.y + 46))
        damage_line = player_choice_font.render(f"DAMAGE UP +{player.get('damage_bonus', 0)}", True, UI_VIOLET)
        screen.blit(damage_line, (card.x + 12, card.y + 78))
        state_line = "ELIMINATED" if player["eliminated"] else "SURVIVED"
        state_surface = player_choice_font.render(state_line, True, UI_CORAL if player["eliminated"] else UI_MINT)
        screen.blit(state_surface, (card.x + 12, card.y + 110))

    if checkpoint_rect is not None:
        checkpoint_label = (f"RETRY W{checkpoint_wave}  ({retries_remaining} LEFT)"
                            if retries_remaining else "NO RETRIES LEFT")
        draw_neon_button(screen, checkpoint_rect, checkpoint_label,
                         button_font, UI_GOLD, enabled=retries_remaining > 0)
    if save_error:
        status = player_choice_font.render(save_error, True, UI_CORAL)
        if status.get_width() > SCREEN_WIDTH - 40:
            status = pygame.transform.smoothscale(status, (SCREEN_WIDTH - 40, status.get_height()))
        screen.blit(status, status.get_rect(center=(SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.77))))
    draw_neon_button(screen, play_again_rect, "NEW RUN", button_font, UI_CYAN)


@ui_scene
def draw_victory_cutscene(screen, elapsed_ms, title_font, button_font, players):
    draw_space_background(screen, "victory", elapsed_ms)
    draw_invasion_stars(screen)
    draw_invasion_earth(
        screen,
        (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 1.08)),
        int(SCREEN_HEIGHT * 0.31),
    )

    for index, player in enumerate(players):
        formation_position = (index + 1) / (len(players) + 1)
        ship_x = int(
            SCREEN_WIDTH * formation_position
            + math.sin(elapsed_ms / 650 + index) * 18
        )
        ship_y = int(SCREEN_HEIGHT * 0.59 + math.sin(elapsed_ms / 520 + index * 2) * 9)
        draw_invasion_ship(screen, ship_x, ship_y, 24, player["color"])
        pygame.draw.line(
            screen,
            player["color"],
            (ship_x, ship_y + 16),
            (ship_x, int(SCREEN_HEIGHT * 0.77)),
            2,
        )

    if elapsed_ms < 4000:
        draw_neon_title(screen, "EARTH SAVED", title_font, (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.12)), UI_MINT)
        draw_fitted_text(screen, f"WAVE {MAX_CAMPAIGN_ROUND} CLEARED / ALL PILOTS REWARDED",
                         button_font, UI_GOLD,
                         pygame.Rect(20, int(SCREEN_HEIGHT * 0.22) - 20, SCREEN_WIDTH - 40, 40))

    credits = (
        ("CAMPAIGN COMPLETE", UI_GOLD),
        ("ALL CAMPAIGN WAVES CLEARED", UI_TEXT),
        ("CREATED BY", UI_CYAN),
        ("ASA GARVER", UI_TEXT),
        ("CO-DEVELOPER", UI_PINK),
        ("DAELYN REGO", UI_TEXT),
        ("THANK YOU FOR DEFENDING EARTH", UI_MINT),
    )
    scroll_offset = elapsed_ms * 0.12
    for index, (credit_line, color) in enumerate(credits):
        y = SCREEN_HEIGHT + 50 + index * 68 - scroll_offset
        if -40 <= y <= SCREEN_HEIGHT + 40:
            credit = button_font.render(credit_line, True, color)
            screen.blit(credit, credit.get_rect(center=(SCREEN_WIDTH // 2, int(y))))


@ui_scene
def draw_completion_screen(screen, title_font, button_font, player_choice_font, play_again_rect, infinite_mode_rect, players):
    if compact_menu_layout():
        draw_compact_end_screen(screen, title_font, button_font, player_choice_font, players,
                                play_again_rect, infinite_mode_rect, completion=True)
        return
    draw_space_background(screen, "victory")
    draw_invasion_stars(screen)
    draw_invasion_earth(
        screen,
        (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 1.08)),
        int(SCREEN_HEIGHT * 0.34),
    )

    draw_neon_title(screen, "CAMPAIGN COMPLETE", title_font, (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.14)), UI_MINT)
    team_score = sum(player["score"] for player in players)
    summary = button_font.render(
        f"{MAX_CAMPAIGN_ROUND} WAVES CLEARED    |    TEAM SCORE {team_score:08d}",
        True,
        UI_GOLD,
    )
    summary_panel = pygame.Rect(0, 0, summary.get_width() + 50, 58)
    summary_panel.center = (SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.27))
    draw_neon_panel(screen, summary_panel, UI_GOLD)
    screen.blit(summary, summary.get_rect(center=(SCREEN_WIDTH // 2, int(SCREEN_HEIGHT * 0.27))))

    ranked_players = sorted(players, key=lambda player: player["score"], reverse=True)
    player_ranks = {}
    previous_score = None
    current_rank = 0
    for position, player in enumerate(ranked_players, start=1):
        if player["score"] != previous_score:
            current_rank = position
            previous_score = player["score"]
        player_ranks[player["number"]] = current_rank

    card_gap = 14
    card_width = min(280, (SCREEN_WIDTH - 64 - card_gap * (len(players) - 1)) // len(players))
    card_height = 190
    cards_width = card_width * len(players) + card_gap * (len(players) - 1)
    card_start_x = (SCREEN_WIDTH - cards_width) // 2
    card_y = int(SCREEN_HEIGHT * 0.38)
    for index, player in enumerate(players):
        card = pygame.Rect(
            card_start_x + index * (card_width + card_gap),
            card_y,
            card_width,
            card_height,
        )
        draw_neon_panel(screen, card, player["color"])
        pygame.draw.rect(screen, player["color"], (card.x + 12, card.y + 37, 50, 3), border_radius=1)

        player_title = player_choice_font.render(
            f"PLAYER {player['number']}  RANK #{player_ranks[player['number']]}",
            True,
            player["color"],
        )
        screen.blit(player_title, (card.x + 12, card.y + 14))
        stat_lines = (
            (f"SCORE {player['score']:08d}", UI_TEXT),
            (f"ENEMIES DESTROYED {player['kills']}", UI_CYAN),
            (f"LIVES REMAINING {player['lives']}", UI_MINT),
            (f"DAMAGE UP +{player.get('damage_bonus', 0)}", UI_GOLD),
        )
        for line_index, (text, color) in enumerate(stat_lines):
            stat = player_choice_font.render(text, True, color)
            screen.blit(stat, (card.x + 12, card.y + 50 + line_index * 32))

    draw_neon_button(screen, infinite_mode_rect, "INFINITE MODE", button_font, UI_GOLD)
    draw_neon_button(screen, play_again_rect, "PLAY AGAIN", button_font, UI_CYAN)


def reset_game_state(round_num=1, powerups=None, infinite_mode=False):
    enemies = create_enemies(round_num, infinite_mode)
    bunkers = create_bunkers()
    enemy_bullets = []
    player_bullets = []
    particles = []
    powerups = [] if powerups is None else powerups
    enemy_dx = 1
    return enemies, bunkers, enemy_bullets, player_bullets, particles, powerups, enemy_dx


def grant_boss_clear_life(players):
    """Give EVERY player a life after a boss wave, up to five.

    Eliminated teammates return with one life. This is a team-wide reward,
    not a single life shared across the team. No damage milestones are added.
    """
    now = pygame.time.get_ticks()
    for player in players:
        gained_life = player["eliminated"] or player["lives"] < player_life_capacity(player)
        if player["eliminated"]:
            player["eliminated"] = False
            player["lives"] = 1
            reset_durability(player)
            player["respawn_until"] = 0
            player["shield_until"] = now + SPAWN_SHIELD_DURATION
            player["cooldown"] = 0
            reset_player_animation(player)
        else:
            player["lives"] = min(player_life_capacity(player), player["lives"] + 1)
        guardian_notice = (player.get("powerup_notice", "").startswith("GUARDIAN REWARD:")
                           and player.get("powerup_notice_until", 0) > now)
        if guardian_notice:
            player["powerup_notice"] += " / +1 LIFE" if gained_life else " / MAX LIVES"
            player["powerup_notice_until"] = max(player["powerup_notice_until"], now + 2300)
        else:
            player["powerup_notice"] = "BOSS CLEAR +1 LIFE" if gained_life else "BOSS CLEAR - MAX LIVES"
            player["powerup_notice_until"] = now + 2300


def revive_eliminated_teammates(players):
    now = pygame.time.get_ticks()
    for player in players:
        if player["eliminated"]:
            player["eliminated"] = False
            player["lives"] = 1
            reset_durability(player)
            player["respawn_until"] = 0
            player["shield_until"] = now + SPAWN_SHIELD_DURATION
            player["cooldown"] = 0
            reset_player_animation(player)


def save_sector_checkpoint(players, round_num):
    """Snapshot progress on entry; retry never duplicates later-wave pickups."""
    return {
        "wave": sector_start_round(round_num),
        "pilots": [{"score": p["score"], "kills": p["kills"],
                    "damage_bonus": p["damage_bonus"],
                    "durability_bonus": p.get("durability_bonus", 0),
                    "warp_ready": p.get("warp_ready", False),
                    "reflector_charges": p.get("reflector_charges", 0),
                    "supply_kills_left": p.get("supply_kills_left", 0),
                    "pending_missiles": p.get("pending_missiles", False)} for p in players],
    }


def restore_sector_checkpoint(checkpoint, player_sprites):
    """Respawn with three lives and fully repaired checkpoint durability."""
    pilots = checkpoint["pilots"]
    players = create_player_states(len(pilots), player_sprites)
    now = pygame.time.get_ticks()
    for pilot, saved in zip(players, pilots):
        for field in ("score", "kills", "damage_bonus"):
            pilot[field] = saved[field]
        for field, default in SAVED_OPTIONAL_PILOT_DEFAULTS.items():
            pilot[field] = saved.get(field, default)
        pilot["durability_bonus"] = saved.get("durability_bonus", saved.get("health_bonus", 0))
        pilot["lives"] = STARTING_LIVES
        reset_durability(pilot)
        pilot["shield_until"] = now + SPAWN_SHIELD_DURATION
        pilot["powerup_notice"] = f"SECTOR {sector_for_round(checkpoint['wave'])} CHECKPOINT"
        pilot["powerup_notice_until"] = now + 2400
    return players


# The disk save stores a *wave-start* snapshot, not every live projectile.
# This avoids fragile serialization of Pygame surfaces/Rects and allows a
# reliable restart even if the window is closed mid-fight. Saves contain only
# JSON primitives (no pickle or executable data) and are atomically replaced.
SAVED_OPTIONAL_PILOT_DEFAULTS = {"durability_bonus": 0, "durability_damage": 0,
                                 "warp_ready": False, "reflector_charges": 0,
                                 "supply_kills_left": 0, "pending_missiles": False}
SAVED_PILOT_FIELDS = ("score", "kills", "lives", "damage_bonus", "eliminated",
                      *SAVED_OPTIONAL_PILOT_DEFAULTS)
SAVED_OPTIONAL_TIMER_FIELDS = frozenset(("cryo_until", "orbit_until", "gravity_until", "chain_reaction_until", "nova_charge_until",
                                         "durability_regen_until", "durability_invuln_until"))
SAVED_TIMER_FIELDS = tuple(dict.fromkeys((
    *POWERUP_TIMER_KEYS.values(), "shield_until", "respawn_until", "nova_charge_until",
    "durability_regen_until", "durability_invuln_until",
)))


def build_saved_run(round_num, players, checkpoint, infinite_mode=False, now=None, *,
                    retries_remaining=MAX_RUN_RETRIES, run_defeated=False):
    now = pygame.time.get_ticks() if now is None else now
    pilots = []
    for player in players:
        pilot = {key: player.get(key, SAVED_OPTIONAL_PILOT_DEFAULTS[key])
                 if key in SAVED_OPTIONAL_PILOT_DEFAULTS else player[key]
                 for key in SAVED_PILOT_FIELDS}
        pilot["remaining_ms"] = {
            key: max(0, int(player.get(key, 0) - now)) for key in SAVED_TIMER_FIELDS
        }
        # Only a live charge is portable. A due pulse retains one millisecond
        # so Continue resolves it once rather than dropping it or restarting it.
        pilot["remaining_ms"]["nova_charge_until"] = (
            max(1, min(NOVA_COUNTDOWN_MS, int(player.get("nova_charge_until", 0) - now)))
            if player.get("pending_nova", False) and not player["eliminated"] else 0
        )
        pilot["remaining_ms"]["durability_regen_until"] = (
            max(1, min(DURABILITY_REGEN_DELAY_MS,
                       int(player.get("durability_regen_until", 0) - now)))
            if player.get("durability_damage", 0) else 0
        )
        pilot["momentum_stacks"] = (
            int(player["momentum_stacks"])
            if player["bullet_time_until"] > now else 0
        )
        pilot["shatter_stacks"] = (int(player.get("shatter_stacks", 0))
                                    if player.get("cryo_until", 0) > now else 0)
        pilots.append(pilot)
    return {
        "version": SAVE_FORMAT_VERSION,
        "saved_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "wave": int(round_num),
        "player_count": len(players),
        "infinite_mode": bool(infinite_mode),
        "retries_remaining": retries_remaining,
        "run_defeated": run_defeated,
        "pilots": pilots,
        "checkpoint": {
            "wave": int(checkpoint["wave"]),
            "pilots": [migrate_legacy_health_state(dict(pilot)) for pilot in checkpoint["pilots"]],
        },
    }


def write_saved_run(snapshot, filename=SAVE_FILE):
    """Save atomically; on failure keep the previous valid save untouched."""
    from tempfile import NamedTemporaryFile
    temporary = None
    try:
        filename = Path(filename)
        filename.parent.mkdir(parents=True, exist_ok=True)
        # Unique sibling files keep an export from clobbering an unrelated
        # filename such as run.tmp, and allow atomic replacement on Windows.
        with NamedTemporaryFile(mode="w", encoding="utf-8", dir=filename.parent,
                                prefix=f".{filename.name}.", suffix=".tmp", delete=False) as handle:
            temporary = Path(handle.name)
            json.dump(snapshot, handle, separators=(",", ":"), allow_nan=False)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, filename)
        return True
    except (OSError, TypeError, ValueError, RecursionError):
        try:
            if temporary is not None:
                temporary.unlink(missing_ok=True)
        except OSError:
            pass
        return False


def save_slot_path(slot):
    """Each of the three menu slots has its own independent autosave file."""
    if type(slot) is not int or not 1 <= slot <= SAVE_SLOT_COUNT:
        raise ValueError(f"Save slot must be an integer from 1 to {SAVE_SLOT_COUNT}")
    return SAVE_FILE.parent / f"save_slot_{slot}.json"


def save_slot_occupied(slot):
    """Treat inaccessible slots as occupied so the menu never erases them."""
    try:
        return save_slot_path(slot).exists()
    except OSError:
        return True


def list_saved_runs():
    """Read slots without creating, deleting, or repairing any file."""
    return [load_saved_run(save_slot_path(slot))
            for slot in range(1, SAVE_SLOT_COUNT + 1)]


def migrate_legacy_save():
    """Copy a valid old single-slot run once, without replacing any slot.

    The original save is retained. A small import marker prevents the same
    legacy run from reappearing after its imported slot is later replaced.
    Existing unreadable/corrupt slots are occupied, never silently erased.
    Return the newly filled slot, or None if nothing was imported.
    """
    legacy = load_saved_run(SAVE_FILE)
    if legacy is None:
        return None
    marker_path = SAVE_FILE.parent / ".legacy_save_imported.json"
    try:
        fingerprint = hashlib.sha256(SAVE_FILE.read_bytes()).hexdigest()
        try:
            marker = (json.loads(marker_path.read_text(encoding="utf-8"))
                      if marker_path.exists() and marker_path.stat().st_size <= 4096 else None)
        except (OSError, ValueError, RecursionError):
            marker = None
        if isinstance(marker, dict) and marker.get("source_sha256") == fingerprint:
            return None
        for slot, saved in enumerate(list_saved_runs(), start=1):
            if saved is not None and saved.get("legacy_migration_id") == fingerprint:
                write_saved_run({"source_sha256": fingerprint, "slot": slot}, marker_path)
                return None
        for slot in range(1, SAVE_SLOT_COUNT + 1):
            filename = save_slot_path(slot)
            if filename.exists():
                continue
            imported = dict(legacy, slot=slot, legacy_migration_id=fingerprint)
            if "saved_at" not in imported:
                imported["saved_at"] = datetime.fromtimestamp(
                    SAVE_FILE.stat().st_mtime, timezone.utc).isoformat(timespec="seconds")
            if not write_saved_run(imported, filename):
                return None
            write_saved_run({"source_sha256": fingerprint, "slot": slot}, marker_path)
            return slot
    except (OSError, ValueError, TypeError, RecursionError):
        return None
    return None


def autosave_run(round_num, players, checkpoint, infinite_mode=False, previous_save=None, slot=None, *,
                 retries_remaining=MAX_RUN_RETRIES, run_defeated=False):
    """Keep the last good Continue snapshot and report a failed disk write."""
    snapshot = build_saved_run(round_num, players, checkpoint, infinite_mode,
                               retries_remaining=retries_remaining, run_defeated=run_defeated)
    if slot is None:
        success = write_saved_run(snapshot)
    else:
        filename = save_slot_path(slot)
        snapshot["slot"] = slot
        # A failed write must never return a Continue snapshot from a different
        # slot, even if the caller has just switched its selected slot.
        if previous_save is None or previous_save.get("slot") != slot:
            previous_save = load_saved_run(filename)
        success = write_saved_run(snapshot, filename)
    if success:
        return snapshot, None
    status = "last saved wave kept" if previous_save is not None else "no saved run"
    return previous_save, f"AUTOSAVE FAILED - {status}. Check disk space/permissions."


def prepare_checkpoint_retry(checkpoint, player_sprites, infinite_mode, previous_save,
                              slot, retries_remaining):
    """Persist the spent retry before starting it; failed writes keep defeat open."""
    if retries_remaining <= 0:
        return None, previous_save, "NO RETRIES LEFT - start a new run."
    players = restore_sector_checkpoint(checkpoint, player_sprites)
    snapshot, error = autosave_run(
        checkpoint["wave"], players, checkpoint, infinite_mode, previous_save, slot=slot,
        retries_remaining=retries_remaining - 1,
    )
    return (None if error else players), snapshot, error


def load_saved_run(filename=SAVE_FILE):
    """Ignore invalid/corrupted/unsupported saves rather than crashing startup."""
    try:
        if not filename.exists() or filename.stat().st_size > 100_000:
            return None
        data = json.loads(filename.read_text(encoding="utf-8"))
        if (not isinstance(data, dict) or type(data.get("version")) is not int
                or data["version"] != SAVE_FORMAT_VERSION):
            return None
        if "slot" in data and (type(data["slot"]) is not int
                               or not 1 <= data["slot"] <= SAVE_SLOT_COUNT):
            return None
        if (type(data.get("retries_remaining", MAX_RUN_RETRIES)) is not int
                or not 0 <= data.get("retries_remaining", MAX_RUN_RETRIES) <= MAX_RUN_RETRIES
                or type(data.get("run_defeated", False)) is not bool):
            return None
        if "saved_at" in data:
            if not isinstance(data["saved_at"], str):
                return None
            saved_at = datetime.fromisoformat(data["saved_at"])
            if saved_at.tzinfo is None:
                return None
        wave = data["wave"]
        count = data["player_count"]
        cp = data["checkpoint"]
        if (type(wave) is not int or not 1 <= wave <= 100_000
                or type(count) is not int or not 1 <= count <= 4
                or not isinstance(data["infinite_mode"], bool)
                or (wave > MAX_CAMPAIGN_ROUND and not data["infinite_mode"])):
            return None
        if (not isinstance(cp, dict) or type(cp.get("wave")) is not int
                or cp["wave"] != sector_start_round(wave)):
            return None
        if (not isinstance(data.get("pilots"), list) or len(data["pilots"]) != count
                or not isinstance(cp.get("pilots"), list) or len(cp["pilots"]) != count):
            return None
        for pilot in data["pilots"]:
            if not isinstance(pilot, dict) or not isinstance(pilot.get("remaining_ms"), dict):
                return None
            if any(type(pilot.get(k)) is not int for k in ("score", "kills", "lives", "damage_bonus", "momentum_stacks")):
                return None
            if (type(pilot.get("health_bonus", 0)) is not int
                    or not 0 <= pilot.get("health_bonus", 0) <= MAX_HEALTH_BONUS):
                return None
            durability_bonus = pilot.get("durability_bonus", pilot.get("health_bonus", 0))
            if (type(durability_bonus) is not int
                    or not 0 <= durability_bonus <= MAX_DURABILITY_BONUS
                    or type(pilot.get("durability_damage", 0)) is not int
                    or not 0 <= pilot.get("durability_damage", 0) <= durability_bonus):
                return None
            legacy_capacity = (BASE_MAX_LIVES + pilot.get("health_bonus", 0)
                               if "durability_bonus" not in pilot else BASE_MAX_LIVES)
            if not (pilot["score"] >= 0 and pilot["kills"] >= 0
                    and 0 <= pilot["lives"] <= legacy_capacity
                    and 0 <= pilot["damage_bonus"] <= MAX_DAMAGE_BONUS
                    and 0 <= pilot["momentum_stacks"] <= BULLET_TIME_MAX_STACKS
                    and isinstance(pilot.get("eliminated"), bool)):
                return None
            if pilot["eliminated"] != (pilot["lives"] == 0):
                return None
            if (type(pilot.get("warp_ready", False)) is not bool
                    or type(pilot.get("pending_missiles", False)) is not bool
                    or type(pilot.get("reflector_charges", 0)) is not int
                    or not 0 <= pilot.get("reflector_charges", 0) <= 3
                    or type(pilot.get("supply_kills_left", 0)) is not int
                    or not 0 <= pilot.get("supply_kills_left", 0) <= 8):
                return None
            if (type(pilot.get("shatter_stacks", 0)) is not int
                    or not 0 <= pilot.get("shatter_stacks", 0) <= SHATTER_MAX_STACKS):
                return None
            timer_keys = set(pilot["remaining_ms"])
            if (not timer_keys <= set(SAVED_TIMER_FIELDS)
                    or not set(SAVED_TIMER_FIELDS) - SAVED_OPTIONAL_TIMER_FIELDS <= timer_keys):
                return None
            if any(type(pilot["remaining_ms"].get(k, 0)) is not int or
                   not 0 <= pilot["remaining_ms"].get(k, 0) <= 180_000 for k in SAVED_TIMER_FIELDS):
                return None
            if pilot["remaining_ms"].get("nova_charge_until", 0) > NOVA_COUNTDOWN_MS:
                return None
        for pilot in cp["pilots"]:
            if (not isinstance(pilot, dict) or
                any(type(pilot.get(k)) is not int for k in ("score", "kills", "damage_bonus")) or
                pilot["score"] < 0 or pilot["kills"] < 0 or
                not 0 <= pilot["damage_bonus"] <= MAX_DAMAGE_BONUS):
                return None
            if (type(pilot.get("health_bonus", 0)) is not int
                    or not 0 <= pilot.get("health_bonus", 0) <= MAX_HEALTH_BONUS):
                return None
            durability_bonus = pilot.get("durability_bonus", pilot.get("health_bonus", 0))
            if type(durability_bonus) is not int or not 0 <= durability_bonus <= MAX_DURABILITY_BONUS:
                return None
            if (type(pilot.get("warp_ready", False)) is not bool
                    or type(pilot.get("pending_missiles", False)) is not bool
                    or type(pilot.get("reflector_charges", 0)) is not int
                    or not 0 <= pilot.get("reflector_charges", 0) <= 3
                    or type(pilot.get("supply_kills_left", 0)) is not int
                    or not 0 <= pilot.get("supply_kills_left", 0) <= 8):
                return None
        for pilot in data["pilots"]:
            migrate_legacy_health_state(pilot)
        for pilot in cp["pilots"]:
            migrate_legacy_health_state(pilot)
        return data
    except (OSError, ValueError, KeyError, TypeError, RecursionError):
        return None


def clear_saved_run(filename=SAVE_FILE):
    try:
        filename.unlink(missing_ok=True)
        return True
    except OSError:
        return False


def save_transfer_path(value):
    """Accept a user-entered filename without treating an empty field as cwd."""
    text = str(value).strip().strip('"')
    if not text or "\x00" in text:
        raise ValueError("Choose a JSON filename first.")
    path = Path(text).expanduser()
    if not path.suffix and not path.exists():
        path = path.with_suffix(".json")
    return path


def export_saved_slot(slot, destination, overwrite=False):
    """Export validated JSON, never accidentally overwrite another managed slot."""
    snapshot = load_saved_run(save_slot_path(slot))
    if snapshot is None:
        return False, "EXPORT FAILED - this slot has no readable save."
    try:
        destination = save_transfer_path(destination)
        managed = [SAVE_FILE, *(save_slot_path(index) for index in range(1, SAVE_SLOT_COUNT + 1))]
        if any(destination.resolve() == filename.resolve() for filename in managed):
            return False, "Choose an export path outside the game's managed save files."
        if destination.exists() and not overwrite:
            return False, "That file already exists. Confirm overwrite before exporting."
        exported = dict(snapshot)
        exported.pop("slot", None)
        exported.pop("legacy_migration_id", None)
        if not write_saved_run(exported, destination):
            return False, "EXPORT FAILED - check the folder and available disk space."
        return True, f"EXPORTED SLOT {slot} - {destination.name}"
    except (OSError, ValueError, TypeError, RuntimeError):
        return False, "EXPORT FAILED - choose a writable JSON filename."


def import_saved_slot(slot, source, overwrite=False):
    """Validate before replacing just one slot, leaving bad imports untouched."""
    destination = save_slot_path(slot)
    try:
        source = save_transfer_path(source)
        snapshot = load_saved_run(source)
        if snapshot is None:
            return None, "IMPORT FAILED - unreadable or unsupported save file."
        if save_slot_occupied(slot) and not overwrite:
            return None, "This slot is occupied. Confirm replacement before importing."
        imported = dict(snapshot, slot=slot)
        imported.pop("legacy_migration_id", None)
        if not write_saved_run(imported, destination):
            return None, "IMPORT FAILED - the previous slot was kept. Check folder permissions."
        return imported, f"IMPORTED INTO SLOT {slot} - CONTINUE to play"
    except (OSError, ValueError, TypeError, RuntimeError):
        return None, "IMPORT FAILED - the previous slot was kept."


def delete_saved_slot(slot):
    """Delete only the selected local slot after the UI obtains confirmation."""
    if clear_saved_run(save_slot_path(slot)):
        return True, f"DELETED SLOT {slot} - other slots and exports are unchanged"
    return False, "DELETE FAILED - the save file was kept. Check folder permissions."


def restore_saved_run(snapshot, player_sprites):
    """Continue with saved pilots/buffs at the start of the recorded wave."""
    players = create_player_states(snapshot["player_count"], player_sprites)
    now = pygame.time.get_ticks()
    for player, pilot in zip(players, snapshot["pilots"]):
        for field in SAVED_PILOT_FIELDS:
            player[field] = pilot.get(field, SAVED_OPTIONAL_PILOT_DEFAULTS[field]) if field in SAVED_OPTIONAL_PILOT_DEFAULTS else pilot[field]
        player["durability_bonus"] = pilot.get("durability_bonus", pilot.get("health_bonus", 0))
        player["lives"] = min(BASE_MAX_LIVES, player["lives"])
        for field in SAVED_TIMER_FIELDS:
            remaining = pilot["remaining_ms"].get(field, 0)
            player[field] = now + remaining if remaining else 0
        player["pending_nova"] = bool(pilot["remaining_ms"].get("nova_charge_until", 0))
        player["momentum_stacks"] = (pilot["momentum_stacks"]
                                      if pilot["remaining_ms"]["bullet_time_until"] else 0)
        player["shatter_stacks"] = (pilot.get("shatter_stacks", 0)
                                     if pilot["remaining_ms"].get("cryo_until", 0) else 0)
        player["powerup_notice"] = "RUN RESTORED"
        player["powerup_notice_until"] = now + 2400
    return (snapshot["wave"], players, snapshot["checkpoint"], snapshot["infinite_mode"])


def main():
    global SCREEN_WIDTH, SCREEN_HEIGHT, _UI_FRAME, _UI_LAYOUT_SIZE, _UI_POINTER_POS, _UI_PRESS
    pygame.init()
    _HUD_FONTS.clear()
    _UI_RIPPLES.clear()
    _BUTTON_ANIMATIONS.clear()
    _UI_PRESS = None
    ensure_audio_manager()

    display_manager = DisplayManager()
    if not display_manager.settings_file.exists() and not display_manager.preferences["fullscreen"]:
        desktop = pygame.display.get_desktop_sizes()[0]
        display_manager.preferences["window_size"] = [max(320, min(1280, round(desktop[0] * .92))),
                                                        max(240, min(720, round(desktop[1] * .88)))]
    display_manager.open()
    SCREEN_WIDTH, SCREEN_HEIGHT = WORLD_SIZE
    screen = display_manager.world_surface
    pygame.display.set_caption("Space Invaders")

    title_font = pygame.font.SysFont(None, 84)
    death_title_font = pygame.font.SysFont(None, 100)
    button_font = pygame.font.SysFont(None, 36)
    player_choice_font = pygame.font.SysFont(None, 24)
    journal_font = pygame.font.SysFont(None, 20)
    round_font = pygame.font.SysFont(None, 72)
    lives_font = pygame.font.SysFont(None, 36)
    native_ui_underlay = None
    native_threats = pygame.Surface(WORLD_SIZE, pygame.SRCALPHA)

    player_sprites = [
        generate_pixel_sprite(PLAYER_ART, color, PLAYER_WIDTH, PLAYER_HEIGHT)
        for color in PLAYER_COLORS
    ]
    journal_sprites = create_enemy_journal_sprites()

    round_num = STARTING_ROUND
    player_count = 1
    players = create_player_states(player_count, player_sprites)
    checkpoint = save_sector_checkpoint(players, round_num)
    migrate_legacy_save()
    saved_slots = list_saved_runs()
    active_slot = None
    saved_run = None
    save_browser_open = False
    pending_replace_slot = None
    pending_save_action = None
    save_status = None
    save_error = None
    enemies, bunkers, enemy_bullets, player_bullets, particles, powerups, enemy_dx = reset_game_state(round_num)
    enemy_dy = 20

    clock = pygame.time.Clock()
    keyboard = HeldInput()
    keyboard_controls = KeyboardControls()
    game_started = False
    enemy_journal_open = False
    enemy_journal_page = 0
    game_over = False
    retries_remaining = MAX_RUN_RETRIES
    campaign_complete = False
    infinite_mode = False
    death_cutscene_started = None
    victory_started_at = None
    lives_message = None
    paused = False
    paused_at = None

    transitioning = True
    transition_timer = TRANSITION_DURATION
    transition_started_at = pygame.time.get_ticks()

    settings_open = False
    keyboard_controls_open = False
    settings_resume_after_close = False

    def set_game_paused(value):
        nonlocal paused, paused_at, transition_started_at, lives_message
        if value == paused:
            return
        if value:
            paused = True
            paused_at = pygame.time.get_ticks()
            if AUDIO_MANAGER is not None and AUDIO_MANAGER.music_channel is not None:
                AUDIO_MANAGER.music_channel.pause()
            return
        pause_duration = pygame.time.get_ticks() - paused_at
        for player in players:
            for key, deadline in player.items():
                if key.endswith("_until") and deadline:
                    player[key] = deadline + pause_duration
        for enemy in enemies:
            for key in ("cryo_slow_until", "next_fire_ms"):
                if enemy.get(key, 0):
                    enemy[key] += pause_duration
        for shot in enemy_bullets:
            if "aimed_fired_ms" in shot:
                shot["aimed_fired_ms"] += pause_duration
        if transitioning:
            transition_started_at += pause_duration
        if lives_message is not None:
            lives_message = (lives_message[0], lives_message[1] + pause_duration)
        paused = False
        paused_at = None
        if AUDIO_MANAGER is not None and AUDIO_MANAGER.music_channel is not None:
            AUDIO_MANAGER.music_channel.unpause()

    def activate_frame_ui():
        arena = game_started and not game_over and not campaign_complete
        surface = display_manager.activate(arena)
        layout = menu_control_layout()
        if arena:
            layout["display_button_rect"] = gameplay_display_button_rect(
                layout["pause_button_rect"], layout["exit_button_rect"], paused)
        return arena, surface, layout

    def close_display_settings():
        nonlocal settings_open, keyboard_controls_open, settings_resume_after_close
        settings_open = False
        keyboard_controls_open = False
        keyboard.clear()
        if settings_resume_after_close:
            set_game_paused(False)
        settings_resume_after_close = False

    def open_keyboard_controls():
        nonlocal settings_open, keyboard_controls_open, settings_resume_after_close
        if not settings_open:
            settings_resume_after_close = arena and not paused
        settings_open = False
        keyboard_controls_open = True
        keyboard_controls.begin()
        keyboard.clear()
        if settings_resume_after_close:
            set_game_paused(True)

    running = True

    while running:
        _UI_FRAME += 1
        clock.tick(60)
        keyboard.begin_frame()

        arena, ui_surface, controls = activate_frame_ui()
        screen = display_manager.world_surface if arena else ui_surface
        enemy_journal_page = max(0, min(enemy_journal_page, journal_page_count() - 1))
        pending_events = pygame.event.get()
        batch_mode_epoch = display_manager.mode_epoch
        resize_types = (pygame.VIDEORESIZE, getattr(pygame, "WINDOWRESIZED", -1),
                        getattr(pygame, "WINDOWSIZECHANGED", -2))
        last_resize = next((event for event in reversed(pending_events) if event.type in resize_types), None)
        for raw_event in pending_events:
            if raw_event.type in resize_types:
                if raw_event is last_resize and display_manager.mode_epoch == batch_mode_epoch:
                    size = (getattr(raw_event, "w", getattr(raw_event, "x", display_manager.display.get_width())),
                            getattr(raw_event, "h", getattr(raw_event, "y", display_manager.display.get_height())))
                    display_manager.resize(size, from_event=True)
                continue
            arena, ui_surface, controls = activate_frame_ui()
            event = display_manager.map_event(raw_event, arena)
            if event.type == pygame.QUIT:
                running = False
                continue
            if event.type in (pygame.WINDOWFOCUSLOST, pygame.WINDOWFOCUSGAINED, pygame.ACTIVEEVENT):
                keyboard.process_event(event)
            if keyboard_controls_open:
                if keyboard_controls.process_event(event):
                    close_display_settings()
                keyboard.clear()
                continue
            if (event.type == pygame.KEYDOWN and event.key == pygame.K_F9
                    and pending_save_action is None and pending_replace_slot is None):
                open_keyboard_controls()
                continue
            if raw_event.type == pygame.KEYDOWN and raw_event.key in (pygame.K_F6, pygame.K_F7, pygame.K_F8, pygame.K_F11):
                if raw_event.key == pygame.K_F6:
                    display_manager.adjust_gui_scale(-1)
                elif raw_event.key == pygame.K_F7:
                    display_manager.adjust_gui_scale(1)
                elif raw_event.key == pygame.K_F8:
                    display_manager.reset_gui_scale()
                else:
                    display_manager.toggle_fullscreen()
                keyboard.discard_taps()
                continue
            if (raw_event.type == pygame.MOUSEWHEEL
                    and pygame.key.get_mods() & pygame.KMOD_CTRL):
                if raw_event.y:
                    display_manager.adjust_gui_scale(1 if raw_event.y > 0 else -1)
                keyboard.discard_taps()
                continue
            if settings_open:
                if event.type == pygame.KEYDOWN and event.key in (pygame.K_ESCAPE, pygame.K_RETURN, pygame.K_KP_ENTER):
                    close_display_settings()
                elif event.type == pygame.MOUSEBUTTONDOWN:
                    settings_layout = display_settings_layout()
                    if settings_layout["smaller"].collidepoint(event.pos):
                        display_manager.adjust_gui_scale(-1)
                    elif settings_layout["larger"].collidepoint(event.pos):
                        display_manager.adjust_gui_scale(1)
                    elif settings_layout["auto"].collidepoint(event.pos):
                        display_manager.reset_gui_scale()
                    elif settings_layout["mode"].collidepoint(event.pos):
                        display_manager.toggle_fullscreen()
                    elif settings_layout["close"].collidepoint(event.pos):
                        close_display_settings()
                    elif settings_layout["keyboard"].collidepoint(event.pos):
                        open_keyboard_controls()
                keyboard.discard_taps()
                continue
            if (event.type == pygame.MOUSEBUTTONDOWN and pending_save_action is None
                    and pending_replace_slot is None
                    and controls["display_button_rect"].collidepoint(event.pos)):
                settings_open = True
                settings_resume_after_close = arena and not paused
                if settings_resume_after_close:
                    set_game_paused(True)
                register_ui_click(event.pos, UI_CYAN)
                keyboard.clear()
                continue
            if (event.type == pygame.MOUSEBUTTONDOWN and not game_started
                    and save_browser_open and pending_replace_slot is None and pending_save_action is None):
                tabs = save_browser_layout().get("slot_tabs", [])
                selected = next((index for index, rect in enumerate(tabs, start=1)
                                 if rect.collidepoint(event.pos)), None)
                if selected is not None:
                    set_selected_save_slot(selected)
                    register_ui_click(event.pos, UI_GOLD)
                    continue
            keyboard.process_event(event)
            requested_run = None
            if event.type == pygame.QUIT:
                running = False

            if not game_started and save_browser_open and pending_save_action is not None:
                action = pending_save_action
                finished = False
                message = None
                if event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE:
                    pending_save_action = None
                    pygame.key.stop_text_input()
                    keyboard.discard_taps()
                elif event.type == pygame.KEYDOWN and event.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
                    finished, message = confirm_save_action(action)
                elif event.type == pygame.MOUSEBUTTONDOWN:
                    layout = save_browser_layout()
                    if layout["cancel"].collidepoint(event.pos):
                        pending_save_action = None
                        pygame.key.stop_text_input()
                    elif layout["confirm"].collidepoint(event.pos):
                        register_ui_click(event.pos, UI_CYAN)
                        finished, message = confirm_save_action(action)
                    elif action["stage"] == "path" and layout["browse"].collidepoint(event.pos):
                        browse_save_transfer(action)
                    elif action["stage"] == "path" and layout["path_input"].collidepoint(event.pos):
                        action["select_all"] = True
                else:
                    update_save_action_input(action, event)
                if finished:
                    saved_slots = list_saved_runs()
                    if active_slot == action["slot"] and action["kind"] in ("delete", "import"):
                        saved_run = saved_slots[active_slot - 1]
                    save_error = None
                    save_status = message
                    pending_save_action = None
                    keyboard.discard_taps()
                continue

            if (event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE
                    and not game_started and save_browser_open):
                if pending_replace_slot is not None:
                    pending_replace_slot = None
                else:
                    save_browser_open = False
                keyboard.discard_taps()

            if (
                event.type == pygame.KEYDOWN
                and not game_started
                and enemy_journal_open
                and event.key == pygame.K_ESCAPE
            ):
                enemy_journal_open = False

            if event.type == pygame.MOUSEBUTTONDOWN:
                # Only enabled, visible controls produce interaction feedback.
                ui_targets = []
                if not game_started:
                    if save_browser_open:
                        layout = save_browser_layout()
                        if pending_replace_slot is not None:
                            ui_targets = [(layout["confirm"], UI_CORAL), (layout["cancel"], UI_CYAN)]
                        else:
                            ui_targets = [(layout["back"], UI_CYAN), (layout["quit"], UI_CORAL)]
                            for card in layout["cards"]:
                                snapshot = saved_slots[card["slot"] - 1]
                                ui_targets.append((card["new"], UI_MINT))
                                ui_targets.append((card["import"], UI_GOLD))
                                if save_slot_occupied(card["slot"]):
                                    ui_targets.append((card["delete"], UI_CORAL))
                                if snapshot is not None:
                                    if saved_run_can_continue(snapshot):
                                        ui_targets.append((card["continue"], UI_GOLD))
                                    ui_targets.append((card["export"], UI_CYAN))
                    elif enemy_journal_open:
                        ui_targets = [(controls["journal_back_rect"], UI_VIOLET)]
                        if enemy_journal_page > 0:
                            ui_targets.append((controls["journal_previous_rect"], UI_CYAN))
                        if enemy_journal_page < journal_page_count() - 1:
                            ui_targets.append((controls["journal_next_rect"], UI_CYAN))
                    else:
                        ui_targets = [(controls["start_button_rect"], UI_MINT), (controls["journal_button_rect"], UI_VIOLET)]
                        ui_targets.append((controls["continue_button_rect"], UI_GOLD))
                        ui_targets.extend((rect, PLAYER_COLORS[index]) for index, rect in enumerate(controls["choice_button_rects"]))
                elif game_over:
                    if infinite_mode or (death_cutscene_started is not None
                            and pygame.time.get_ticks() - death_cutscene_started >= DEFEAT_CUTSCENE_DURATION):
                        ui_targets = [(controls["play_again_rect"], UI_CYAN)]
                        if retries_remaining > 0:
                            ui_targets.append((controls["checkpoint_rect"], UI_GOLD))
                elif campaign_complete:
                    if victory_started_at is not None and pygame.time.get_ticks() - victory_started_at >= VICTORY_CUTSCENE_DURATION:
                        ui_targets = [(controls["play_again_rect"], UI_CYAN), (controls["infinite_mode_rect"], UI_GOLD)]
                else:
                    ui_targets = [(controls["pause_button_rect"], UI_MINT if paused else UI_CYAN)]
                    if paused:
                        ui_targets.append((controls["exit_button_rect"], UI_CORAL))
                for ui_rect, ui_color in ui_targets:
                    if ui_rect.collidepoint(event.pos):
                        register_ui_click(event.pos, ui_color)
                        break
                if not game_started:
                    if save_browser_open:
                        layout = save_browser_layout()
                        if pending_replace_slot is not None:
                            if layout["confirm"].collidepoint(event.pos):
                                requested_run = (pending_replace_slot, None)
                            elif layout["cancel"].collidepoint(event.pos):
                                pending_replace_slot = None
                        elif layout["back"].collidepoint(event.pos):
                            save_browser_open = False
                        elif layout["quit"].collidepoint(event.pos):
                            running = False
                        else:
                            for card in layout["cards"]:
                                snapshot = saved_slots[card["slot"] - 1]
                                slot = card["slot"]
                                if card["import"].collidepoint(event.pos):
                                    pending_save_action = begin_save_action("import", slot)
                                    save_status = None
                                    break
                                if snapshot is not None and card["export"].collidepoint(event.pos):
                                    pending_save_action = begin_save_action("export", slot)
                                    save_status = None
                                    break
                                if save_slot_occupied(slot) and card["delete"].collidepoint(event.pos):
                                    pending_save_action = begin_save_action("delete", slot)
                                    save_status = None
                                    break
                                if (saved_run_can_continue(snapshot)
                                        and card["continue"].collidepoint(event.pos)):
                                    requested_run = (slot, snapshot)
                                    break
                                if card["new"].collidepoint(event.pos):
                                    if save_slot_occupied(slot):
                                        pending_replace_slot = slot
                                    else:
                                        requested_run = (slot, None)
                                    break
                    elif enemy_journal_open:
                        if controls["journal_back_rect"].collidepoint(event.pos):
                            enemy_journal_open = False
                        elif controls["journal_previous_rect"].collidepoint(event.pos):
                            enemy_journal_page = max(0, enemy_journal_page - 1)
                        elif controls["journal_next_rect"].collidepoint(event.pos):
                            max_page = journal_page_count() - 1
                            enemy_journal_page = min(max_page, enemy_journal_page + 1)
                    else:
                        for index, choice_rect in enumerate(controls["choice_button_rects"], start=1):
                            if choice_rect.collidepoint(event.pos):
                                player_count = index
                                players = create_player_states(player_count, player_sprites)
                                break

                        if controls["journal_button_rect"].collidepoint(event.pos):
                            enemy_journal_open = True
                            enemy_journal_page = 0
                        elif controls["continue_button_rect"].collidepoint(event.pos):
                            saved_slots = list_saved_runs()
                            save_browser_open = True
                            pending_replace_slot = None
                        elif controls["start_button_rect"].collidepoint(event.pos):
                            saved_slots = list_saved_runs()
                            free_slot = next((slot for slot in range(1, SAVE_SLOT_COUNT + 1)
                                              if not save_slot_occupied(slot)), None)
                            if free_slot is None:
                                save_browser_open = True
                                pending_replace_slot = None
                            else:
                                requested_run = (free_slot, None)

                elif game_over:
                    cutscene_finished = infinite_mode or (
                        death_cutscene_started is not None
                        and pygame.time.get_ticks() - death_cutscene_started >= DEFEAT_CUTSCENE_DURATION
                    )
                    if (cutscene_finished and retries_remaining > 0
                            and controls["checkpoint_rect"].collidepoint(event.pos)):
                        # Resume directly at the latest checkpoint. This works
                        # for any defeated pilot, including solo players.
                        retry_players, saved_run, save_error = prepare_checkpoint_retry(
                            checkpoint, player_sprites, infinite_mode, saved_run,
                            active_slot, retries_remaining)
                        saved_slots[active_slot - 1] = saved_run
                        keyboard.discard_taps()
                        if retry_players is not None:
                            retries_remaining -= 1
                            round_num = checkpoint["wave"]
                            players = retry_players
                            enemies, bunkers, enemy_bullets, player_bullets, particles, powerups, enemy_dx = reset_game_state(
                                round_num, infinite_mode=infinite_mode)
                            game_over = False
                            death_cutscene_started = None
                            lives_message = None
                            transitioning = True
                            transition_timer = TRANSITION_DURATION
                            transition_started_at = pygame.time.get_ticks()
                    elif cutscene_finished and controls["play_again_rect"].collidepoint(event.pos):
                        game_started = False
                        game_over = False
                        infinite_mode = False
                        campaign_complete = False
                        victory_started_at = None
                        death_cutscene_started = None
                        round_num = STARTING_ROUND
                        players = create_player_states(player_count, player_sprites)
                        checkpoint = save_sector_checkpoint(players, round_num)
                        saved_slots = list_saved_runs()
                        save_browser_open = True
                        pending_replace_slot = None
                        keyboard.discard_taps()
                        enemies, bunkers, enemy_bullets, player_bullets, particles, powerups, enemy_dx = reset_game_state(round_num)
                        transitioning = True
                        transition_timer = TRANSITION_DURATION
                        transition_started_at = pygame.time.get_ticks()

                elif campaign_complete:
                    cutscene_finished = (
                        victory_started_at is not None
                        and pygame.time.get_ticks() - victory_started_at >= VICTORY_CUTSCENE_DURATION
                    )
                    if cutscene_finished and controls["infinite_mode_rect"].collidepoint(event.pos):
                        completion_duration = pygame.time.get_ticks() - victory_started_at
                        for player in players:
                            for key, value in player.items():
                                if key.endswith("_until") and value:
                                    player[key] = value + completion_duration
                        campaign_complete = False
                        victory_started_at = None
                        infinite_mode = True
                        game_over = False
                        round_num = MAX_CAMPAIGN_ROUND + 1
                        revive_eliminated_teammates(players)
                        enemies, bunkers, enemy_bullets, player_bullets, particles, powerups, enemy_dx = reset_game_state(
                            round_num,
                            powerups,
                            infinite_mode=True,
                        )
                        reset_player_positions(players)
                        checkpoint = save_sector_checkpoint(players, round_num)
                        saved_run, save_error = autosave_run(
                            round_num, players, checkpoint, infinite_mode, saved_run, slot=active_slot,
                            retries_remaining=retries_remaining)
                        saved_slots[active_slot - 1] = saved_run
                        keyboard.discard_taps()
                        transitioning = True
                        transition_timer = TRANSITION_DURATION
                        transition_started_at = pygame.time.get_ticks()
                    elif cutscene_finished and controls["play_again_rect"].collidepoint(event.pos):
                        campaign_complete = False
                        victory_started_at = None
                        infinite_mode = False
                        game_started = False
                        game_over = False
                        death_cutscene_started = None
                        round_num = STARTING_ROUND
                        players = create_player_states(player_count, player_sprites)
                        checkpoint = save_sector_checkpoint(players, round_num)
                        saved_slots = list_saved_runs()
                        save_browser_open = True
                        pending_replace_slot = None
                        keyboard.discard_taps()
                        enemies, bunkers, enemy_bullets, player_bullets, particles, powerups, enemy_dx = reset_game_state(round_num)

                else:
                    if controls["pause_button_rect"].collidepoint(event.pos):
                        keyboard.discard_taps()
                        set_game_paused(not paused)
                    elif paused and controls["exit_button_rect"].collidepoint(event.pos):
                        keyboard.discard_taps()
                        paused = False
                        paused_at = None
                        if AUDIO_MANAGER is not None and AUDIO_MANAGER.music_channel is not None:
                            AUDIO_MANAGER.music_channel.unpause()
                        game_started = False
                        game_over = False
                        round_num = STARTING_ROUND
                        players = create_player_states(player_count, player_sprites)
                        checkpoint = save_sector_checkpoint(players, round_num)
                        saved_slots = list_saved_runs()
                        save_browser_open = True
                        pending_replace_slot = None
                        enemies, bunkers, enemy_bullets, player_bullets, particles, powerups, enemy_dx = reset_game_state(round_num)
                        transitioning = True
                        transition_timer = TRANSITION_DURATION
                        transition_started_at = pygame.time.get_ticks()

            if requested_run is not None:
                active_slot, requested_snapshot = requested_run
                resuming_defeat = bool(requested_snapshot and requested_snapshot.get("run_defeated", False))
                if requested_snapshot is None:
                    retries_remaining = MAX_RUN_RETRIES
                    round_num = STARTING_ROUND
                    infinite_mode = False
                    players = create_player_states(player_count, player_sprites)
                    checkpoint = save_sector_checkpoint(players, round_num)
                    saved_run, save_error = autosave_run(
                        round_num, players, checkpoint, previous_save=saved_slots[active_slot - 1],
                        slot=active_slot, retries_remaining=retries_remaining)
                    saved_slots[active_slot - 1] = saved_run
                else:
                    saved_run = requested_snapshot
                    save_error = None
                    retries_remaining = saved_run.get("retries_remaining", MAX_RUN_RETRIES)
                    round_num, players, checkpoint, infinite_mode = restore_saved_run(saved_run, player_sprites)
                    player_count = len(players)
                enemies, bunkers, enemy_bullets, player_bullets, particles, powerups, enemy_dx = reset_game_state(
                    round_num, infinite_mode=infinite_mode)
                game_started = True
                game_over = resuming_defeat
                campaign_complete = False
                enemy_journal_open = False
                save_browser_open = False
                pending_replace_slot = None
                pending_save_action = None
                save_status = None
                paused = False
                paused_at = None
                lives_message = None
                death_cutscene_started = (pygame.time.get_ticks() - DEFEAT_CUTSCENE_DURATION
                                          if resuming_defeat else None)
                victory_started_at = None
                transitioning = True
                transition_timer = TRANSITION_DURATION
                transition_started_at = pygame.time.get_ticks()
                keyboard.discard_taps()

        arena, ui_surface, controls = activate_frame_ui()
        screen = display_manager.world_surface if arena else ui_surface
        enemy_journal_page = max(0, min(enemy_journal_page, journal_page_count() - 1))
        if not game_started:
            if save_browser_open:
                draw_save_browser(screen, saved_slots, title_font, button_font,
                                  player_choice_font, pending_replace_slot=pending_replace_slot,
                                  save_error=save_error, pending_save_action=pending_save_action,
                                  save_status=save_status)
            elif enemy_journal_open:
                draw_enemy_journal(
                    screen,
                    enemy_journal_page,
                    title_font,
                    button_font,
                    player_choice_font,
                    journal_font,
                    journal_sprites,
                    controls["journal_previous_rect"],
                    controls["journal_next_rect"],
                    controls["journal_back_rect"],
                )
            else:
                draw_start_screen(
                    screen,
                    controls["start_button_rect"],
                    controls["journal_button_rect"],
                    controls["choice_button_rects"],
                    title_font,
                    button_font,
                    player_choice_font,
                    player_count,
                    saved_run=saved_run,
                    continue_button_rect=controls["continue_button_rect"],
                    save_error=save_error,
                    saved_slots=saved_slots,
                )

        elif campaign_complete:
            victory_elapsed = pygame.time.get_ticks() - victory_started_at
            if victory_elapsed < VICTORY_CUTSCENE_DURATION:
                draw_victory_cutscene(
                    screen,
                    victory_elapsed,
                    death_title_font,
                    button_font,
                    players,
                )
            else:
                draw_completion_screen(
                    screen,
                    death_title_font,
                    button_font,
                    player_choice_font,
                    controls["play_again_rect"],
                    controls["infinite_mode_rect"],
                    players,
                )

        elif game_over:
            if death_cutscene_started is None:
                death_cutscene_started = pygame.time.get_ticks() - (
                    DEFEAT_CUTSCENE_DURATION if infinite_mode else 0
                )
            cutscene_elapsed = pygame.time.get_ticks() - death_cutscene_started
            if cutscene_elapsed < DEFEAT_CUTSCENE_DURATION:
                draw_alien_invasion_cutscene(
                    screen,
                    cutscene_elapsed,
                    title_font,
                    button_font,
                )
            else:
                draw_death_screen(
                    screen,
                    death_title_font,
                    button_font,
                    player_choice_font,
                    controls["play_again_rect"],
                    players,
                    round_num,
                    controls["checkpoint_rect"],
                    checkpoint["wave"],
                    retries_remaining=retries_remaining,
                    save_error=save_error,
                )

        else:
            if not paused:
                now = pygame.time.get_ticks()
                for player in players:
                    if (not transitioning and player["respawn_until"]
                            and now >= player["respawn_until"]):
                        player["x"] = player["spawn_x"]
                        player["y"] = player_spawn_y()
                        player["respawn_until"] = 0
                        player["shield_until"] = now + SPAWN_SHIELD_DURATION
                        reset_player_animation(player)

                if not enemies and not transitioning:
                    if round_num % 5 == 0:
                        grant_boss_clear_life(players)
                    if round_num >= MAX_CAMPAIGN_ROUND and not infinite_mode:
                        campaign_complete = True
                        # Retain this slot so its final boss can be replayed.
                        victory_started_at = pygame.time.get_ticks()
                    else:
                        old_sector = sector_for_round(round_num)
                        round_num += 1
                        if sector_for_round(round_num) != old_sector:
                            revive_eliminated_teammates(players)
                            checkpoint = save_sector_checkpoint(players, round_num)
                        enemies, bunkers, enemy_bullets, player_bullets, particles, powerups, enemy_dx = reset_game_state(
                            round_num,
                            powerups,
                            infinite_mode=infinite_mode,
                        )
                        reset_player_positions(players)
                        saved_run, save_error = autosave_run(
                            round_num, players, checkpoint, infinite_mode, saved_run, slot=active_slot,
                            retries_remaining=retries_remaining)
                        saved_slots[active_slot - 1] = saved_run
                        transitioning = True
                        transition_timer = TRANSITION_DURATION
                        transition_started_at = pygame.time.get_ticks()

                if not transitioning and not campaign_complete:
                    keys = keyboard
                    update_durability(players, now)
                    update_player_movement(keys, players)
                    update_player_projectiles(keys, players, player_count, player_bullets, enemies)
                    check_player_bullet_collisions(
                        player_bullets, enemies, particles, enemy_bullets, powerups, players
                    )
                    update_powerups(powerups, players, enemy_bullets, particles)
                    resolve_instant_powerups(players, enemies, enemy_bullets,
                                             player_bullets, powerups, particles)
                    check_bunker_collisions(bunkers, player_bullets, enemy_bullets, enemies, particles)
                    enemy_dx = update_enemies(enemies, enemy_dx, enemy_dy, round_num)
                    check_player_ram_collisions(
                        enemies, particles, enemy_bullets, powerups, players
                    )
                    targets = [
                        (
                            max(
                                0,
                                min(
                                    SCREEN_WIDTH,
                                    player["x"] + PLAYER_WIDTH / 2
                                    + player["move_dx"] * ENEMY_AIM_LEAD_FRAMES,
                                ),
                            ),
                            max(
                                0,
                                min(
                                    SCREEN_HEIGHT,
                                    player["y"] + PLAYER_HEIGHT / 2
                                    + player["move_dy"] * ENEMY_AIM_LEAD_FRAMES,
                                ),
                            ),
                        )
                        for player in players
                        if not player["eliminated"] and player["respawn_until"] == 0
                    ]
                    update_enemy_projectiles(enemies, enemy_bullets, targets, players, particles, round_num)
                    game_over, lives_message = death(
                        enemies, enemy_bullets, particles, players, lives_font, lives_message
                    )
                    if game_over:
                        saved_run, save_error = autosave_run(
                            round_num, players, checkpoint, infinite_mode, saved_run, slot=active_slot,
                            retries_remaining=retries_remaining, run_defeated=True)
                        saved_slots[active_slot - 1] = saved_run

            if not paused:
                update_ship_animations(players, enemies)

            if (native_ui_underlay is None
                    or native_ui_underlay.get_size() != ui_surface.get_size()):
                native_ui_underlay = pygame.Surface(ui_surface.get_size(), pygame.SRCALPHA)
            draw_gameplay(
                screen,
                enemies,
                enemy_bullets,
                player_bullets,
                bunkers,
                particles,
                powerups,
                players,
                controls["exit_button_rect"],
                controls["pause_button_rect"],
                player_choice_font,
                paused,
                paused_at,
                transition_started_at if transitioning else None,
                round_num=round_num,
                save_error=save_error,
                ui_surface=native_ui_underlay,
                defer_ui_overlay=True,
                defer_native_ui=True,
            )
            native_threats.fill((0, 0, 0, 0))
            threat_now = (paused_at if paused and paused_at is not None
                          else transition_started_at if transitioning
                          else pygame.time.get_ticks())
            has_native_threats = bool(enemy_bullets) or any(
                enemy.get("signature_warning") for enemy in enemies)
            if has_native_threats:
                draw_hostile_projectiles(native_threats, enemy_bullets, threat_now, enemies=enemies)

            if transitioning and not paused:
                draw_round_transition(screen, round_num, round_font, transition_timer)
                transition_timer -= 1
                if transition_timer <= 0:
                    transition_duration = pygame.time.get_ticks() - transition_started_at
                    for player in players:
                        for key, value in player.items():
                            if key.endswith("_until") and value:
                                player[key] = value + transition_duration
                    transitioning = False

        if arena:
            ui_surface.fill((0, 0, 0, 0))
            with ui_dimensions(ui_surface.get_size()):
                draw_gameplay_ui_overlay(ui_surface, controls["exit_button_rect"],
                                         controls["pause_button_rect"], player_choice_font,
                                         paused, save_error)
                if not paused:
                    lives_message = draw_lives_text(ui_surface, lives_message)
                if pending_save_action is None and pending_replace_slot is None:
                    display_label = "GUI" if controls["display_button_rect"].width < 80 else "DISPLAY"
                    draw_neon_button(ui_surface, controls["display_button_rect"], display_label, journal_font, UI_CYAN)
                draw_ui_feedback(ui_surface)
                if settings_open:
                    draw_display_settings(ui_surface, display_manager, button_font, player_choice_font)
                if keyboard_controls_open:
                    keyboard_controls.draw(ui_surface, button_font, journal_font)
        else:
            with ui_dimensions(screen.get_size()):
                if pending_save_action is None and pending_replace_slot is None:
                    display_label = "GUI" if controls["display_button_rect"].width < 80 else "DISPLAY"
                    draw_neon_button(screen, controls["display_button_rect"], display_label, journal_font, UI_CYAN)
                draw_ui_feedback(screen)
                if settings_open:
                    draw_display_settings(screen, display_manager, button_font, player_choice_font)
                if keyboard_controls_open:
                    keyboard_controls.draw(screen, button_font, journal_font)
        display_manager.flush_preferences()
        if arena:
            display_manager.present(screen, arena, ui_underlay=native_ui_underlay,
                                    ui_overlay=ui_surface,
                                    threat_surface=native_threats if has_native_threats else None)
        else:
            display_manager.present(screen, arena)

    display_manager.flush_preferences(force=True)
    _UI_LAYOUT_SIZE = None
    _UI_POINTER_POS = None
    SCREEN_WIDTH, SCREEN_HEIGHT = WORLD_SIZE
    pygame.quit()
    sys.exit()

if __name__ == "__main__":
    main()
