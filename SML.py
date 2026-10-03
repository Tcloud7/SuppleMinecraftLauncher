"""
Supple Minecraft Launcher - early self-made launcher prototype

Scope:
- Microsoft account sign-in via OAuth device-code flow
- Saves signed-in account list locally
- Encrypts Microsoft token cache using Windows DPAPI
- Easy account switching
- Minecraft Java ownership/profile verification
- Launches installed Java versions directly from .minecraft
- Detects and launches installed Minecraft-family Windows apps
  (Bedrock, Dungeons, Dungeons II, Legends) through Windows app activation

IMPORTANT:
Minecraft Services currently rejects ordinary third-party Microsoft client IDs
unless the app registration has been authorized/allowlisted for Minecraft
Services. Put YOUR approved Microsoft application client ID into Settings.

Dependencies:
    py -m pip install msal requests minecraft-launcher-lib

Windows only.
"""

from __future__ import annotations

import base64
import io
import ctypes
from html.parser import HTMLParser
from datetime import datetime, timezone
from ctypes import wintypes
import json
import os
from pathlib import Path
import platform
import queue
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import tkinter as tk
import tkinter.font as tkfont
from tkinter import ttk, messagebox, simpledialog, filedialog
import zipfile
import webbrowser

try:
    from PIL import Image, ImageTk, ImageDraw, ImageFont
except ImportError:
    Image = None
    ImageTk = None


try:
    import requests
    import msal
except ImportError:
    root = tk.Tk()
    root.withdraw()
    messagebox.showerror(
        "Missing dependencies",
        "This launcher needs two Python packages:\n\n"
        "py -m pip install msal requests"
    )
    raise

# Optional authentication cross-check. Supple can still start without this
# package, but when it is installed we try its well-tested Xbox/Minecraft
# authentication implementation before Supple's native implementation.
try:
    import minecraft_launcher_lib
except ImportError:
    minecraft_launcher_lib = None

APP_NAME = "Supple Minecraft Launcher"
APP_VERSION = "1.0.0"
DEFAULT_CLIENT_ID = "6e72e008-b746-4490-ab99-ccff4ce31871"

BASE_DIR = Path(__file__).resolve().parent
SETTINGS_FILE = BASE_DIR / "settings.json"
INSTALLATIONS_FILE = BASE_DIR / "installations.json"
ACCOUNT_METADATA_FILE = BASE_DIR / "account_metadata.dpapi"
CACHE_FILE = BASE_DIR / "token_cache.dpapi"
LOG_FILE = BASE_DIR / "launcher.log"
TEXTURES_DIR = BASE_DIR / "textures"
APP_ICON_FILE = TEXTURES_DIR / "icon.ico"
FONTS_DIR = BASE_DIR / "fonts"
MODSTORAGE_DIR = BASE_DIR / "modstorage"
MODREF_FILE = MODSTORAGE_DIR / "modref.json"
VERSIONREF_FILE = BASE_DIR / "versionref.json"

# One-time migration source from older SML builds.
LEGACY_DATA_DIR = Path(os.getenv("APPDATA", Path.home())) / "SuppleLauncher"
LEGACY_CONFIG_FILE = LEGACY_DATA_DIR / "config.json"
LEGACY_CACHE_FILE = LEGACY_DATA_DIR / "token_cache.dpapi"

MC_DIR = Path(os.getenv("APPDATA", Path.home())) / ".minecraft"

DEFAULT_CONFIG = {
    "client_id": DEFAULT_CLIENT_ID,
    "selected_account": "",
    "account_order": [],
    "page_state": {},
    "selected_java_version": "",
    "selected_installation": "",
    "java_memory_mb": 4096,
    "minecraft_dir": str(MC_DIR),
    "show_log_window": False,
    "date_format": "MM/DD/YYYY",
    "censor_account_email": True,
    "censor_account_microsoft": True,
    "censor_account_java": False,
    "bedrock_data_dir": "",
    "dungeons_data_dir": "",
    "dungeons2_data_dir": "",
    "legends_data_dir": "",
}

DEFAULT_INSTALLATIONS = {"installations": []}

AUTHORITY = "https://login.microsoftonline.com/consumers"

LEGACY_MINECRAFT_CLIENT_IDS = {"00000000402b5328"}
SCOPES = ["XboxLive.signin"]

XBL_AUTH = "https://user.auth.xboxlive.com/user/authenticate"
XSTS_AUTH = "https://xsts.auth.xboxlive.com/xsts/authorize"
MC_LOGIN = "https://api.minecraftservices.com/authentication/login_with_xbox"
MC_PROFILE = "https://api.minecraftservices.com/minecraft/profile"
MC_ENTITLEMENTS = "https://api.minecraftservices.com/entitlements/mcstore"

CREATE_NO_WINDOW = 0x08000000 if os.name == "nt" else 0


# ----------------------------- Windows DPAPI -----------------------------

class DATA_BLOB(ctypes.Structure):
    _fields_ = [
        ("cbData", wintypes.DWORD),
        ("pbData", ctypes.POINTER(ctypes.c_byte)),
    ]


def _blob(data: bytes):
    buf = ctypes.create_string_buffer(data)
    return DATA_BLOB(len(data), ctypes.cast(buf, ctypes.POINTER(ctypes.c_byte))), buf


def dpapi_encrypt(data: bytes) -> bytes:
    if os.name != "nt":
        raise RuntimeError("This launcher currently supports Windows only.")
    in_blob, in_buf = _blob(data)
    out_blob = DATA_BLOB()
    crypt32 = ctypes.windll.crypt32
    kernel32 = ctypes.windll.kernel32
    if not crypt32.CryptProtectData(
        ctypes.byref(in_blob), APP_NAME, None, None, None, 0, ctypes.byref(out_blob)
    ):
        raise ctypes.WinError()
    try:
        result = ctypes.string_at(out_blob.pbData, out_blob.cbData)
    finally:
        kernel32.LocalFree(out_blob.pbData)
    return result


def dpapi_decrypt(data: bytes) -> bytes:
    if os.name != "nt":
        raise RuntimeError("This launcher currently supports Windows only.")
    in_blob, in_buf = _blob(data)
    out_blob = DATA_BLOB()
    crypt32 = ctypes.windll.crypt32
    kernel32 = ctypes.windll.kernel32
    if not crypt32.CryptUnprotectData(
        ctypes.byref(in_blob), None, None, None, None, 0, ctypes.byref(out_blob)
    ):
        raise ctypes.WinError()
    try:
        result = ctypes.string_at(out_blob.pbData, out_blob.cbData)
    finally:
        kernel32.LocalFree(out_blob.pbData)
    return result


# ------------------------------- Utilities -------------------------------

def ensure_local_storage():
    for folder in (TEXTURES_DIR, FONTS_DIR, MODSTORAGE_DIR):
        folder.mkdir(parents=True, exist_ok=True)


def _read_json(path: Path, default):
    if not path.exists():
        return json.loads(json.dumps(default))
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(data, dict):
            return data
    except Exception as exc:
        log(f"Could not read {path.name}: {exc}")
    return json.loads(json.dumps(default))


def _write_json(path: Path, data):
    path.write_text(json.dumps(data, indent=2), encoding="utf-8")


def normalize_installation(item):
    if isinstance(item, str):
        name = item.strip()
        if not name:
            return None
        return {"name": name, "version": "", "vanilla": True, "mods": []}

    if not isinstance(item, dict):
        return None

    name = str(item.get("name", "")).strip()
    if not name:
        return None

    mods = item.get("mods", [])
    if not isinstance(mods, list):
        mods = []

    clean_mods = []
    for mod in mods:
        filename = Path(str(mod)).name
        if filename and filename not in clean_mods:
            clean_mods.append(filename)

    return {
        "name": name,
        "version": str(item.get("version", "")),
        "vanilla": bool(item.get("vanilla", True)),
        "mods": clean_mods,
    }


def migrate_legacy_storage():
    ensure_local_storage()

    legacy = {}
    if LEGACY_CONFIG_FILE.exists():
        try:
            legacy = json.loads(LEGACY_CONFIG_FILE.read_text(encoding="utf-8"))
        except Exception:
            legacy = {}

    if not SETTINGS_FILE.exists():
        settings = DEFAULT_CONFIG.copy()
        if isinstance(legacy, dict):
            for key in settings:
                if key in legacy:
                    settings[key] = legacy[key]
        _write_json(SETTINGS_FILE, settings)

    if not INSTALLATIONS_FILE.exists():
        old_list = legacy.get("installations", []) if isinstance(legacy, dict) else []
        normalized = []
        if isinstance(old_list, list):
            for item in old_list:
                clean = normalize_installation(item)
                if clean is not None:
                    normalized.append(clean)
        _write_json(INSTALLATIONS_FILE, {"installations": normalized})

    if not CACHE_FILE.exists() and LEGACY_CACHE_FILE.exists():
        try:
            shutil.copy2(LEGACY_CACHE_FILE, CACHE_FILE)
        except Exception:
            pass


def log(msg: str):
    ensure_local_storage()
    stamp = time.strftime("%Y-%m-%d %H:%M:%S")
    with LOG_FILE.open("a", encoding="utf-8") as f:
        f.write(f"[{stamp}] {msg}\\n")



def load_account_metadata():
    """
    Account/profile display metadata is encrypted with Windows DPAPI.
    The file can only be decrypted by the same Windows user account.
    """
    ensure_local_storage()

    if not ACCOUNT_METADATA_FILE.exists():
        return {
            "profiles": {}
        }

    try:
        encrypted = ACCOUNT_METADATA_FILE.read_bytes()
        raw = dpapi_decrypt(encrypted).decode("utf-8")
        data = json.loads(raw)

        if not isinstance(data, dict):
            return {"profiles": {}}

        profiles = data.get("profiles", {})

        if not isinstance(profiles, dict):
            profiles = {}

        return {
            "profiles": profiles
        }

    except Exception as exc:
        log(
            f"Could not read encrypted account metadata: {exc}"
        )
        return {
            "profiles": {}
        }


def save_account_metadata(data):
    ensure_local_storage()

    clean = {
        "profiles": data.get(
            "profiles",
            {}
        )
        if isinstance(data, dict)
        else {}
    }

    raw = json.dumps(
        clean,
        indent=2
    ).encode("utf-8")

    ACCOUNT_METADATA_FILE.write_bytes(
        dpapi_encrypt(raw)
    )


def load_config():
    ensure_local_storage()
    migrate_legacy_storage()

    cfg = DEFAULT_CONFIG.copy()
    data = _read_json(SETTINGS_FILE, DEFAULT_CONFIG)
    for key in DEFAULT_CONFIG:
        if key in data:
            cfg[key] = data[key]

    if not str(cfg.get("client_id", "")).strip():
        cfg["client_id"] = DEFAULT_CLIENT_ID


    # One-time migration of old plaintext account/profile metadata.
    legacy_profile_cache = data.get(
        "account_profile_cache",
        {}
    )

    if isinstance(
        legacy_profile_cache,
        dict
    ) and legacy_profile_cache:
        metadata = load_account_metadata()
        profiles = metadata.setdefault(
            "profiles",
            {}
        )
        profiles.update(
            legacy_profile_cache
        )
        save_account_metadata(
            metadata
        )

        # Remove it from settings.json on the next save.
        data.pop(
            "account_profile_cache",
            None
        )

    return cfg


def save_config(cfg):
    ensure_local_storage()
    clean = DEFAULT_CONFIG.copy()
    for key in DEFAULT_CONFIG:
        if key in cfg:
            clean[key] = cfg[key]
    _write_json(SETTINGS_FILE, clean)


def load_installations_file():
    ensure_local_storage()
    migrate_legacy_storage()

    data = _read_json(INSTALLATIONS_FILE, DEFAULT_INSTALLATIONS)
    raw = data.get("installations", [])
    if not isinstance(raw, list):
        raw = []

    installations = []
    for item in raw:
        clean = normalize_installation(item)
        if clean is not None:
            installations.append(clean)

    return {"installations": installations}


def save_installations_file(data):
    ensure_local_storage()
    normalized = []
    for item in data.get("installations", []):
        clean = normalize_installation(item)
        if clean is not None:
            normalized.append(clean)
    _write_json(INSTALLATIONS_FILE, {"installations": normalized})


def safe_version_folder_name(version: str) -> str:
    value = str(version).strip() or "unknown"
    value = re.sub(r'[<>:"/\\\\|?*]', "_", value)
    return value.rstrip(". ") or "unknown"


def version_modstorage_dir(version: str) -> Path:
    folder = MODSTORAGE_DIR / safe_version_folder_name(version)
    folder.mkdir(parents=True, exist_ok=True)
    return folder



def load_modref():
    """Load the launcher-wide mod metadata registry."""
    MODSTORAGE_DIR.mkdir(parents=True, exist_ok=True)

    data = _read_json(
        MODREF_FILE,
        {"mods": []}
    )

    mods = data.get("mods", [])
    if not isinstance(mods, list):
        mods = []

    clean = []
    for item in mods:
        if isinstance(item, dict):
            clean.append(dict(item))

    return {"mods": clean}


def save_modref(data):
    MODSTORAGE_DIR.mkdir(parents=True, exist_ok=True)
    mods = data.get("mods", []) if isinstance(data, dict) else []
    if not isinstance(mods, list):
        mods = []
    _write_json(
        MODREF_FILE,
        {"mods": mods}
    )


def modref_storage_key(installation_version, filename):
    return (
        safe_version_folder_name(installation_version)
        + "/"
        + Path(str(filename)).name
    )


def upsert_modref(entry):
    """
    Insert/update one mod record. Records are keyed by the version storage
    folder + JAR filename, since the same JAR name may exist for different
    Minecraft versions.
    """
    data = load_modref()
    mods = data["mods"]

    key = str(entry.get("storage_key", "")).strip()
    if not key:
        key = modref_storage_key(
            entry.get("installation_version", ""),
            entry.get("filename", "")
        )
        entry["storage_key"] = key

    replacement = dict(entry)

    for index, old in enumerate(mods):
        if str(old.get("storage_key", "")) == key:
            mods[index] = replacement
            save_modref(data)
            return replacement

    mods.append(replacement)
    save_modref(data)
    return replacement


def find_modref(installation_version, filename):
    """
    Prefer the exact modstorage/version record, but gracefully fall back to a
    filename match. This lets the UI retain a real Modrinth display name when
    an installation/version identifier was renamed or normalized differently.
    """
    key = modref_storage_key(
        installation_version,
        filename
    )

    mods = load_modref().get(
        "mods",
        []
    )

    for item in mods:
        if item.get(
            "storage_key"
        ) == key:
            return item

    filename_lower = Path(
        str(filename)
    ).name.casefold()

    matches = [
        item
        for item in mods
        if Path(
            str(
                item.get(
                    "filename",
                    ""
                )
            )
        ).name.casefold()
        == filename_lower
    ]

    if not matches:
        return None

    # Prefer richer Modrinth metadata over a generated local fallback.
    matches.sort(
        key=lambda item: (
            item.get(
                "source"
            ) == "modrinth",
            bool(
                item.get(
                    "display_name"
                )
            ),
        ),
        reverse=True
    )

    return matches[0]




def _fallback_mod_display_name(filename):
    """
    Best-effort display name for old/manual JARs that predate modref metadata.
    It deliberately preserves most of the filename instead of guessing too
    aggressively about which numeric suffix is a mod version.
    """
    stem = Path(str(filename)).stem
    value = stem.replace("_", " ").replace("-", " ")
    value = re.sub(r"\s+", " ", value).strip()
    return value or stem or "Unknown Mod"


def ensure_modref_for_storage():
    """
    Ensure every JAR already present in modstorage has at least a registry
    entry. Old/manual JARs cannot have trustworthy Modrinth metadata inferred,
    so unknown fields are left blank.
    """
    MODSTORAGE_DIR.mkdir(parents=True, exist_ok=True)
    data = load_modref()
    mods = data["mods"]
    known = {
        str(item.get("storage_key", ""))
        for item in mods
        if isinstance(item, dict)
    }
    changed = False

    for folder in MODSTORAGE_DIR.iterdir():
        if not folder.is_dir():
            continue

        installation_version = folder.name

        for jar in folder.glob("*.jar"):
            key = modref_storage_key(
                installation_version,
                jar.name
            )

            if key in known:
                continue

            mods.append({
                "storage_key": key,
                "display_name": _fallback_mod_display_name(jar.name),
                "filename": jar.name,
                "mod_version": "",
                "game_version": minecraft_game_version_from_installation_version(
                    installation_version
                ),
                "supported_game_versions": [],
                "modrinth_url": "",
                "project_id": "",
                "loader": loader_from_installation_version(
                    installation_version
                ) or "",
                "installation_version": installation_version,
                "source": "existing/local",
            })
            known.add(key)
            changed = True

    if changed:
        save_modref(data)

    return data


MINECRAFT_APP_REG_INFO = "https://help.minecraft.net/hc/en-us/articles/16254801392141"
OMNI_VERSION_DATA_URL = "https://raw.githubusercontent.com/Nixinova/Minecraft-Versions/main/data/java.yaml"
OMNI_INDEX_URL = "https://docs.google.com/spreadsheets/d/1OCxMNQLeZJi4BlKKwHx2OlzktKiLEwFXnmCrSdAFwYQ/htmlview"
OMNI_INDEX_JAVA_GID = "2126693093"
OMNI_INDEX_OTHER_GID = "804883379"
MOJANG_VERSION_MANIFEST_URL = "https://piston-meta.mojang.com/mc/game/version_manifest_v2.json"
OMNI_ARCHIVE_CLIENT_ROOT = "https://omniarchive.net/archive/java/client/"
VERSIONREF_SCHEMA_VERSION = 7

MODRINTH_API = "https://api.modrinth.com/v2"


def minecraft_game_version_from_installation_version(version: str) -> str:
    value = str(version).strip()

    # Loader installation IDs often contain both loader version and game
    # version. The final Minecraft-style numeric version is generally the one
    # we need for Modrinth filtering.
    matches = re.findall(r'(?<!\d)(\d+\.\d+(?:\.\d+)?)(?!\d)', value)

    if matches:
        return matches[-1]

    # Snapshot identifiers (e.g. 26w14a) can also be passed directly.
    snapshot = re.search(r'(\d{2}w\d{2}[a-z])', value, re.I)
    if snapshot:
        return snapshot.group(1)

    return value


def loader_from_installation_version(version: str):
    value = str(version).lower()

    if "neoforge" in value:
        return "neoforge"
    if "fabric" in value:
        return "fabric"
    if "quilt" in value:
        return "quilt"
    if "forge" in value:
        return "forge"

    return None


def modrinth_search(query: str, game_version: str, limit=20):
    facets = [
        ["project_type:mod"],
    ]

    if game_version:
        facets.append([f"versions:{game_version}"])

    response = requests.get(
        f"{MODRINTH_API}/search",
        params={
            "query": query,
            "limit": int(limit),
            "index": "relevance",
            "facets": json.dumps(facets),
        },
        timeout=20,
        headers={
            "User-Agent": "Supple-Launcher/0.1"
        }
    )
    response.raise_for_status()
    return response.json().get("hits", [])


def modrinth_project(project_id: str):
    response = requests.get(
        f"{MODRINTH_API}/project/{project_id}",
        timeout=20,
        headers={
            "User-Agent": "Supple-Launcher/0.1"
        }
    )
    response.raise_for_status()
    return response.json()


def modrinth_compatible_versions(project_id: str, game_version: str, loader=None):
    params = {
        "include_changelog": "false",
    }

    if game_version:
        params["game_versions"] = json.dumps([game_version])

    if loader:
        params["loaders"] = json.dumps([loader])

    response = requests.get(
        f"{MODRINTH_API}/project/{project_id}/version",
        params=params,
        timeout=20,
        headers={
            "User-Agent": "Supple-Launcher/0.1"
        }
    )
    response.raise_for_status()
    return response.json()


def download_modrinth_project(project_id: str, installation_version: str):
    game_version = minecraft_game_version_from_installation_version(
        installation_version
    )
    loader = loader_from_installation_version(
        installation_version
    )

    versions = modrinth_compatible_versions(
        project_id,
        game_version,
        loader
    )

    # If a custom/modloader installation name does not reveal the loader,
    # retry using only the Minecraft game version.
    if not versions and loader:
        versions = modrinth_compatible_versions(
            project_id,
            game_version,
            None
        )

    if not versions:
        raise RuntimeError(
            "Modrinth has no compatible file for this installation's "
            f"Minecraft version ({game_version})."
        )

    chosen = versions[0]

    try:
        project = modrinth_project(project_id)
    except Exception:
        project = {}

    files = chosen.get("files", [])

    if not files:
        raise RuntimeError(
            "The selected Modrinth version does not contain a downloadable file."
        )

    file_info = next(
        (item for item in files if item.get("primary")),
        files[0]
    )

    filename = Path(
        file_info.get("filename", "mod.jar")
    ).name
    url = file_info.get("url")

    if not url:
        raise RuntimeError(
            "Modrinth did not provide a download URL for this file."
        )

    target_dir = version_modstorage_dir(
        installation_version
    )
    target = target_dir / filename

    with requests.get(
        url,
        stream=True,
        timeout=60,
        headers={
            "User-Agent": "Supple-Launcher/0.1"
        }
    ) as response:
        response.raise_for_status()

        with target.open("wb") as handle:
            for chunk in response.iter_content(
                chunk_size=1024 * 256
            ):
                if chunk:
                    handle.write(chunk)

    slug = str(
        project.get("slug")
        or project_id
    ).strip()

    display_name = str(
        project.get("title")
        or project.get("name")
        or Path(filename).stem
    ).strip()

    modrinth_url = (
        f"https://modrinth.com/mod/{slug}"
        if slug
        else ""
    )

    metadata = {
        "storage_key": modref_storage_key(
            installation_version,
            filename
        ),
        "display_name": display_name,
        "filename": filename,
        "mod_version": str(
            chosen.get("version_number", "")
        ),
        "game_version": game_version,
        "supported_game_versions": list(
            chosen.get("game_versions", [])
            or []
        ),
        "modrinth_url": modrinth_url,
        "project_id": str(
            project.get("id")
            or project_id
        ),
        "loader": loader or "",
        "installation_version": installation_version,
        "source": "modrinth",
    }

    upsert_modref(metadata)

    return {
        "filename": filename,
        "path": str(target),
        "version_name": chosen.get("name", ""),
        "version_number": chosen.get("version_number", ""),
        "loader": loader,
        "display_name": display_name,
        "game_version": game_version,
        "modrinth_url": modrinth_url,
        "project_id": str(project.get("id") or project_id),
        "metadata": metadata,
    }



def local_launcher_java_profile_name(
    mc_dir: Path,
    email: str = "",
    xbox_xuid: str = ""
):
    """
    Best-effort display-only fallback to the official launcher's local profile
    cache.

    Matching is deliberately account-specific. SML will NOT reuse the only
    cached Java profile for an unrelated second Microsoft account.
    """
    candidates = [
        mc_dir / "launcher_accounts.json",
        mc_dir / "launcher_accounts_microsoft_store.json",
    ]

    wanted_email = str(email or "").strip().lower()
    wanted_xuid = str(xbox_xuid or "").strip()

    for path in candidates:
        if not path.is_file():
            continue

        try:
            data = json.loads(
                path.read_text(
                    encoding="utf-8",
                    errors="ignore"
                )
            )
        except Exception:
            continue

        accounts = data.get("accounts", {})
        if not isinstance(accounts, dict):
            continue

        for account in accounts.values():
            if not isinstance(account, dict):
                continue

            profile = account.get(
                "minecraftProfile",
                {}
            )

            if not isinstance(profile, dict):
                continue

            profile_name = str(
                profile.get("name", "")
            ).strip()

            if not profile_name:
                continue

            account_email = str(
                account.get("username")
                or account.get("email")
                or account.get("userName")
                or ""
            ).strip().lower()

            possible_ids = {
                str(account.get("xuid", "")).strip(),
                str(account.get("xboxUserId", "")).strip(),
                str(account.get("remoteId", "")).strip(),
                str(account.get("msaId", "")).strip(),
            }
            possible_ids.discard("")

            if (
                wanted_email
                and account_email
                and account_email == wanted_email
            ):
                return profile_name

            if (
                wanted_xuid
                and wanted_xuid in possible_ids
            ):
                return profile_name

    return ""


SML_MOD_MANIFEST = ".sml-managed.json"


def sync_installation_mods(mc_dir: Path, installation: dict):
    """
    Activate an installation's SML-managed mods in .minecraft/mods.

    The canonical JARs remain in modstorage/<version>/.
    Hard links are used when possible; copy is the fallback.
    """
    mods_dir = mc_dir / "mods"
    mods_dir.mkdir(parents=True, exist_ok=True)

    manifest_path = mods_dir / SML_MOD_MANIFEST
    previous = []

    if manifest_path.exists():
        try:
            data = json.loads(manifest_path.read_text(encoding="utf-8"))
            previous = data.get("files", [])
            if not isinstance(previous, list):
                previous = []
        except Exception:
            previous = []

    # Remove only mods SML placed on the previous launch.
    for filename in previous:
        target = mods_dir / Path(str(filename)).name
        if target.exists() or target.is_symlink():
            try:
                target.unlink()
            except Exception as exc:
                raise RuntimeError(
                    f"Could not remove the previous SML-managed mod:\\n{target}\\n\\n{exc}"
                )

    version = str(installation.get("version", ""))
    vanilla = bool(installation.get("vanilla", True))
    selected_mods = installation.get("mods", [])
    if not isinstance(selected_mods, list):
        selected_mods = []

    if vanilla:
        manifest_path.write_text(
            json.dumps({
                "installation": installation.get("name", ""),
                "version": version,
                "vanilla": True,
                "files": []
            }, indent=2),
            encoding="utf-8"
        )
        return

    storage = version_modstorage_dir(version)
    placed = []

    for raw_name in selected_mods:
        filename = Path(str(raw_name)).name
        if not filename:
            continue

        source = storage / filename
        if not source.is_file():
            raise RuntimeError(
                "This installation references a mod that is missing from modstorage:\\n\\n"
                f"{source}"
            )

        target = mods_dir / filename
        if target.exists():
            raise RuntimeError(
                "A non-SML file with the same name already exists in .minecraft\\\\mods:\\n\\n"
                f"{target}\\n\\n"
                "Move or remove that conflicting file before launching."
            )

        try:
            os.link(source, target)
            method = "hardlink"
        except Exception:
            shutil.copy2(source, target)
            method = "copy"

        placed.append(filename)
        log(
            f"Activated {filename} for installation "
            f"{installation.get('name', '')} via {method}"
        )

    manifest_path.write_text(
        json.dumps({
            "installation": installation.get("name", ""),
            "version": version,
            "vanilla": False,
            "files": placed
        }, indent=2),
        encoding="utf-8"
    )


def powershell(script: str) -> str:
    cp = subprocess.run(
        ["powershell.exe", "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", script],
        capture_output=True,
        text=True,
        creationflags=CREATE_NO_WINDOW,
        timeout=25,
    )
    if cp.returncode != 0:
        raise RuntimeError(cp.stderr.strip() or "PowerShell command failed.")
    return cp.stdout


# -------------------------- Microsoft authentication --------------------------

class AuthManager:
    def __init__(self, config):
        self.config = config
        self.cache = msal.SerializableTokenCache()
        self._load_cache()

    def _load_cache(self):
        if CACHE_FILE.exists():
            try:
                raw = dpapi_decrypt(CACHE_FILE.read_bytes())
                self.cache.deserialize(raw.decode("utf-8"))
            except Exception as e:
                log(f"Token cache load failed: {e}")

    def save_cache(self):
        if self.cache.has_state_changed:
            ensure_local_storage()
            CACHE_FILE.write_bytes(
                dpapi_encrypt(self.cache.serialize().encode("utf-8"))
            )

    def app(self):
        client_id = self.config.get("client_id", "").strip()

        if not client_id:
            raise RuntimeError(
                "No Microsoft application Client ID is configured.\n\n"
                "Open Settings and enter your own Microsoft Entra public-client Application ID."
            )

        if client_id in LEGACY_MINECRAFT_CLIENT_IDS:
            raise RuntimeError(
                "The Client ID 00000000402b5328 is no longer accepted by Microsoft "
                "for this sign-in flow.\n\n"
                "Create your own Microsoft Entra public-client application and enter "
                "its Application (client) ID in Settings."
            )

        return msal.PublicClientApplication(
            client_id=client_id,
            authority=AUTHORITY,
            token_cache=self.cache,
        )

    def accounts(self):
        try:
            return self.app().get_accounts()
        except Exception:
            return []

    def add_account_device_flow(self, callback):
        """
        callback(stage, payload)
          stage='code': payload has message/user_code/verification_uri
          stage='done': payload is token result
          stage='error': payload is str
        """
        def worker():
            try:
                app = self.app()
                flow = app.initiate_device_flow(scopes=SCOPES)
                if "user_code" not in flow:
                    raise RuntimeError(flow.get("error_description") or str(flow))
                callback("code", flow)
                result = app.acquire_token_by_device_flow(flow)
                self.save_cache()
                if "access_token" not in result:
                    raise RuntimeError(result.get("error_description") or str(result))
                callback("done", result)
            except Exception as e:
                callback("error", str(e))

        threading.Thread(target=worker, daemon=True).start()

    def microsoft_token_for_account(self, home_account_id):
        app = self.app()
        accounts = [a for a in app.get_accounts()
                    if a.get("home_account_id") == home_account_id]
        if not accounts:
            raise RuntimeError("That Microsoft account is no longer in the local token cache.")
        result = app.acquire_token_silent(SCOPES, account=accounts[0])
        self.save_cache()
        if not result or "access_token" not in result:
            raise RuntimeError(
                "The saved sign-in can no longer be refreshed. Remove and re-add this account."
            )
        return result["access_token"], accounts[0]

    def remove_account(self, home_account_id):
        app = self.app()
        for account in app.get_accounts():
            if account.get("home_account_id") == home_account_id:
                app.remove_account(account)
        self.save_cache()

    def xbox_identity(self, home_account_id):
        """
        Return the Xbox identity attached to a cached Microsoft account.

        This is separate from Minecraft Services, so the gamertag can still be
        shown even if the launcher Client ID is not currently accepted by the
        Minecraft Services login endpoint.
        """
        ms_token, account = self.microsoft_token_for_account(
            home_account_id
        )

        # Microsoft -> Xbox user token
        response = requests.post(
            XBL_AUTH,
            json={
                "Properties": {
                    "AuthMethod": "RPS",
                    "SiteName": "user.auth.xboxlive.com",
                    "RpsTicket": "d=" + ms_token,
                },
                "RelyingParty": "http://auth.xboxlive.com",
                "TokenType": "JWT",
            },
            headers={
                "Accept": "application/json",
                "Content-Type": "application/json",
                "x-xbl-contract-version": "1",
            },
            timeout=20,
        )

        if not response.ok:
            raise RuntimeError(
                f"Xbox Live authentication failed "
                f"({response.status_code}): {response.text[:500]}"
            )

        user_data = response.json()
        user_token = user_data["Token"]

        # General Xbox XSTS token. This response normally includes gamertag
        # and XUID display claims.
        response = requests.post(
            XSTS_AUTH,
            json={
                "Properties": {
                    "SandboxId": "RETAIL",
                    "UserTokens": [user_token],
                },
                "RelyingParty": "http://xboxlive.com",
                "TokenType": "JWT",
            },
            headers={
                "Accept": "application/json",
                "Content-Type": "application/json",
                "x-xbl-contract-version": "1",
            },
            timeout=20,
        )

        if not response.ok:
            raise RuntimeError(
                f"Xbox identity lookup failed "
                f"({response.status_code}): {response.text[:500]}"
            )

        xsts = response.json()
        xui = (
            xsts.get("DisplayClaims", {})
            .get("xui", [{}])[0]
        )

        gamertag = (
            xui.get("mgt")
            or xui.get("gtg")
            or xui.get("umg")
            or ""
        )

        return {
            "gamertag": gamertag,
            "xuid": xui.get("xid", ""),
            "user_hash": xui.get("uhs", ""),
            "ms_account": account,
        }

    def minecraft_session(self, home_account_id):
        ms_token, account = self.microsoft_token_for_account(home_account_id)

        # First try minecraft-launcher-lib when available. This intentionally
        # starts with the SAME Microsoft access token obtained for Supple's
        # configured Client ID. That makes it a useful implementation test:
        # if this path succeeds while the native path fails, our request chain
        # is at fault; if both are rejected as an invalid app registration,
        # the Client ID is the blocker rather than Supple's request code.
        if minecraft_launcher_lib is not None:
            try:
                microsoft_account = minecraft_launcher_lib.microsoft_account

                xbl = microsoft_account.authenticate_with_xbl(
                    ms_token
                )

                if not isinstance(xbl, dict) or not xbl.get("Token"):
                    raise RuntimeError(
                        "minecraft-launcher-lib Xbox authentication returned "
                        + str(xbl)[:800]
                    )

                xui = (
                    xbl.get("DisplayClaims", {})
                    .get("xui", [{}])[0]
                )
                uhs = xui.get("uhs", "")
                xuid = xui.get("xid", "")

                if not uhs:
                    raise RuntimeError(
                        "minecraft-launcher-lib Xbox authentication did not "
                        "return a user hash."
                    )

                xsts = microsoft_account.authenticate_with_xsts(
                    xbl["Token"]
                )

                if not isinstance(xsts, dict) or not xsts.get("Token"):
                    raise RuntimeError(
                        "minecraft-launcher-lib XSTS authentication returned "
                        + str(xsts)[:800]
                    )

                mc = microsoft_account.authenticate_with_minecraft(
                    uhs,
                    xsts["Token"]
                )

                if not isinstance(mc, dict) or not mc.get("access_token"):
                    detail = str(mc)[:1000]
                    raise RuntimeError(
                        "minecraft-launcher-lib Minecraft authentication "
                        "did not return an access token: "
                        + detail
                    )

                mc_token = mc["access_token"]
                profile = microsoft_account.get_profile(
                    mc_token
                )

                if (
                    not isinstance(profile, dict)
                    or not profile.get("id")
                    or not profile.get("name")
                ):
                    raise RuntimeError(
                        "minecraft-launcher-lib profile request returned "
                        + str(profile)[:1000]
                    )

                log(
                    "Minecraft Java profile resolved through "
                    "minecraft-launcher-lib for "
                    + str(profile.get("name", ""))
                )

                return {
                    "ms_account": account,
                    "access_token": mc_token,
                    "uuid": profile.get("id", ""),
                    "name": profile.get("name", "Player"),
                    "xuid": xuid,
                    "auth_source": "minecraft-launcher-lib",
                }

            except Exception as exc:
                # Keep the native path as a fallback so installing the test
                # library cannot make authentication less reliable. The exact
                # failure is written to launcher.log for comparison.
                log(
                    "minecraft-launcher-lib authentication failed: "
                    + repr(exc)
                )
        else:
            log(
                "minecraft-launcher-lib is not installed; using Supple's "
                "native Minecraft authentication path. Install with: "
                "py -m pip install minecraft-launcher-lib"
            )

        # Microsoft -> Xbox Live
        r = requests.post(
            XBL_AUTH,
            json={
                "Properties": {
                    "AuthMethod": "RPS",
                    "SiteName": "user.auth.xboxlive.com",
                    "RpsTicket": "d=" + ms_token,
                },
                "RelyingParty": "http://auth.xboxlive.com",
                "TokenType": "JWT",
            },
            headers={"Accept": "application/json", "Content-Type": "application/json"},
            timeout=20,
        )
        if not r.ok:
            raise RuntimeError(f"Xbox Live authentication failed ({r.status_code}): {r.text[:500]}")
        xbl = r.json()
        xbl_token = xbl["Token"]

        # Xbox Live -> XSTS for Minecraft Services
        r = requests.post(
            XSTS_AUTH,
            json={
                "Properties": {
                    "SandboxId": "RETAIL",
                    "UserTokens": [xbl_token],
                },
                "RelyingParty": "rp://api.minecraftservices.com/",
                "TokenType": "JWT",
            },
            headers={"Accept": "application/json", "Content-Type": "application/json"},
            timeout=20,
        )
        if not r.ok:
            msg = r.text[:800]
            if r.status_code == 401:
                msg += (
                    "\n\nXSTS can also reject child accounts, accounts without an Xbox profile, "
                    "or accounts whose Xbox privacy/family settings block access."
                )
            raise RuntimeError(f"XSTS authentication failed ({r.status_code}): {msg}")
        xsts = r.json()
        xsts_token = xsts["Token"]
        xui = xsts.get("DisplayClaims", {}).get("xui", [{}])[0]
        uhs = xui.get("uhs", "")
        xuid = xui.get("xid", "")

        # XSTS -> Minecraft access token
        r = requests.post(
            MC_LOGIN,
            json={"identityToken": f"XBL3.0 x={uhs};{xsts_token}"},
            headers={"Accept": "application/json", "Content-Type": "application/json"},
            timeout=20,
        )
        if not r.ok:
            msg = r.text[:800]
            if r.status_code == 403 and "Invalid app registration" in r.text:
                msg += (
                    "\n\nMicrosoft and Xbox authentication succeeded, but Minecraft "
                    "Services rejected this launcher's Client ID. This is not an Entra "
                    "configuration error; the Client ID is not authorized for Minecraft "
                    "Services.\n\nMinecraft App Registration Info: "
                    + MINECRAFT_APP_REG_INFO
                )
            raise RuntimeError(f"Minecraft Services login failed ({r.status_code}): {msg}")
        mc = r.json()
        mc_token = mc["access_token"]

        # Profile is a practical ownership/profile check for Java.
        r = requests.get(
            MC_PROFILE,
            headers={"Authorization": "Bearer " + mc_token},
            timeout=20,
        )
        if r.status_code in (404, 403):
            raise RuntimeError(
                "This Microsoft account did not return a Minecraft: Java Edition profile. "
                "It may not own Java Edition, or Minecraft Services access may be unavailable."
            )
        if not r.ok:
            raise RuntimeError(f"Minecraft profile request failed ({r.status_code}): {r.text[:500]}")
        profile = r.json()

        return {
            "ms_account": account,
            "access_token": mc_token,
            "uuid": profile.get("id", ""),
            "name": profile.get("name", "Player"),
            "xuid": xuid,
        }


# ------------------------------ Java launcher ------------------------------


def _version_loader_source(version_id: str):
    lower = str(version_id).lower()

    if "neoforge" in lower:
        return "NeoForge"
    if "fabric" in lower:
        return "Fabric"
    if "quilt" in lower:
        return "Quilt"
    if "forge" in lower:
        return "Forge"

    return ""


def _version_category(version_id: str) -> str:
    value = str(version_id).strip()
    lower = value.lower()

    if _version_loader_source(value):
        return "Mod Loaders"

    if re.match(r"^a\d", lower):
        return "Alpha"

    if re.match(r"^b\d", lower):
        return "Beta"

    if (
        re.match(r"^c\d", lower)
        or "classic" in lower
    ):
        return "Classic"

    if re.fullmatch(r"\d+(?:\.\d+){0,3}", value):
        return "Releases"

    if (
        re.search(r"(?:^|[-_])rc[-_]?\d+", lower)
        or "release candidate" in lower
    ):
        return "Release Candidates"

    if (
        re.search(r"(?:^|[-_])pre[-_]?\d+", lower)
        or "pre-release" in lower
        or "prerelease" in lower
    ):
        return "Pre-Releases"

    if re.fullmatch(r"\d{2}w\d{2}[a-z]", lower):
        return "Snapshots"

    return "Misc"





def _historical_display_id(version_id: str, phase: str) -> str:
    """
    Display old Java versions using the conventional Omniarchive/Minecraft
    phase prefix while keeping the internal/catalog ID untouched.
    """
    value = str(version_id).strip()
    phase = str(phase or "").strip()

    lower = value.lower()

    if phase == "Alpha":
        return value if lower.startswith("a") else f"a{value}"

    if phase == "Beta":
        return value if lower.startswith("b") else f"b{value}"

    if phase == "Classic":
        return value if lower.startswith("c") else f"c{value}"

    if phase == "Indev":
        if lower.startswith(("in-", "indev-")):
            return value
        return f"in-{value}"

    if phase == "Infdev":
        if lower.startswith(("inf-", "infdev-")):
            return value
        return f"inf-{value}"

    return value


def _historical_aliases(version_id: str, phase: str):
    raw = str(version_id).strip()
    display = _historical_display_id(
        raw,
        phase
    )

    aliases = {
        raw,
        display,
    }

    # A few launchers/archives use longer textual phase prefixes.
    if phase == "Indev":
        aliases.add(
            f"indev-{raw}"
        )
    elif phase == "Infdev":
        aliases.add(
            f"infdev-{raw}"
        )

    return {
        alias
        for alias in aliases
        if alias
    }



def _version_date_display(
    value: str,
    date_format="MM/DD/YYYY"
) -> str:
    value = str(value or "").strip()

    if not value:
        return "Unknown"

    try:
        parsed = datetime.strptime(
            value[:10],
            "%Y-%m-%d"
        )
    except Exception:
        return value

    choices = {
        "MM/DD/YYYY": (
            parsed.month,
            parsed.day,
            parsed.year,
            "/"
        ),
        "DD/MM/YYYY": (
            parsed.day,
            parsed.month,
            parsed.year,
            "/"
        ),
        "YYYY/MM/DD": (
            parsed.year,
            parsed.month,
            parsed.day,
            "/"
        ),
        "MM-DD-YYYY": (
            parsed.month,
            parsed.day,
            parsed.year,
            "-"
        ),
        "DD-MM-YYYY": (
            parsed.day,
            parsed.month,
            parsed.year,
            "-"
        ),
        "YYYY-MM-DD": (
            parsed.year,
            parsed.month,
            parsed.day,
            "-"
        ),
    }

    first, second, third, sep = choices.get(
        date_format,
        choices["MM/DD/YYYY"]
    )

    return (
        f"{first}{sep}"
        f"{second}{sep}"
        f"{third}"
    )




def _version_sort_key(item):
    date = str(
        item.get("release_date", "")
        or ""
    ).strip()

    installed = bool(
        item.get("installed")
    )

    # Installed custom/modloader versions with no catalog date stay above
    # the historical catalog so the user's usable local versions are easy
    # to find. Dated versions are newest-first.
    if not date:
        return (
            1 if installed else -1,
            "",
            str(item.get("id", "")).casefold()
        )

    return (
        0,
        date,
        str(item.get("id", "")).casefold()
    )


def _parse_omniarchive_derived_java_yaml(raw: str):
    """
    Parse the Omniarchive-derived Java dataset using its actual phase headings.

    Internal IDs remain unchanged for matching. display_id is what the launcher
    shows to the user, e.g. a1.1.1, b1.7, c0.30, in-20100125, inf-20100630.
    """
    by_id = {}

    current_major = ""
    current_minor = ""

    line_re = re.compile(
        r"^\s*-\s*\['([^']+)',\s*Java,\s*([^,]+),\s*.*?"
        r"\[\{.*?date:\s*([0-9]{4}-[0-9]{2}-[0-9]{2}|~)"
    )

    for raw_line in str(raw).splitlines():
        line = raw_line.strip()

        if line.startswith("## "):
            current_major = line[3:].strip()
            current_minor = ""
            continue

        if line.startswith("### "):
            current_minor = line[4:].strip()
            continue

        match = line_re.search(
            raw_line
        )

        if not match:
            continue

        version_id = match.group(1).strip()
        row_phase = match.group(2).strip()
        raw_date = match.group(3).strip()

        if not version_id:
            continue

        phase = (
            current_major
            or row_phase
        )

        release_date = (
            ""
            if raw_date == "~"
            else raw_date
        )

        if phase == "Beta":
            category = "Beta"

        elif phase in (
            "Alpha",
            "Indev",
            "Infdev",
        ):
            # Indev/Infdev belong under the Alpha checkbox per launcher UX.
            category = "Alpha"

        elif phase in (
            "Classic",
            "Pre-Classic",
        ):
            category = "Classic"

        elif phase == "Release":
            if current_minor == "Full versions":
                category = "Releases"

            elif current_minor == "Pres":
                lower = version_id.lower()

                if (
                    "rc" in lower
                    or "release candidate" in lower
                ):
                    category = "Release Candidates"
                else:
                    category = "Pre-Releases"

            elif current_minor == "Snapshots":
                category = "Snapshots"

            else:
                category = "Misc"

        else:
            category = _version_category(
                version_id
            )

        display_id = _historical_display_id(
            version_id,
            phase
        )

        aliases = sorted(
            _historical_aliases(
                version_id,
                phase
            )
        )

        if version_id in by_id:
            item = by_id[
                version_id
            ]

            if (
                not item.get(
                    "release_date"
                )
                and release_date
            ):
                item[
                    "release_date"
                ] = release_date

            if (
                item.get(
                    "category"
                )
                == "Misc"
                and category != "Misc"
            ):
                item[
                    "category"
                ] = category

            continue

        by_id[
            version_id
        ] = {
            "id": version_id,
            "display_id": display_id,
            "aliases": aliases,
            "phase": phase,
            "release_date": release_date,
            "category": category,
            "installed": False,
            "catalogued": True,
            "download_available": True,
            "source": "Omniarchive index",
        }

    return list(
        by_id.values()
    )




def _local_version_release_date(mc_dir: Path, version_id: str) -> str:
    path = (
        mc_dir
        / "versions"
        / version_id
        / f"{version_id}.json"
    )

    if not path.exists():
        return ""

    try:
        data = json.loads(
            path.read_text(
                encoding="utf-8"
            )
        )
    except Exception:
        return ""

    for key in (
        "releaseTime",
        "time",
    ):
        value = str(
            data.get(key, "")
            or ""
        ).strip()

        match = re.match(
            r"(\d{4}-\d{2}-\d{2})",
            value
        )

        if match:
            return match.group(1)

    return ""



def _archive_filename_to_version(filename: str) -> str:
    name = str(filename).strip().split("/")[-1]

    for suffix in (
        ".jar",
        ".zip",
        ".exe",
    ):
        if name.lower().endswith(suffix):
            name = name[:-len(suffix)]
            break

    name = re.sub(
        r"-launcher$",
        "",
        name,
        flags=re.I
    )

    return name


def _omniarchive_listing_entries(html: str):
    hrefs = re.findall(
        r'href=["\']([^"\']+)["\']',
        str(html),
        flags=re.I
    )

    files = set()
    folders = []

    for href in hrefs:
        clean = (
            href.split("?")[0]
            .split("#")[0]
        )

        if not clean or clean in (
            "../",
            "/",
        ):
            continue

        lower = clean.lower()

        # Omniarchive archive pages use absolute vault.omniarchive.uk/.net
        # links for the actual JAR files. These must NOT be discarded.
        if lower.startswith(
            ("http://", "https://")
        ):
            if (
                "vault.omniarchive." in lower
                and lower.endswith(
                    (
                        ".jar",
                        ".zip",
                        ".exe",
                    )
                )
            ):
                files.add(
                    _archive_filename_to_version(
                        clean
                    )
                )
            continue

        if clean.endswith("/"):
            folders.append(
                clean.strip("/")
            )
            continue

        if lower.endswith(
            (
                ".jar",
                ".zip",
                ".exe",
            )
        ):
            files.add(
                _archive_filename_to_version(
                    clean
                )
            )

    return files, folders




class _OmniIndexHTMLParser(HTMLParser):
    """Small dependency-free reader for Google Sheets' published HTML view."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.rows = []
        self._row = None
        self._cell = None

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == "tr":
            self._row = []
        elif tag in ("td", "th") and self._row is not None:
            self._cell = {
                "text": [],
                "class": attrs.get("class", ""),
                "style": attrs.get("style", ""),
                "hrefs": [],
            }
        elif tag == "a" and self._cell is not None:
            href = str(attrs.get("href", "") or "").strip()
            if href:
                self._cell["hrefs"].append(href)

    def handle_data(self, data):
        if self._cell is not None:
            self._cell["text"].append(data)

    def handle_endtag(self, tag):
        if tag in ("td", "th") and self._cell is not None:
            self._cell["text"] = " ".join(
                "".join(self._cell["text"]).split()
            )
            self._row.append(self._cell)
            self._cell = None
        elif tag == "tr" and self._row is not None:
            if self._row:
                self.rows.append(self._row)
            self._row = None


def _omni_index_style_colors(html):
    """Return {css_class: '#rrggbb'} for published Google Sheet cells."""
    colors = {}
    for match in re.finditer(
        r"\.([A-Za-z0-9_-]+)\s*\{([^{}]*)\}",
        str(html),
        flags=re.S,
    ):
        body = match.group(2)
        color_match = re.search(
            r"background(?:-color)?\s*:\s*(#[0-9a-fA-F]{6})",
            body,
            flags=re.I,
        )
        if color_match:
            colors[match.group(1)] = color_match.group(1).lower()
    return colors


def _omni_index_cell_color(cell, class_colors):
    inline = re.search(
        r"background(?:-color)?\s*:\s*(#[0-9a-fA-F]{6})",
        str(cell.get("style", "")),
        flags=re.I,
    )
    if inline:
        return inline.group(1).lower()

    for class_name in str(cell.get("class", "")).split():
        color = class_colors.get(class_name)
        if color:
            return color
    return ""


def _omni_index_color_state(color):
    """Interpret the index's found/unfound cell colouring conservatively."""
    value = str(color or "").lstrip("#")
    if len(value) != 6:
        return None
    try:
        r, g, b = (int(value[i:i + 2], 16) for i in (0, 2, 4))
    except ValueError:
        return None

    # Red/pink cells in the Omniarchive index mean a confirmed version whose
    # client has not been found. Green/cyan/blue variants represent found
    # material (including modified/alternate copies). Ignore neutral greys.
    if r >= g + 35 and r >= b + 20 and r >= 110:
        return False
    if (g >= r + 20 and g >= 90) or (b >= r + 25 and b >= 105):
        return True
    return None


def _omni_index_version_tokens(text):
    value = str(text or "").strip()
    if not value:
        return set()

    out = {value}
    # Published sheets sometimes show a display ID and an internal ID in the
    # same cell. Split only on harmless separators; aliases handle prefixes.
    for token in re.split(r"[\s,;/()]+", value):
        token = token.strip()
        if token and re.search(r"\d", token) and not re.fullmatch(r"\d{4}-\d{2}-\d{2}", token):
            out.add(token)
    return out


def fetch_omniarchive_index_archived_versions():
    """Read archive availability from the Omniarchive index itself.

    The public index is the authority for whether a historical client is
    known/archived.  Vault directory crawling remains a useful fallback, but
    it cannot see every location represented by the index.
    """
    archived = set()

    for gid in (OMNI_INDEX_JAVA_GID, OMNI_INDEX_OTHER_GID):
        url = f"{OMNI_INDEX_URL}?gid={gid}"
        response = requests.get(
            url,
            timeout=30,
            headers={"User-Agent": "Supple-Launcher/0.1"},
        )
        response.raise_for_status()
        html = response.text

        parser = _OmniIndexHTMLParser()
        parser.feed(html)
        class_colors = _omni_index_style_colors(html)

        header = []
        header_row_index = -1
        for row_index, row in enumerate(parser.rows[:80]):
            texts = [str(cell.get("text", "")).strip().casefold() for cell in row]
            if any("version" in text or text == "id" for text in texts):
                header = texts
                header_row_index = row_index
                break

        client_columns = [
            i for i, name in enumerate(header)
            if "client" in name or "download" in name or "archive" in name
        ]
        version_columns = [
            i for i, name in enumerate(header)
            if name == "id" or "version" in name
        ]

        rows = parser.rows[header_row_index + 1:] if header_row_index >= 0 else parser.rows
        for row in rows:
            if not row:
                continue

            candidate_cells = []
            if version_columns:
                candidate_cells.extend(
                    row[i] for i in version_columns if i < len(row)
                )
            else:
                candidate_cells.extend(row[:3])

            version_tokens = set()
            for cell in candidate_cells:
                version_tokens.update(_omni_index_version_tokens(cell.get("text", "")))

            version_tokens = {
                token for token in version_tokens
                if re.search(r"\d", token)
                and len(token) <= 80
                and not re.fullmatch(r"\d{4}-\d{2}-\d{2}", token)
            }
            if not version_tokens:
                continue

            status_cells = [row[i] for i in client_columns if i < len(row)]
            if not status_cells:
                status_cells = candidate_cells

            state = None
            # Explicit wording wins over colour.
            status_text = " ".join(
                str(cell.get("text", "") or "") for cell in status_cells
            ).casefold()
            if any(phrase in status_text for phrase in (
                "not archived", "not found", "missing", "lost",
            )):
                state = False
            elif any(phrase in status_text for phrase in (
                "archived", "found", "available",
            )):
                state = True

            # A direct client/archive link is a strong found signal.
            if state is None:
                for cell in status_cells:
                    for href in cell.get("hrefs", []):
                        low = str(href).casefold()
                        if any(key in low for key in (
                            "omniarchive", "archive.org", "minecraft.net",
                            ".jar", ".zip", ".exe",
                        )):
                            state = True
                            break
                    if state is not None:
                        break

            # Finally use the sheet's found/unfound cell colour.
            if state is None:
                for cell in status_cells:
                    color_state = _omni_index_color_state(
                        _omni_index_cell_color(cell, class_colors)
                    )
                    if color_state is not None:
                        state = color_state
                        break

            if state is True:
                archived.update(version_tokens)

    return archived


def fetch_omniarchive_client_versions():
    """Read Omniarchive's Vault directory listings as a fallback source."""
    archived = set()

    def fetch(url):
        response = requests.get(
            url,
            timeout=20,
            headers={
                "User-Agent": "Supple-Launcher/0.1"
            }
        )
        response.raise_for_status()
        return response.text

    for section in (
        "pre-classic",
        "classic",
        "indev",
        "infdev",
        "alpha",
        "beta",
    ):
        try:
            html = fetch(
                OMNI_ARCHIVE_CLIENT_ROOT
                + section
                + "/"
            )
            files, _ = _omniarchive_listing_entries(
                html
            )
            archived.update(
                files
            )
        except Exception:
            pass

    # Release builds and their prereleases/snapshots are grouped by version.
    try:
        release_root = (
            OMNI_ARCHIVE_CLIENT_ROOT
            + "release/"
        )
        html = fetch(
            release_root
        )
        root_files, folders = _omniarchive_listing_entries(
            html
        )
        archived.update(
            root_files
        )

        for folder in folders:
            if folder in (
                ".",
                "..",
            ):
                continue

            try:
                sub_html = fetch(
                    release_root
                    + folder
                    + "/"
                )
                sub_files, _ = _omniarchive_listing_entries(
                    sub_html
                )
                archived.update(
                    sub_files
                )
            except Exception:
                pass
    except Exception:
        pass

    return archived


def _omniarchive_matches_version(
    version_id,
    archived_versions,
    aliases=None
):
    candidates = {
        str(
            version_id
        ).strip()
    }

    for alias in (
        aliases
        or []
    ):
        candidates.add(
            str(alias).strip()
        )

    candidates = {
        value.casefold()
        for value in candidates
        if value
    }

    for archived in archived_versions:
        archived_lower = str(
            archived
        ).strip().casefold()

        for candidate in candidates:
            if archived_lower == candidate:
                return True

            # Rediscovered historical files often append timestamps/build IDs:
            # 13w03a-1613, 1.5-pre-071309, etc.
            if archived_lower.startswith(
                candidate + "-"
            ):
                return True

            if archived_lower.startswith(
                candidate + "_"
            ):
                return True

            # Some archive names include an r prefix for release builds.
            if archived_lower == (
                "r" + candidate
            ):
                return True

            if archived_lower.startswith(
                "r" + candidate + "-"
            ):
                return True

    return False




def fetch_mojang_version_catalog():
    response = requests.get(
        MOJANG_VERSION_MANIFEST_URL,
        timeout=25,
        headers={
            "User-Agent": "Supple-Launcher/0.1"
        }
    )
    response.raise_for_status()

    payload = response.json()
    result = {}

    for item in payload.get(
        "versions",
        []
    ):
        version_id = str(
            item.get(
                "id",
                ""
            )
        ).strip()

        if not version_id:
            continue

        release_time = str(
            item.get(
                "releaseTime",
                ""
            )
            or ""
        )

        match = re.match(
            r"(\d{4}-\d{2}-\d{2})",
            release_time
        )

        result[version_id] = {
            "release_date": (
                match.group(1)
                if match
                else ""
            ),
            "type": str(
                item.get(
                    "type",
                    ""
                )
            ),
            "url": str(
                item.get(
                    "url",
                    ""
                )
            ),
        }

    latest = payload.get(
        "latest",
        {}
    )

    result["_latest"] = {
        "release": str(
            latest.get(
                "release",
                ""
            )
            or ""
        ),
        "snapshot": str(
            latest.get(
                "snapshot",
                ""
            )
            or ""
        ),
    }

    return result




def apply_version_sources(
    catalog,
    mojang_catalog,
    omni_archived
):
    for item in catalog:
        version_id = str(
            item.get(
                "id",
                ""
            )
        )

        loader = _version_loader_source(
            version_id
        )

        if loader:
            item["source"] = loader
            item["archived"] = True
            item["download_available"] = bool(
                item.get(
                    "installed"
                )
            )
            item["category"] = (
                "Mod Loaders"
            )
            continue

        if version_id in mojang_catalog:
            meta = mojang_catalog[
                version_id
            ]
            item["source"] = "Mojang"
            item["archived"] = True
            item["download_available"] = True

            if not item.get(
                "release_date"
            ):
                item["release_date"] = (
                    meta.get(
                        "release_date",
                        ""
                    )
                )
            continue

        if _omniarchive_matches_version(
            version_id,
            omni_archived,
            aliases=item.get(
                "aliases",
                []
            )
        ):
            item["source"] = (
                "Omniarchive"
            )
            item["archived"] = True
            item["download_available"] = True
            continue

        # The source column describes where the catalog record came from.
        # Archive availability is represented separately by `archived` and the
        # red label; "Unarchived" is a state, not a source.
        item["source"] = str(item.get("source", "") or "Omniarchive")
        if item["source"] == "Omniarchive index":
            item["source"] = "Omniarchive"
        item["archived"] = False
        item["download_available"] = False

    return catalog



def load_versionref():
    data = _read_json(
        VERSIONREF_FILE,
        {}
    )

    if not isinstance(
        data,
        dict
    ):
        data = {}

    versions = data.get(
        "versions",
        []
    )

    if not isinstance(
        versions,
        list
    ):
        versions = []

    return {
        "schema_version": int(
            data.get(
                "schema_version",
                0
            )
            or 0
        ),
        "catalog_fetched": bool(
            data.get(
                "catalog_fetched",
                False
            )
        ),
        "fetched_at": str(
            data.get(
                "fetched_at",
                ""
            )
            or ""
        ),
        "source": str(
            data.get(
                "source",
                ""
            )
            or ""
        ),
        "source_url": str(
            data.get(
                "source_url",
                ""
            )
            or ""
        ),
        "mirror_url": str(
            data.get(
                "mirror_url",
                ""
            )
            or ""
        ),
        "mojang_latest": (
            dict(
                data.get(
                    "mojang_latest",
                    {}
                )
            )
            if isinstance(
                data.get(
                    "mojang_latest",
                    {}
                ),
                dict
            )
            else {}
        ),
        "versions": [
            dict(item)
            for item in versions
            if isinstance(item, dict)
        ],
    }


def save_versionref(data):
    versions = data.get(
        "versions",
        []
    )

    if not isinstance(
        versions,
        list
    ):
        versions = []

    # Stable newest-first JSON ordering for readability.
    dated = sorted(
        versions,
        key=lambda item: (
            str(
                item.get(
                    "release_date",
                    ""
                )
                or ""
            ),
            str(
                item.get(
                    "id",
                    ""
                )
            ).casefold()
        ),
        reverse=True
    )

    _write_json(
        VERSIONREF_FILE,
        {
            "schema_version": int(
                data.get(
                    "schema_version",
                    VERSIONREF_SCHEMA_VERSION
                )
            ),
            "catalog_fetched": bool(
                data.get(
                    "catalog_fetched",
                    False
                )
            ),
            "fetched_at": str(
                data.get(
                    "fetched_at",
                    ""
                )
                or ""
            ),
            "source": str(
                data.get(
                    "source",
                    ""
                )
                or ""
            ),
            "source_url": str(
                data.get(
                    "source_url",
                    ""
                )
                or ""
            ),
            "mirror_url": str(
                data.get(
                    "mirror_url",
                    ""
                )
                or ""
            ),
            "mojang_latest": (
                dict(
                    data.get(
                        "mojang_latest",
                        {}
                    )
                )
                if isinstance(
                    data.get(
                        "mojang_latest",
                        {}
                    ),
                    dict
                )
                else {}
            ),
            "versions": dated,
        }
    )


def update_versionref_installed_state(
    mc_dir: Path,
    installed_versions
):
    """
    Refresh only the local-installed state on every run.

    Catalog dates are never re-downloaded once catalog_fetched is true.
    """
    installed_versions = {
        str(value)
        for value in installed_versions
    }

    data = load_versionref()
    versions = data["versions"]

    by_id = {
        str(item.get("id", "")): item
        for item in versions
        if item.get("id")
    }

    for item in versions:
        aliases = set(
            item.get(
                "aliases",
                []
            )
            if isinstance(
                item.get(
                    "aliases",
                    []
                ),
                list
            )
            else []
        )

        aliases.add(
            str(
                item.get(
                    "id",
                    ""
                )
            )
        )
        aliases.add(
            str(
                item.get(
                    "display_id",
                    ""
                )
            )
        )

        item["installed"] = bool(
            aliases
            & installed_versions
        )

    known_aliases = set()

    for item in versions:
        known_aliases.add(
            str(
                item.get(
                    "id",
                    ""
                )
            )
        )
        known_aliases.add(
            str(
                item.get(
                    "display_id",
                    ""
                )
            )
        )

        for alias in item.get(
            "aliases",
            []
        ) if isinstance(
            item.get(
                "aliases",
                []
            ),
            list
        ) else []:
            known_aliases.add(
                str(alias)
            )

    for version_id in sorted(
        installed_versions,
        key=str.casefold
    ):
        if version_id in known_aliases:
            continue

        versions.append({
            "id": version_id,
            "release_date": _local_version_release_date(
                mc_dir,
                version_id
            ),
            "category": _version_category(
                version_id
            ),
            "installed": True,
            "catalogued": False,
            "download_available": False,
            "archived": True,
            "source": (
                _version_loader_source(
                    version_id
                )
                or "Local"
            ),
        })

    # Keep old local entries in the registry even if later uninstalled, but
    # accurately mark them unavailable.
    for item in versions:
        version_id = str(
            item.get("id", "")
        )

        if not item.get(
            "catalogued",
            False
        ):
            item["installed"] = (
                version_id
                in installed_versions
            )

    save_versionref(
        data
    )
    return data



def java_versions(mc_dir: Path):
    versions = mc_dir / "versions"
    if not versions.exists():
        return []
    found = []
    for d in versions.iterdir():
        if d.is_dir() and (d / f"{d.name}.json").exists():
            found.append(d.name)
    return sorted(found, key=lambda s: s.lower())


def load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def merge_version_json(mc_dir: Path, version_id: str):
    path = mc_dir / "versions" / version_id / f"{version_id}.json"
    if not path.exists():
        raise RuntimeError(f"Version metadata is missing:\n{path}")
    child = load_json(path)
    parent_id = child.get("inheritsFrom")
    if not parent_id:
        return child

    parent = merge_version_json(mc_dir, parent_id)
    merged = dict(parent)
    for key, val in child.items():
        if key == "libraries":
            merged[key] = parent.get(key, []) + val
        elif key == "arguments":
            args = dict(parent.get("arguments", {}))
            for k in ("game", "jvm"):
                args[k] = parent.get("arguments", {}).get(k, []) + val.get(k, [])
            merged[key] = args
        else:
            merged[key] = val
    return merged


def rule_matches(rule):
    osrule = rule.get("os")
    if osrule:
        name = osrule.get("name")
        if name and name != "windows":
            return False
        arch = osrule.get("arch")
        if arch and arch not in ("x86_64", "amd64") and platform.machine().lower() in ("amd64", "x86_64"):
            return False
        ver = osrule.get("version")
        if ver:
            try:
                if not re.search(ver, platform.version()):
                    return False
            except re.error:
                pass
    features = rule.get("features")
    if features:
        # No special quick-play/demo/custom-resolution features enabled here.
        for _, required in features.items():
            if required:
                return False
    return True


def allowed(entry):
    rules = entry.get("rules")
    if not rules:
        return True
    result = False
    for rule in rules:
        if rule_matches(rule):
            result = rule.get("action") == "allow"
    return result


def argument_values(items):
    out = []
    for item in items:
        if isinstance(item, str):
            out.append(item)
        elif isinstance(item, dict) and allowed(item):
            v = item.get("value", [])
            if isinstance(v, str):
                out.append(v)
            else:
                out.extend(v)
    return out


def find_java(mc_dir: Path, major=None):
    runtime = mc_dir / "runtime"
    candidates = []
    if runtime.exists():
        candidates.extend(runtime.rglob("javaw.exe"))
        candidates.extend(runtime.rglob("java.exe"))
    jh = os.getenv("JAVA_HOME")
    if jh:
        for n in ("javaw.exe", "java.exe"):
            p = Path(jh) / "bin" / n
            if p.exists():
                candidates.append(p)
    for name in ("javaw.exe", "java.exe"):
        found = shutil.which(name)
        if found:
            candidates.append(Path(found))
    if not candidates:
        raise RuntimeError(
            "No Java runtime was found. Install Java or launch Java Edition once with "
            "an official installation so a runtime exists."
        )
    return str(candidates[0])


def library_path(mc_dir: Path, lib):
    dl = lib.get("downloads", {}).get("artifact")
    if dl and dl.get("path"):
        return mc_dir / "libraries" / dl["path"]

    # Fallback for old metadata.
    name = lib.get("name", "")
    parts = name.split(":")
    if len(parts) < 3:
        return None
    group, artifact, version = parts[:3]
    classifier = parts[3] if len(parts) > 3 else None
    filename = f"{artifact}-{version}" + (f"-{classifier}" if classifier else "") + ".jar"
    return mc_dir / "libraries" / group.replace(".", "/") / artifact / version / filename


def extract_natives(mc_dir: Path, meta, native_dir: Path):
    native_dir.mkdir(parents=True, exist_ok=True)
    for lib in meta.get("libraries", []):
        if not allowed(lib):
            continue
        natives = lib.get("natives", {})
        classifier = natives.get("windows")
        if not classifier:
            continue
        classifier = classifier.replace("${arch}", "64" if platform.architecture()[0] == "64bit" else "32")
        info = lib.get("downloads", {}).get("classifiers", {}).get(classifier)
        if not info or not info.get("path"):
            continue
        jar = mc_dir / "libraries" / info["path"]
        if not jar.exists():
            continue
        excludes = lib.get("extract", {}).get("exclude", ["META-INF/"])
        try:
            with zipfile.ZipFile(jar) as z:
                for member in z.infolist():
                    if member.is_dir():
                        continue
                    if any(member.filename.startswith(x) for x in excludes):
                        continue
                    # Prevent path traversal.
                    target = (native_dir / member.filename).resolve()
                    if not str(target).startswith(str(native_dir.resolve())):
                        continue
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with z.open(member) as src, open(target, "wb") as dst:
                        shutil.copyfileobj(src, dst)
        except zipfile.BadZipFile:
            pass


def launch_java(mc_dir: Path, version_id: str, session, memory_mb=4096, client_id=""):
    meta = merge_version_json(mc_dir, version_id)
    version_dir = mc_dir / "versions" / version_id

    # Fabric/Forge child manifests may inherit the actual client jar from a parent.
    client_jar = version_dir / f"{version_id}.jar"
    if not client_jar.exists():
        parent = meta.get("inheritsFrom")
        if parent:
            client_jar = mc_dir / "versions" / parent / f"{parent}.jar"
    if not client_jar.exists():
        # Locate jar using effective id if inherited metadata got merged.
        effective = meta.get("id", version_id)
        alt = mc_dir / "versions" / effective / f"{effective}.jar"
        if alt.exists():
            client_jar = alt

    cp = []
    for lib in meta.get("libraries", []):
        if allowed(lib) and "natives" not in lib:
            p = library_path(mc_dir, lib)
            if p and p.exists():
                cp.append(str(p))
    if client_jar.exists():
        cp.append(str(client_jar))
    else:
        raise RuntimeError(f"Client JAR for {version_id} was not found.")

    native_dir = Path(tempfile.mkdtemp(prefix="tcloud_mc_natives_"))
    extract_natives(mc_dir, meta, native_dir)

    java_major = meta.get("javaVersion", {}).get("majorVersion")
    java = find_java(mc_dir, java_major)

    assets_index = meta.get("assetIndex", {}).get("id", meta.get("assets", "legacy"))

    replacements = {
        "${natives_directory}": str(native_dir),
        "${launcher_name}": "SuppleLauncher",
        "${launcher_version}": "0.1",
        "${classpath}": os.pathsep.join(cp),
        "${classpath_separator}": os.pathsep,
        "${library_directory}": str(mc_dir / "libraries"),
        "${auth_player_name}": session["name"],
        "${version_name}": version_id,
        "${game_directory}": str(mc_dir),
        "${assets_root}": str(mc_dir / "assets"),
        "${assets_index_name}": str(assets_index),
        "${auth_uuid}": session["uuid"],
        "${auth_access_token}": session["access_token"],
        "${clientid}": client_id,
        "${auth_xuid}": session.get("xuid", ""),
        "${user_type}": "msa",
        "${version_type}": meta.get("type", "release"),
        "${resolution_width}": "854",
        "${resolution_height}": "480",
    }

    def replace(s):
        for k, v in replacements.items():
            s = s.replace(k, str(v))
        return s

    jvm = []
    game = []
    if "arguments" in meta:
        jvm = [replace(x) for x in argument_values(meta["arguments"].get("jvm", []))]
        game = [replace(x) for x in argument_values(meta["arguments"].get("game", []))]
    else:
        # Legacy metadata.
        game = [replace(x) for x in meta.get("minecraftArguments", "").split()]

    # Ensure these exist even when old metadata did not provide JVM args.
    if not any(a.startswith("-Djava.library.path=") for a in jvm):
        jvm.append("-Djava.library.path=" + str(native_dir))
    if "-cp" not in jvm and "-classpath" not in jvm:
        jvm.extend(["-cp", os.pathsep.join(cp)])

    jvm.insert(0, f"-Xmx{int(memory_mb)}M")
    main_class = meta.get("mainClass")
    if not main_class:
        raise RuntimeError("Version metadata does not specify a Java main class.")

    cmd = [java] + jvm + [main_class] + game
    log("Launching Java version " + version_id)
    subprocess.Popen(cmd, cwd=str(mc_dir))
    return cmd


# --------------------------- Windows game discovery ---------------------------

GAME_PATTERNS = {
    "Bedrock": [
        r"Minecraft for Windows",
        r"Minecraft.*Windows",
    ],
    "Dungeons": [
        r"Minecraft Dungeons(?! II| 2)",
    ],
    "Dungeons II": [
        r"Minecraft Dungeons II",
        r"Minecraft Dungeons 2",
    ],
    "Legends": [
        r"Minecraft Legends",
    ],
}


def get_start_apps():
    # Get-StartApps provides app display names and AppIDs/AUMIDs that Windows can activate.
    script = r"""
$ErrorActionPreference='SilentlyContinue'
Get-StartApps | Select-Object Name, AppID | ConvertTo-Json -Compress
"""
    raw = powershell(script).strip()
    if not raw:
        return []
    data = json.loads(raw)
    if isinstance(data, dict):
        data = [data]
    return data


def discover_games():
    result = {k: None for k in GAME_PATTERNS}
    try:
        apps = get_start_apps()
    except Exception as e:
        log(f"App discovery failed: {e}")
        apps = []

    for label, patterns in GAME_PATTERNS.items():
        for app in apps:
            name = app.get("Name", "") or ""
            if any(re.search(pat, name, re.I) for pat in patterns):
                result[label] = {"name": name, "appid": app.get("AppID", "")}
                break
    return result


def launch_aumid(appid: str):
    if not appid:
        raise RuntimeError("No Windows application ID was found.")
    # Explorer handles shell application activation.
    subprocess.Popen(["explorer.exe", f"shell:AppsFolder\\{appid}"])


# ----------------------------------- GUI -----------------------------------

BASE_DIR = Path(__file__).resolve().parent
TEXTURES_DIR = BASE_DIR / "textures"
FONTS_DIR = BASE_DIR / "fonts"

LOCAL_FOLDERS = [TEXTURES_DIR, FONTS_DIR]
for _folder in LOCAL_FOLDERS:
    try:
        _folder.mkdir(parents=True, exist_ok=True)
    except Exception:
        pass

GEOFONT_FILE = FONTS_DIR / "Geo-Regular.otf"
PIXEL_FONT_FAMILY = "Geo"

def resolve_loaded_font_family(root, preferred_path: Path, fallback="Segoe UI"):
    """
    Native Tk widgets use the bundled Geo font when Windows exposes the
    privately loaded family to Tk. Rasterized launcher text always uses the
    bundled font file directly, so it does not depend on system installation.
    """
    try:
        families = set(tkfont.families(root))
    except Exception:
        return fallback

    if "Geo" in families:
        return "Geo"

    return fallback


GAME_DISPLAY_TITLES = {
    "Java Edition": "Java Edition",
    "Bedrock": "Bedrock Edition",
    "Dungeons": "Dungeons",
    "Dungeons II": "Dungeons II",
    "Legends": "Legends",
}


GAME_BUY_URLS = {
    "Java Edition": "https://www.minecraft.net/en-us/store/minecraft-java-bedrock-edition-pc",
    "Bedrock": "https://www.minecraft.net/en-us/store/minecraft-java-bedrock-edition-pc",
    "Dungeons": "https://www.minecraft.net/en-us/store/minecraft-dungeons",
    "Dungeons II": "https://www.minecraft.net/en-us/store/minecraft-dungeons-ii",
    "Legends": "https://www.minecraft.net/store/legends-standard-edition",
}

GAME_TOOLS = {
    "Java Edition": [
        ("Main", "java_main"),
        ("Skins", "java_skins"),
        ("Screenshots", "java_screenshots"),
        ("Worlds", "java_worlds"),
        ("Servers", "java_servers"),
        ("Logs", "java_logs"),
        ("Resource Packs", "java_resourcepacks"),
    ],
    "Bedrock": [
        ("Main", "bedrock_main"),
        ("Skins", "bedrock_skins"),
        ("Worlds", "bedrock_worlds"),
        ("Resource Packs", "bedrock_resourcepacks"),
        ("Behavior Packs", "bedrock_behaviorpacks"),
        ("Screenshots", "bedrock_screenshots"),
    ],
    "Dungeons": [
        ("Main", "dungeons_main"),
        ("Saves", "dungeons_saves"),
        ("Screenshots", "dungeons_screenshots"),
    ],
    "Dungeons II": [
        ("Main", "dungeons2_main"),
        ("Saves", "dungeons2_saves"),
        ("Screenshots", "dungeons2_screenshots"),
    ],
    "Legends": [
        ("Main", "legends_main"),
        ("Saves", "legends_saves"),
        ("Screenshots", "legends_screenshots"),
    ],
}


def load_private_windows_font(path: Path) -> bool:
    if os.name != "nt" or not path.exists():
        return False
    try:
        FR_PRIVATE = 0x10
        return bool(ctypes.windll.gdi32.AddFontResourceExW(str(path), FR_PRIVATE, 0))
    except Exception as exc:
        log(f"Could not load font {path}: {exc}")
        return False



class Tooltip:
    def __init__(self, widget, text="", launcher=None, delay=450):
        self.widget = widget
        self.text = text or ""
        self.launcher = launcher
        self.delay = delay
        self.after_id = None
        self.window = None

        widget.bind("<Enter>", self._enter, add="+")
        widget.bind("<Leave>", self._leave, add="+")
        widget.bind("<ButtonPress>", self._leave, add="+")

    def set_text(self, text):
        self.text = text or ""
        if not self.text:
            self._leave()

    def _enter(self, _event=None):
        if not self.text:
            return
        self._leave()
        self.after_id = self.widget.after(self.delay, self._show)

    def _show(self):
        if not self.text:
            return
        try:
            x = self.widget.winfo_rootx() + 12
            y = self.widget.winfo_rooty() + self.widget.winfo_height() + 8
        except Exception:
            return

        self.window = tk.Toplevel(self.widget)
        self.window.overrideredirect(True)
        self.window.attributes("-topmost", True)

        frame = tk.Frame(
            self.window,
            bg="#111111",
            bd=2,
            relief="solid"
        )
        frame.pack()

        label = tk.Label(
            frame,
            text=self.text,
            bg="#111111",
            fg="#ffffff",
            justify="left",
            padx=7,
            pady=5,
            wraplength=360,
            font=(
                self.launcher.ui_font if self.launcher else "Segoe UI",
                9
            )
        )
        label.pack()
        self.window.geometry(f"+{x}+{y}")

    def _leave(self, _event=None):
        if self.after_id is not None:
            try:
                self.widget.after_cancel(self.after_id)
            except Exception:
                pass
            self.after_id = None

        if self.window is not None:
            try:
                self.window.destroy()
            except Exception:
                pass
            self.window = None



class PixelScrollbar(tk.Canvas):
    """Square custom vertical scrollbar used by SML popup/list panels."""

    def __init__(self, master, command=None, width=14, launcher=None):
        self.launcher = launcher
        self.command = command
        self._first = 0.0
        self._last = 1.0
        self._drag_offset = 0

        bg = launcher.PANEL_2 if launcher else "#303030"
        super().__init__(
            master,
            width=width,
            bg=bg,
            bd=0,
            highlightthickness=0,
            cursor="hand2"
        )

        self.track = self.create_rectangle(
            2, 2, width - 2, 100,
            fill="#1b1b1b",
            outline="#606060",
            width=1
        )
        self.thumb = self.create_rectangle(
            3, 3, width - 3, 24,
            fill="#777777",
            outline="#a0a0a0",
            width=1
        )

        self.bind("<Configure>", self._redraw)
        self.bind("<Button-1>", self._press)
        self.bind("<B1-Motion>", self._drag)

    def set(self, first, last):
        self._first = float(first)
        self._last = float(last)
        self._redraw()

    def _geometry(self):
        h = max(1, self.winfo_height())
        top = 2
        bottom = h - 2
        track_h = max(1, bottom - top)

        thumb_h = max(
            18,
            int(track_h * max(0.0, self._last - self._first))
        )
        thumb_h = min(track_h, thumb_h)

        travel = max(1, track_h - thumb_h)
        y1 = top + int(travel * self._first)
        y2 = y1 + thumb_h
        return top, bottom, y1, y2, travel, thumb_h

    def _redraw(self, _event=None):
        width = max(8, self.winfo_width())
        top, bottom, y1, y2, _, _ = self._geometry()

        self.coords(
            self.track,
            2, top,
            width - 2, bottom
        )
        self.coords(
            self.thumb,
            3, y1,
            width - 3, y2
        )

    def _press(self, event):
        _, _, y1, y2, travel, _ = self._geometry()

        if y1 <= event.y <= y2:
            self._drag_offset = event.y - y1
            return

        if not callable(self.command):
            return

        fraction = max(
            0.0,
            min(1.0, event.y / max(1, self.winfo_height()))
        )
        self.command("moveto", fraction)

    def _drag(self, event):
        if not callable(self.command):
            return

        top, _, _, _, travel, _ = self._geometry()
        new_y = event.y - self._drag_offset
        fraction = (new_y - top) / max(1, travel)
        fraction = max(0.0, min(1.0, fraction))
        self.command("moveto", fraction)




class PixelCheckbox(tk.Frame):
    """Launcher-styled hard-edged checkbox."""

    def __init__(
        self,
        master,
        launcher,
        text,
        value=True,
        command=None,
        font_size=8
    ):
        super().__init__(
            master,
            bg=launcher.PANEL,
            bd=0,
            highlightthickness=0
        )

        self.launcher = launcher
        self.label_text = str(text)
        self.value = bool(value)
        self.command = command

        self.box = tk.Canvas(
            self,
            width=18,
            height=18,
            bg=launcher.PANEL,
            bd=0,
            highlightthickness=0,
            cursor="hand2"
        )
        self.box.pack(
            side="left",
            padx=(0, 5)
        )

        self.label = tk.Label(
            self,
            bg=launcher.PANEL,
            fg=launcher.TEXT,
            cursor="hand2",
            anchor="w"
        )
        launcher._set_pixel_label_text(
            self.label,
            self.label_text,
            font_size,
            launcher.TEXT
        )
        self.label.pack(
            side="left"
        )

        for widget in (
            self,
            self.box,
            self.label,
        ):
            widget.bind(
                "<Button-1>",
                self._toggle
            )

        self._draw()

    def _draw(self):
        self.box.delete(
            "all"
        )

        self.box.create_rectangle(
            1,
            1,
            16,
            16,
            fill=self.launcher.PANEL_3,
            outline="#8a8a8a",
            width=2
        )

        if self.value:
            # Blocky check mark.
            self.box.create_rectangle(
                4,
                8,
                6,
                11,
                fill=self.launcher.TEXT,
                outline=""
            )
            self.box.create_rectangle(
                6,
                10,
                8,
                13,
                fill=self.launcher.TEXT,
                outline=""
            )
            self.box.create_rectangle(
                8,
                7,
                10,
                11,
                fill=self.launcher.TEXT,
                outline=""
            )
            self.box.create_rectangle(
                10,
                4,
                12,
                8,
                fill=self.launcher.TEXT,
                outline=""
            )

    def _toggle(self, _event=None):
        self.value = not self.value
        self._draw()

        if callable(
            self.command
        ):
            self.command(
                self.value
            )

    def get(self):
        return self.value

    def set(self, value):
        self.value = bool(
            value
        )
        self._draw()


class CustomDropdown(tk.Frame):
    """Custom dropdown with selectable rows and optional right-side action buttons."""

    def __init__(self, master, launcher, items=None, value="", width=None,
                 command=None, placeholder="Select...", tooltip=""):
        super().__init__(master, bg=launcher.PANEL, bd=0, highlightthickness=0)
        self.launcher = launcher
        self.items = []
        self.value = value
        self.command = command
        self.placeholder = placeholder
        self.pixel_width = 0
        self.requested_width = width
        self.popup = None
        self.enabled = True
        self._tooltip_text = tooltip
        self._width_measure_cache = {}
        self._measure_font = None
        self._tk_measure_font = None
        self._column_layout = None

        # Width calculation runs across the entire version catalog. Tk's
        # font metrics are dramatically cheaper here than Pillow getbbox()
        # calls for every unique version string.
        try:
            self._tk_measure_font = tkfont.Font(
                family=launcher.ui_font,
                size=9
            )
        except Exception:
            self._tk_measure_font = None

        # Keep the Pillow font only as a fallback for unusual environments.
        try:
            if ImageFont is not None and GEOFONT_FILE.exists():
                self._measure_font = ImageFont.truetype(
                    str(GEOFONT_FILE),
                    20
                )
        except Exception:
            self._measure_font = None

        self.button = tk.Button(
            self,
            text="",
            command=self.toggle,
            bg=launcher.PANEL_3,
            fg=launcher.TEXT,
            activebackground="#ffffff",
            activeforeground="#000000",
            relief="sunken",
            bd=3,
            highlightthickness=0,
            anchor="w",
            padx=6,
            pady=1,
            cursor="hand2",
            compound="left"
        )
        self.button.pack(fill="x", expand=True)
        self.tooltip = Tooltip(
            self.button,
            self._tooltip_text,
            launcher=launcher
        )
        self.button._text_photo = None
        self.button._hover_value = 0.0
        self.button._hover_target = 0.0

        self.button.bind("<Enter>", lambda e: self._set_main_hover(1.0))
        self.button.bind("<Leave>", lambda e: self._set_main_hover(0.0))

        self.set_items(items or [])
        self.set(value, notify=False)

    def _measure_text_width(self, text):
        value = str(text or "")

        cached = self._width_measure_cache.get(value)
        if cached is not None:
            return cached

        # This method may run over the entire version catalog, so avoid
        # Pillow getbbox() for every entry.  Tk metrics are very cheap, but
        # Geo is ultimately rasterized by Pillow and can be wider than
        # Tk reports.  Keep a conservative character-width floor so action
        # buttons and columns never get clipped.
        width = 0
        try:
            if self._tk_measure_font is not None:
                width = int(self._tk_measure_font.measure(value if value else " "))
        except Exception:
            width = 0

        width = max(1, width, len(value) * 12)
        self._width_measure_cache[value] = width
        return width


    def _required_width_for_text(self, text):
        return max(
            54,
            self._measure_text_width(
                "@@@@@"
            ) + 30,
            self._measure_text_width(
                text
            ) + 30
        )


    def _action_width_for_item(self, item):
        total = 0

        for action in item.get(
            "actions",
            []
        ):
            total += max(
                48,
                self._measure_text_width(
                    action.get(
                        "label",
                        "..."
                    )
                ) + 26
            ) + 3

        return total


    def _right_text_width_for_item(self, item):
        right_text = str(
            item.get(
                "right_text",
                ""
            )
            or ""
        )

        if not right_text:
            return 0

        return (
            self._measure_text_width(
                right_text
            )
            + 14
        )


    def _source_text_width_for_item(self, item):
        source_text = str(
            item.get(
                "source_text",
                ""
            )
            or ""
        )

        if not source_text:
            return 0

        return (
            self._measure_text_width(
                source_text
            )
            + 14
        )


    def _prepare_column_layout(self):
        rows = [
            item
            for item in self.items
            if (
                item.get("right_text") is not None
                or item.get("source_text") is not None
            )
            and item.get("row_type") != "button"
        ]

        if not rows:
            self._column_layout = None
            return

        label_w = self._measure_text_width(
            "@@@@@"
        )
        date_w = self._measure_text_width(
            "Unknown"
        )
        source_w = self._measure_text_width(
            "Omniarchive"
        )
        action_w = self._measure_text_width(
            "Download"
        ) + 26

        for item in rows:
            label_w = max(
                label_w,
                self._measure_text_width(
                    item.get(
                        "label",
                        ""
                    )
                )
            )
            date_w = max(
                date_w,
                self._measure_text_width(
                    item.get(
                        "right_text",
                        ""
                    )
                )
            )
            source_w = max(
                source_w,
                self._measure_text_width(
                    item.get(
                        "source_text",
                        ""
                    )
                )
            )

            for action in item.get(
                "actions",
                []
            ):
                action_w = max(
                    action_w,
                    self._measure_text_width(
                        action.get(
                            "label",
                            ""
                        )
                    ) + 26
                )

        self._column_layout = {
            "label": label_w + 20,
            "date": date_w + 20,
            "source": source_w + 20,
            "action": max(
                76,
                action_w + 8
            ),
        }




    def _fit_width_to_items(self):
        """
        Size every dropdown to the longest complete row.

        Normal rows include both their label and any right-side action buttons,
        so installation dropdowns reserve space for EDIT instead of wrapping
        the installation name underneath it.
        """
        minimum = self._required_width_for_text(
            "@@@@@"
        )

        if self._column_layout:
            layout = self._column_layout
            self.pixel_width = int(
                layout["label"]
                + layout["date"]
                + layout["source"]
                + layout["action"]
                + 16
            )
            return

        width = minimum

        if not self.items:
            width = max(
                width,
                self._required_width_for_text(
                    str(self.value or "")
                )
            )

        for item in self.items:
            label = str(
                item.get("label", "")
            )

            row_width = self._required_width_for_text(
                label
            )

            if item.get("row_type") != "button":
                row_width += self._action_width_for_item(
                    item
                )
                row_width += self._right_text_width_for_item(
                    item
                )

            width = max(
                width,
                row_width
            )

        self.pixel_width = int(width)


    def set_items(self, items):
        out = []
        for item in items:
            if isinstance(item, str):
                out.append({"label": item, "value": item, "actions": []})
            else:
                d = dict(item)
                d.setdefault("label", str(d.get("value", "")))
                d.setdefault("value", d.get("label", ""))
                d.setdefault("actions", [])
                out.append(d)
        self.items = out
        self._prepare_column_layout()
        self._fit_width_to_items()
        self._refresh_button()

    def _label(self):
        for item in self.items:
            if item.get("value") == self.value:
                return item.get("label", str(self.value))
        return str(self.value) if self.value else self.placeholder

    def _render_main_text(self, color):
        display = self._label()
        photo = self.launcher._dropdown_text_photo(
            display,
            color,
            max_width=max(100, self.pixel_width),
            exact_width=max(54, self.pixel_width)
        )
        if photo is not None:
            self.button._text_photo = photo
            self.button.config(image=photo, text="")
        else:
            self.button.config(
                image="",
                text=display,
                fg=color,
                font=(self.launcher.ui_font, 9)
            )

    def _refresh_button(self):
        self._render_main_text(self.launcher.TEXT)

    def get(self):
        return self.value

    def set(self, value, notify=True):
        self.value = value

        # Normally the longest list item controls width. If a caller sets a
        # value that is not currently in the list, allow that value to expand
        # the dropdown rather than clipping it.
        known_values = {
            item.get("value")
            for item in self.items
        }
        if value not in known_values and value:
            self.pixel_width = max(
                self.pixel_width,
                self._required_width_for_text(
                    self._label()
                )
            )

        self._refresh_button()
        if notify and self.command:
            self.command(value)

    def _set_main_hover(self, target):
        if not self.enabled:
            return
        self.button._hover_target = float(target)
        self._animate_main_hover()

    def _animate_main_hover(self):
        current = float(getattr(self.button, "_hover_value", 0.0))
        target = float(getattr(self.button, "_hover_target", 0.0))
        step = 0.15
        if abs(current - target) < 0.02:
            current = target
        elif current < target:
            current = min(target, current + step)
        else:
            current = max(target, current - step)

        self.button._hover_value = current
        bg = self.launcher._mix_color(self.launcher.PANEL_3, "#ffffff", current)
        fg = self.launcher._mix_color("#ffffff", "#000000", current)

        try:
            self.button.config(
                bg=bg, activebackground=bg,
                fg=fg, activeforeground=fg
            )
            self._render_main_text(fg)
        except tk.TclError:
            return

        if current != target:
            self.after(16, self._animate_main_hover)

    def set_enabled(self, enabled, tooltip=None):
        self.enabled = bool(enabled)

        if tooltip is not None:
            self.tooltip.set_text(tooltip)

        # Do not use Tk's disabled state because image-backed buttons become
        # stippled/patterned. Disabled behavior is enforced logically.
        self.button.config(
            state="normal",
            cursor="hand2" if self.enabled else "arrow"
        )

        self.button._hover_value = 0.0
        self.button._hover_target = 0.0

        if self.enabled:
            self.button.config(
                bg=self.launcher.PANEL_3,
                activebackground=self.launcher.PANEL_3
            )
            self._render_main_text(self.launcher.TEXT)
        else:
            self.button.config(
                bg="#555555",
                activebackground="#555555"
            )
            self._render_main_text("#9b9b9b")
            self.close()


    def toggle(self):
        if not self.enabled:
            return

        if self.popup and self.popup.winfo_exists():
            self.close()
        else:
            self.open()

    def close(self):
        if self.popup and self.popup.winfo_exists():
            self.popup.destroy()
        self.popup = None

    def _choose(self, value, keep_open=False):
        self.set(value, notify=True)
        if not keep_open:
            self.close()

    def _action(self, action):
        fn = action.get("command")
        if callable(fn):
            fn()

    def _make_aligned_metadata_row(
        self,
        parent,
        item
    ):
        layout = self._column_layout
        selectable = bool(
            item.get(
                "selectable",
                True
            )
        )

        row = tk.Frame(
            parent,
            bg=self.launcher.PANEL_2,
            bd=0,
            height=31,
            cursor=(
                "hand2"
                if selectable
                else "arrow"
            )
        )
        row.pack(
            fill="x",
            padx=3,
            pady=1
        )
        row.pack_propagate(False)

        holders = {}

        for name in (
            "label",
            "date",
            "source",
            "action",
        ):
            holder = tk.Frame(
                row,
                bg=self.launcher.PANEL_2,
                width=layout[name],
                height=31
            )
            holder.pack(
                side="left",
                fill="y"
            )
            holder.pack_propagate(False)
            holders[name] = holder

        normal_label_color = item.get(
            "label_color",
            self.launcher.TEXT
        )

        label = tk.Label(
            holders["label"],
            bg=self.launcher.PANEL_2,
            fg=normal_label_color,
            anchor="w"
        )
        label.pack(
            fill="both",
            expand=True,
            padx=(7, 4)
        )

        date_text = str(
            item.get(
                "right_text",
                ""
            )
            or ""
        )
        date_label = tk.Label(
            holders["date"],
            bg=self.launcher.PANEL_2,
            fg=self.launcher.MUTED,
            anchor="e"
        )
        date_label.pack(
            fill="both",
            expand=True,
            padx=5
        )

        source_text = str(
            item.get(
                "source_text",
                ""
            )
            or ""
        )
        source_label = tk.Label(
            holders["source"],
            bg=self.launcher.PANEL_2,
            fg=self.launcher.MUTED,
            anchor="e"
        )
        source_label.pack(
            fill="both",
            expand=True,
            padx=5
        )

        def render(
            label_color=normal_label_color,
            metadata_color=None
        ):
            if metadata_color is None:
                metadata_color = self.launcher.MUTED

            self.launcher._set_pixel_label_text(
                label,
                item.get("label", ""),
                9,
                label_color,
                max_width=max(40, layout["label"] - 12),
                align="left"
            )
            self.launcher._set_pixel_label_text(
                date_label,
                date_text,
                8,
                metadata_color,
                max_width=max(40, layout["date"] - 10),
                align="right"
            )
            self.launcher._set_pixel_label_text(
                source_label,
                source_text,
                8,
                metadata_color,
                max_width=max(40, layout["source"] - 10),
                align="right"
            )

        render()

        actions = item.get(
            "actions",
            []
        )

        if actions:
            action = actions[0]
            button = self.launcher.beveled_button(
                holders["action"],
                action.get(
                    "label",
                    "Download"
                ),
                lambda a=action: self._action(
                    a
                ),
                font_size=8,
                tooltip=action.get(
                    "tooltip",
                    ""
                )
            )
            button.pack(
                fill="x",
                padx=4,
                pady=2
            )
            self.launcher.set_button_enabled(
                button,
                bool(
                    action.get(
                        "enabled",
                        True
                    )
                ),
                tooltip=action.get(
                    "tooltip",
                    ""
                )
            )

        def hover(active):
            bg = (
                "#ffffff"
                if active
                else self.launcher.PANEL_2
            )

            row.config(
                bg=bg
            )

            for holder in holders.values():
                holder.config(
                    bg=bg
                )

            label.config(
                bg=bg
            )
            date_label.config(
                bg=bg
            )
            source_label.config(
                bg=bg
            )

            render(
                "#000000"
                if active
                else normal_label_color,
                "#555555"
                if active
                else self.launcher.MUTED
            )

        def choose(_event=None):
            if not selectable:
                return "break"

            self._choose(
                item.get(
                    "value"
                ),
                keep_open=bool(
                    item.get(
                        "keep_open"
                    )
                )
            )
            return "break"

        for widget in (
            row,
            holders["label"],
            holders["date"],
            holders["source"],
            label,
            date_label,
            source_label,
        ):
            widget.bind(
                "<Enter>",
                lambda e: hover(True)
            )
            widget.bind(
                "<Leave>",
                lambda e: hover(False)
            )
            widget.bind(
                "<Button-1>",
                choose
            )

        return row


    def _make_row(self, parent, item):
        if (
            self._column_layout
            and item.get("row_type") != "button"
            and (
                item.get("right_text") is not None
                or item.get("source_text") is not None
            )
        ):
            return self._make_aligned_metadata_row(
                parent,
                item
            )

        if item.get("row_type") == "button":
            row = tk.Frame(
                parent,
                bg=self.launcher.PANEL_2,
                bd=0
            )
            row.pack(
                fill="x",
                padx=3,
                pady=2
            )
            button = self.launcher.beveled_button(
                row,
                item.get("label", ""),
                command=lambda: self._choose(
                    item.get("value"),
                    keep_open=bool(
                        item.get(
                            "keep_open"
                        )
                    )
                ),
                font_size=9
            )
            button.pack(
                fill="x",
                expand=True
            )
            return row

        selectable = bool(
            item.get(
                "selectable",
                True
            )
        )

        row = tk.Frame(
            parent,
            bg=self.launcher.PANEL_2,
            bd=0,
            height=29,
            cursor=(
                "hand2"
                if selectable
                else "arrow"
            )
        )
        row.pack(
            fill="x",
            padx=3,
            pady=1
        )
        row.pack_propagate(
            False
        )

        # Actions are packed first on the far right.
        for action in reversed(
            item.get(
                "actions",
                []
            )
        ):
            action_button = self.launcher.beveled_button(
                row,
                action.get(
                    "label",
                    "..."
                ),
                lambda a=action: self._action(
                    a
                ),
                font_size=8
            )
            action_button.pack(
                side="right",
                padx=(3, 0),
                pady=1
            )

        date_label = None
        right_text = str(
            item.get(
                "right_text",
                ""
            )
            or ""
        )

        if right_text:
            date_label = tk.Label(
                row,
                bg=self.launcher.PANEL_2,
                fg=self.launcher.MUTED,
                anchor="e",
                padx=6,
                cursor=(
                    "hand2"
                    if selectable
                    else "arrow"
                )
            )

            self.launcher._set_pixel_label_text(
                date_label,
                right_text,
                8,
                self.launcher.MUTED,
                align="right"
            )

            date_label.pack(
                side="right"
            )

        label = tk.Label(
            row,
            text="",
            bg=self.launcher.PANEL_2,
            fg=self.launcher.TEXT,
            anchor="w",
            padx=7,
            cursor=(
                "hand2"
                if selectable
                else "arrow"
            )
        )
        label.pack(
            side="left",
            fill="both",
            expand=True
        )

        normal_label_color = item.get(
            "label_color",
            self.launcher.TEXT
        )

        def render_label(color):
            action_width = (
                self._action_width_for_item(
                    item
                )
                + self._right_text_width_for_item(
                    item
                )
            )

            photo = self.launcher._hard_text_photo(
                item.get(
                    "label",
                    ""
                ),
                9,
                color,
                max_width=max(
                    100,
                    self.pixel_width
                    - action_width
                    - 18
                ),
                align="left"
            )

            if photo is not None:
                label._text_photo = photo
                label.config(
                    image=photo,
                    text=""
                )
            else:
                label.config(
                    image="",
                    text=item.get(
                        "label",
                        ""
                    ),
                    fg=color,
                    font=(
                        self.launcher.ui_font,
                        9
                    )
                )

        render_label(
            normal_label_color
        )

        def hover(active):
            bg = (
                "#ffffff"
                if active
                else self.launcher.PANEL_2
            )

            if active:
                label_color = (
                    "#555555"
                    if normal_label_color
                    != self.launcher.TEXT
                    else "#000000"
                )
                date_color = "#555555"
            else:
                label_color = (
                    normal_label_color
                )
                date_color = (
                    self.launcher.MUTED
                )

            row.config(
                bg=bg
            )
            label.config(
                bg=bg,
                fg=label_color
            )
            render_label(
                label_color
            )

            if date_label is not None:
                date_label.config(
                    bg=bg,
                    fg=date_color
                )
                self.launcher._set_pixel_label_text(
                    date_label,
                    right_text,
                    8,
                    date_color,
                    align="right"
                )

        def choose(_event=None):
            if not selectable:
                return "break"

            self._choose(
                item.get(
                    "value"
                ),
                keep_open=bool(
                    item.get(
                        "keep_open"
                    )
                )
            )
            return "break"

        hover_widgets = [
            row,
            label,
        ]

        if date_label is not None:
            hover_widgets.append(
                date_label
            )

        for widget in hover_widgets:
            widget.bind(
                "<Enter>",
                lambda e: hover(
                    True
                )
            )
            widget.bind(
                "<Leave>",
                lambda e: hover(
                    False
                )
            )
            widget.bind(
                "<Button-1>",
                choose
            )

        return row


    def open(self):
        if not self.enabled or not self.items:
            return

        self.close()

        pop = tk.Toplevel(self)
        self.popup = pop
        self._popup_render_token = object()
        render_token = self._popup_render_token

        pop.withdraw()
        pop.overrideredirect(True)
        pop.configure(bg=self.launcher.PANEL_2)

        self.update_idletasks()

        x = self.winfo_rootx()
        y = self.winfo_rooty() + self.winfo_height()

        outer = tk.Frame(
            pop,
            bg=self.launcher.PANEL_2,
            bd=3,
            relief="raised"
        )
        outer.pack(fill="both", expand=True)

        body = tk.Frame(outer, bg=self.launcher.PANEL_2)
        body.pack(fill="both", expand=True)

        rows = tk.Frame(body, bg=self.launcher.PANEL_2)
        rows.pack(side="left", fill="both", expand=True)

        visible_count = min(10, len(self.items))
        needs_scroll = len(self.items) > visible_count
        first_index = 0
        pending_render_job = None

        scrollbar = None
        if needs_scroll:
            scrollbar = PixelScrollbar(
                body,
                width=14,
                launcher=self.launcher
            )
            scrollbar.pack(side="right", fill="y")

        def popup_alive():
            if (
                self.popup is not pop
                or getattr(self, "_popup_render_token", None) is not render_token
            ):
                return False
            try:
                return bool(pop.winfo_exists())
            except tk.TclError:
                return False

        def update_scrollbar():
            if scrollbar is None:
                return
            total = max(1, len(self.items))
            scrollbar.set(
                first_index / total,
                min(1.0, (first_index + visible_count) / total)
            )

        def wheel(event):
            nonlocal first_index
            if not needs_scroll:
                return "break"

            delta = getattr(event, "delta", 0)
            if delta:
                notches = max(1, abs(int(delta)) // 120)
                # Two rows per wheel notch feels responsive while still
                # allowing precise browsing of adjacent historical builds.
                step = (-2 if delta > 0 else 2) * notches
            elif getattr(event, "num", None) == 4:
                step = -2
            else:
                step = 2

            maximum = max(0, len(self.items) - visible_count)
            new_index = max(0, min(maximum, first_index + step))
            if new_index != first_index:
                first_index = new_index
                update_scrollbar()
                request_render()
            return "break"

        def bind_wheel(widget):
            if not needs_scroll:
                return
            widget.bind("<MouseWheel>", wheel, add="+")
            widget.bind("<Button-4>", wheel, add="+")
            widget.bind("<Button-5>", wheel, add="+")
            for child in widget.winfo_children():
                bind_wheel(child)

        def render_visible_rows():
            if not popup_alive():
                return

            for child in rows.winfo_children():
                child.destroy()

            stop = min(len(self.items), first_index + visible_count)
            for item in self.items[first_index:stop]:
                row = self._make_row(rows, item)
                bind_wheel(row)

            update_scrollbar()

        def request_render():
            # Mouse wheels can deliver several events while one set of rows is
            # being drawn. Coalesce them into one redraw at the newest index
            # instead of building obsolete intermediate rows and making the UI
            # feel several ticks behind the user's wheel.
            nonlocal pending_render_job
            if pending_render_job is not None or not popup_alive():
                return

            def flush():
                nonlocal pending_render_job
                pending_render_job = None
                render_visible_rows()

            pending_render_job = pop.after_idle(flush)

        def scroll_command(*args):
            nonlocal first_index
            if not needs_scroll or not args:
                return

            maximum = max(0, len(self.items) - visible_count)

            if args[0] == "moveto" and len(args) > 1:
                try:
                    fraction = float(args[1])
                except (TypeError, ValueError):
                    return
                first_index = int(round(maximum * max(0.0, min(1.0, fraction))))
            elif args[0] == "scroll" and len(args) > 1:
                try:
                    amount = int(args[1])
                except (TypeError, ValueError):
                    return
                first_index = max(0, min(maximum, first_index + amount))
            else:
                return

            update_scrollbar()
            request_render()

        if scrollbar is not None:
            scrollbar.command = scroll_command

        # Each metadata row is 31px high plus 1px vertical packing on both
        # sides. Account for the full 33px slot so the tenth/bottom row is not
        # clipped by the popup geometry.
        row_slot_height = 33
        wanted_h = min(360, max(36, row_slot_height * visible_count + 6))
        wanted_w = max(self.pixel_width, self.winfo_width())
        if needs_scroll:
            wanted_w += 14

        pop.geometry(f"{wanted_w}x{wanted_h}+{x}+{y}")
        pop.bind("<Escape>", lambda e: self.close())
        pop.bind("<MouseWheel>", wheel, add="+")
        pop.bind("<Button-4>", wheel, add="+")
        pop.bind("<Button-5>", wheel, add="+")

        render_visible_rows()
        pop.deiconify()
        pop.lift()
        pop.focus_force()

    def close(self):
        self._popup_render_token = None

        pop = self.popup
        self.popup = None

        if pop is not None:
            try:
                pop.destroy()
            except tk.TclError:
                pass


class Launcher(tk.Tk):
    BG = "#151515"
    PANEL = "#242424"
    PANEL_2 = "#303030"
    PANEL_3 = "#3c3c3c"
    TEXT = "#f3f3f3"
    MUTED = "#bdbdbd"
    GREEN = "#3c8527"
    GREEN_ACTIVE = "#2f6f1f"
    GREEN_DISABLED = "#465143"
    BLACK = "#090909"

    def __init__(self):
        # Give Windows a stable application identity so the custom window icon
        # is also used for taskbar grouping when the launcher is run as Python.
        if os.name == "nt":
            try:
                ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(
                    "SuppleLauncher"
                )
            except Exception:
                pass

        super().__init__()
        self.title(APP_NAME)

        # The launcher icon is user/project artwork stored alongside the other
        # textures.  Missing or invalid icon files should never stop startup.
        if APP_ICON_FILE.exists():
            try:
                self.iconbitmap(default=str(APP_ICON_FILE))
            except Exception as exc:
                log(f"Could not load application icon: {exc}")

        # 1120x720 is the smallest supported window size.  It keeps the
        # widest secondary pages (notably Accounts and Settings) fully
        # visible instead of allowing the user to resize into clipped UI.
        self.geometry("1120x720")
        self.minsize(1120, 720)
        self.configure(bg=self.BG)

        self.pixel_font_loaded = load_private_windows_font(GEOFONT_FILE)
        self.ui_font = resolve_loaded_font_family(self, GEOFONT_FILE, fallback="Segoe UI")
        self.option_add("*Font", (self.ui_font, 10))

        # Pixel text is used throughout the interface.  Re-loading the same
        # font and re-rasterizing identical labels on every page visit was a
        # major source of navigation stalls.  These bounded caches make
        # revisiting pages substantially cheaper while preserving the exact
        # hard-edged appearance.
        self._pil_font_cache = {}
        self._hard_text_photo_cache = {}
        self._dropdown_text_photo_cache = {}
        self._text_photo_cache_limit = 1400

        self.config_data = load_config()
        self.installations_data = load_installations_file()
        self.account_metadata = load_account_metadata()
        self.auth = AuthManager(self.config_data)
        self._cached_java_names_by_hid = {}
        self._cached_gamertags_by_hid = {}
        self._identity_fetch_inflight = set()
        self._version_catalog_fetch_inflight = False
        self._mojang_latest_fetch_inflight = False
        self._mojang_latest_checked_session = False

        saved_profiles = self._account_profile_cache()
        for hid, data in saved_profiles.items():
            if not isinstance(data, dict):
                continue

            gamertag = str(
                data.get("gamertag", "")
            ).strip()

            java_name = str(
                data.get("java_name", "")
            ).strip()

            if gamertag:
                self._cached_gamertags_by_hid[
                    hid
                ] = gamertag

            if java_name:
                self._cached_java_names_by_hid[
                    hid
                ] = java_name
        self.games = {}
        self.account_map = {}
        self.selected_game = "Java Edition"
        self.current_screen = "game"
        self._hover_jobs = {}
        self._loading_job = None
        self._loading_frame = 0
        self._visited_navigation_keys = set()
        self.game_available = {
            "Java Edition": None,
            "Bedrock": None,
            "Dungeons": None,
            "Dungeons II": None,
            "Legends": None,
        }

        self._discovery_results = queue.Queue()
        self._discovery_poll_started = False
        self._ui_dispatch_queue = queue.Queue()
        self._ui_dispatch_poll_started = False

        self._build_shell()
        self._start_discovery_poll()
        self._start_ui_dispatch_poll()
        self.refresh_all()
        self.show_game("Java Edition")
        self._visited_navigation_keys.add(("show_game", ("Java Edition",)))
        self.update_navigation_button_states()

    # ---------- common widgets ----------

    def _hard_text_photo(self, text, size=10, color="#ffffff",
                         max_width=None, align="left"):
        """
        Render the bundled Geo font as hard-edged pixel text.

        GeoFont's dominant glyph grid uses 50-unit steps in a 1000-unit em.
        Rendering at exact 20px multiples therefore keeps those steps aligned
        to whole screen pixels. Sizes such as 16px or 24px cause fractional
        scaling and uneven stroke thickness even with antialiasing disabled.
        """
        if Image is None or ImageTk is None or ImageFont is None or ImageDraw is None:
            return None
        if not GEOFONT_FILE.exists():
            return None

        cache_key = (str(text), int(size), str(color), max_width, str(align))
        cached_photo = self._hard_text_photo_cache.get(cache_key)
        if cached_photo is not None:
            return cached_photo

        try:
            # GeoFont must stay on exact 20px multiples to preserve its
            # intended hard-pixel geometry.
            if size <= 17:
                pixel_size = 20
            elif size <= 27:
                pixel_size = 40
            else:
                pixel_size = 60

            font = self._pil_font_cache.get(pixel_size)
            if font is None:
                font = ImageFont.truetype(str(GEOFONT_FILE), pixel_size)
                self._pil_font_cache[pixel_size] = font

            def measure(line):
                bbox = font.getbbox(
                    line if line else " "
                )
                return max(
                    1,
                    bbox[2] - bbox[0]
                )

            # max_width is already in final screen pixels.
            lines = []

            for raw_line in str(text).split("\n"):
                if max_width is None or raw_line == "":
                    lines.append(raw_line)
                    continue

                current = ""

                for word in raw_line.split(" "):
                    trial = (
                        word
                        if not current
                        else current + " " + word
                    )

                    if measure(trial) <= max_width or not current:
                        current = trial
                    else:
                        lines.append(current)
                        current = word

                lines.append(current)

            if not lines:
                lines = [""]

            metric = font.getbbox("Agyp")
            ascent_offset = metric[1]
            line_height = max(
                1,
                metric[3] - metric[1]
            )

            # Integer spacing only; no fractional resizing after rasterization.
            if pixel_size == 20:
                line_gap = 4
                pad = 4
            elif pixel_size == 40:
                line_gap = 8
                pad = 8
            else:
                line_gap = 12
                pad = 12

            widths = [
                measure(line)
                for line in lines
            ]

            canvas_w = max(widths) + pad * 2
            canvas_h = (
                line_height * len(lines)
                + line_gap * max(
                    0,
                    len(lines) - 1
                )
                + pad * 2
            )

            # One-bit raster: pixels are either fully on or fully off.
            mask = Image.new(
                "1",
                (canvas_w, canvas_h),
                0
            )
            draw = ImageDraw.Draw(mask)

            y = pad - ascent_offset

            for line, line_width in zip(
                lines,
                widths
            ):
                if align == "center":
                    x = (
                        canvas_w - line_width
                    ) // 2
                elif align == "right":
                    x = (
                        canvas_w
                        - line_width
                        - pad
                    )
                else:
                    x = pad

                draw.text(
                    (x, y),
                    line,
                    font=font,
                    fill=1,
                    stroke_width=0
                )

                y += (
                    line_height
                    + line_gap
                )

            rgba = Image.new(
                "RGBA",
                mask.size,
                color
            )

            rgba.putalpha(
                mask.convert("L").point(
                    lambda p: 255 if p else 0
                )
            )

            photo = ImageTk.PhotoImage(rgba)
            self._hard_text_photo_cache[cache_key] = photo
            if len(self._hard_text_photo_cache) > self._text_photo_cache_limit:
                try:
                    self._hard_text_photo_cache.pop(next(iter(self._hard_text_photo_cache)))
                except Exception:
                    pass
            return photo

        except Exception as exc:
            log(
                f"Hard text rendering failed: "
                f"{type(exc).__name__}: {exc}"
            )
            return None

    def _dropdown_text_photo(self, text, color="#ffffff", max_width=240, exact_width=None):
        """
        Render custom-dropdown text with the same hard-edged 20px Geo font,
        then draw the dropdown arrow as pixel geometry.
        """
        if Image is None or ImageTk is None or ImageFont is None or ImageDraw is None:
            return None
        if not GEOFONT_FILE.exists():
            return None

        cache_key = (str(text), str(color), int(max_width), exact_width)
        cached_photo = self._dropdown_text_photo_cache.get(cache_key)
        if cached_photo is not None:
            return cached_photo

        try:
            pixel_size = 20
            font = self._pil_font_cache.get(pixel_size)
            if font is None:
                font = ImageFont.truetype(str(GEOFONT_FILE), pixel_size)
                self._pil_font_cache[pixel_size] = font

            metric = font.getbbox("Agyp")
            bbox = font.getbbox(
                text if text else " "
            )

            text_w = max(
                1,
                bbox[2] - bbox[0]
            )
            text_h = max(
                1,
                metric[3] - metric[1]
            )

            # Keep all geometry integer-aligned with the 20px text raster.
            pad_x = 4
            pad_y = 4
            arrow_w = 8
            arrow_h = 6
            gap = 8

            natural_width = (
                text_w
                + pad_x * 2
                + gap
                + arrow_w
            )

            if exact_width is not None:
                width = max(
                    natural_width,
                    int(exact_width)
                )
            else:
                width = min(
                    max_width,
                    natural_width
                )

            height = max(
                text_h + pad_y * 2,
                24
            )

            mask = Image.new(
                "1",
                (width, height),
                0
            )

            draw = ImageDraw.Draw(mask)

            draw.text(
                (
                    pad_x,
                    pad_y - metric[1]
                ),
                text,
                font=font,
                fill=1,
                stroke_width=0
            )

            # 2-pixel-stepped down arrow.
            ax = (
                width
                - pad_x
                - arrow_w
            )
            ay = (
                height
                - arrow_h
            ) // 2

            draw.rectangle(
                (ax, ay, ax + 7, ay + 1),
                fill=1
            )
            draw.rectangle(
                (ax + 2, ay + 2, ax + 5, ay + 3),
                fill=1
            )
            draw.rectangle(
                (ax + 3, ay + 4, ax + 4, ay + 5),
                fill=1
            )

            rgba = Image.new(
                "RGBA",
                mask.size,
                color
            )

            rgba.putalpha(
                mask.convert("L").point(
                    lambda p: 255 if p else 0
                )
            )

            photo = ImageTk.PhotoImage(rgba)
            self._dropdown_text_photo_cache[cache_key] = photo
            if len(self._dropdown_text_photo_cache) > 300:
                try:
                    self._dropdown_text_photo_cache.pop(next(iter(self._dropdown_text_photo_cache)))
                except Exception:
                    pass
            return photo

        except Exception as exc:
            log(
                f"Dropdown text rendering failed: "
                f"{type(exc).__name__}: {exc}"
            )
            return None

    def _set_pixel_label_text(self, label, text, size=10, color=None,
                              max_width=None, align="left"):
        color = color or self.TEXT
        photo = self._hard_text_photo(
            text, size, color, max_width=max_width, align=align
        )
        if photo is not None:
            label._text_photo = photo
            label.config(image=photo, text="")
        else:
            label.config(
                image="",
                text=text,
                fg=color,
                font=(self.ui_font, size)
            )

    def _update_button_text_image(self, button, color):
        photo = self._hard_text_photo(
            getattr(button, "_label_text", ""),
            getattr(button, "_label_size", 10),
            color,
            align="center"
        )
        if photo is not None:
            button._text_photo = photo
            button.config(image=photo, text="")
        else:
            button.config(
                image="",
                text=getattr(button, "_label_text", ""),
                fg=color
            )

    def beveled_button(self, parent, text, command=None, *, bg=None,
                       font_size=10, anchor="center", width=None, state="normal",
                       tooltip=None):
        bg = bg or self.PANEL_3

        button = tk.Button(
            parent,
            text="",
            command=lambda: self._invoke_button(button),
            bg=bg,
            fg=self.TEXT,
            activebackground=bg,
            activeforeground=self.TEXT,
            relief="raised",
            overrelief="raised",
            bd=3,
            highlightthickness=0,
            padx=10,
            pady=7,
            font=(self.ui_font, font_size),
            anchor=anchor,
            width=width,
            state="normal",
            cursor="hand2",
            compound="center",
            takefocus=False
        )

        button._label_text = text
        button._label_size = font_size
        button._base_bg = bg
        button._base_fg = self.TEXT
        button._hover_value = 0.0
        button._hover_target = 0.0
        button._logical_disabled = (state == "disabled")
        button._real_command = command
        button._tooltip = Tooltip(
            button,
            tooltip or "",
            launcher=self
        )

        self._update_button_visual(button)

        button.bind(
            "<Enter>",
            lambda e, b=button: self._on_button_enter(b),
            add="+"
        )
        button.bind(
            "<Leave>",
            lambda e, b=button: self._on_button_leave(b),
            add="+"
        )
        return button

    def _invoke_button(self, button):
        if getattr(button, "_logical_disabled", False):
            return

        command = getattr(button, "_real_command", None)
        if callable(command):
            command()

    def _button_is_disabled(self, button):
        return bool(
            getattr(
                button,
                "_logical_disabled",
                False
            )
        )

    def _update_button_visual(self, button):
        if self._button_is_disabled(button):
            button._hover_value = 0.0
            button._hover_target = 0.0

            bg = "#555555"
            fg = "#9b9b9b"

            button.config(
                state="normal",
                bg=bg,
                fg=fg,
                activebackground=bg,
                activeforeground=fg,
                cursor="arrow",
                relief="raised"
            )
            self._update_button_text_image(
                button,
                fg
            )
            return

        bg = getattr(
            button,
            "_base_bg",
            self.PANEL_3
        )

        button.config(
            state="normal",
            bg=bg,
            fg=self.TEXT,
            activebackground=bg,
            activeforeground=self.TEXT,
            cursor="hand2"
        )

        self._update_button_text_image(
            button,
            self.TEXT
        )

    def set_button_enabled(self, button, enabled, tooltip=None):
        button._logical_disabled = not bool(enabled)

        if tooltip is not None:
            button._tooltip.set_text(tooltip)

        self._update_button_visual(button)

    def _on_button_enter(self, button):
        if self._button_is_disabled(button):
            return
        self._set_hover_target(
            button,
            1.0
        )

    def _on_button_leave(self, button):
        if self._button_is_disabled(button):
            return
        self._set_hover_target(
            button,
            0.0
        )

    @staticmethod
    def _hex_to_rgb(color):
        color = color.lstrip("#")
        return tuple(int(color[i:i+2], 16) for i in (0, 2, 4))

    @staticmethod
    def _rgb_to_hex(rgb):
        return "#%02x%02x%02x" % tuple(
            max(0, min(255, int(v))) for v in rgb
        )

    def _mix_color(self, a, b, t):
        ar, ag, ab = self._hex_to_rgb(a)
        br, bg, bb = self._hex_to_rgb(b)
        return self._rgb_to_hex((
            ar + (br - ar) * t,
            ag + (bg - ag) * t,
            ab + (bb - ab) * t,
        ))

    def _set_hover_target(self, button, target):
        if self._button_is_disabled(button):
            return
        button._hover_target = target
        self._animate_hover(button)

    def _animate_hover(self, button):
        current = float(getattr(button, "_hover_value", 0.0))
        target = float(getattr(button, "_hover_target", 0.0))

        step = 0.15
        if abs(current - target) < 0.02:
            current = target
        elif current < target:
            current = min(target, current + step)
        else:
            current = max(target, current - step)

        button._hover_value = current

        base_bg = getattr(button, "_base_bg", self.PANEL_3)
        bg = self._mix_color(base_bg, "#ffffff", current)
        fg = self._mix_color("#ffffff", "#000000", current)

        try:
            button.config(
                bg=bg,
                fg=fg,
                activebackground=bg,
                activeforeground=fg
            )
            self._update_button_text_image(button, fg)
        except tk.TclError:
            return

        if current != target:
            self.after(
                16,
                lambda b=button: self._animate_hover(b)
            )

    def panel(self, parent):
        return tk.Frame(parent, bg=self.PANEL, bd=3, relief="sunken")

    def clear_content(self):
        for child in self.content.winfo_children():
            child.destroy()

    def top_title(self, parent, text):
        label = tk.Label(
            parent,
            bg=self.BG,
            fg=self.TEXT,
            anchor="w"
        )
        self._set_pixel_label_text(
            label,
            text,
            20,
            self.TEXT,
            align="left"
        )
        label.pack(fill="x", pady=(0, 10))

    def back_bar(self, parent, save_command=None):
        row = tk.Frame(parent, bg=self.BG)
        row.pack(fill="x", pady=(12, 0))
        self.beveled_button(row, "Back", self.back_to_game).pack(side="left")
        if save_command:
            self.beveled_button(row, "Save", save_command, bg=self.GREEN).pack(side="right")

    def navigate(self, callback, *args):
        page_key = (
            getattr(callback, "__name__", repr(callback)),
            tuple(str(arg) for arg in args)
        )

        # Once a page has been built before, its repeated text/assets are
        # already hot in the raster caches.  Rebuild it directly instead of
        # flashing a loading screen again.
        if page_key in self._visited_navigation_keys:
            if self._loading_job is not None:
                try:
                    self.after_cancel(self._loading_job)
                except Exception:
                    pass
                self._loading_job = None
            callback(*args)
            return

        # First visit: keep the loading page because some screens still need
        # genuine discovery/layout work. Paint it immediately, then start the
        # build on the next event-loop turn without the old fixed 80 ms delay.
        self.clear_content()
        self.current_screen = "loading"

        holder = tk.Frame(self.content, bg=self.BG)
        holder.pack(fill="both", expand=True)

        self._loading_label = tk.Label(
            holder,
            bg=self.BG,
            fg=self.TEXT
        )
        self._loading_label.place(
            relx=0.5,
            rely=0.5,
            anchor="center"
        )

        self._loading_frame = 0
        self._tick_loading()

        try:
            self.update_idletasks()
        except tk.TclError:
            pass

        self.after(
            1,
            lambda: self._finish_navigation(callback, args, page_key)
        )

    def _tick_loading(self):
        if self.current_screen != "loading":
            return

        frames = [
            "LOADING",
            "LOADING.",
            "LOADING..",
            "LOADING..."
        ]

        self._set_pixel_label_text(
            self._loading_label,
            frames[self._loading_frame % len(frames)],
            16,
            self.TEXT,
            align="center"
        )

        self._loading_frame += 1
        self._loading_job = self.after(
            130,
            self._tick_loading
        )

    def _finish_navigation(self, callback, args, page_key=None):
        if self._loading_job is not None:
            try:
                self.after_cancel(self._loading_job)
            except Exception:
                pass
            self._loading_job = None

        callback(*args)
        if page_key is not None:
            self._visited_navigation_keys.add(page_key)

    # ---------- shell ----------

    def _build_shell(self):
        self.grid_rowconfigure(0, weight=1)
        self.grid_columnconfigure(0, weight=1)

        self.main_pane = tk.PanedWindow(
            self,
            orient="horizontal",
            sashwidth=8,
            sashrelief="raised",
            bg=self.PANEL_2,
            bd=0,
            showhandle=False
        )
        self.main_pane.grid(row=0, column=0, sticky="nsew")

        sidebar = tk.Frame(self.main_pane, bg=self.PANEL_2, bd=3, relief="raised", width=225)
        self.main_pane.add(sidebar, minsize=170, width=225)

        brand = tk.Frame(sidebar, bg=self.BLACK, bd=3, relief="sunken", height=68)
        brand.pack(fill="x", padx=8, pady=(8, 12))
        brand.pack_propagate(False)

        brand_label = tk.Label(
            brand,
            bg=self.BLACK,
            fg="white"
        )
        self._set_pixel_label_text(
            brand_label,
            "SML",
            24,
            "white",
            align="center"
        )
        brand_label.pack(
            expand=True
        )


        self.game_buttons = {}
        game_specs = [
            ("Java Edition", "Java Edition", self.PANEL_3),
            ("Bedrock", "Bedrock Edition", self.PANEL_3),
            ("Dungeons", "Dungeons", "#b96718"),
            ("Dungeons II", "Dungeons II", "#168d89"),
            ("Legends", "Legends", "#1aaed0"),
        ]
        for game, button_label, button_bg in game_specs:
            b = self.beveled_button(
                sidebar,
                button_label,
                lambda g=game: self.navigate(self.show_game, g),
                anchor="w",
                bg=button_bg
            )
            b.pack(fill="x", padx=10, pady=4)
            b._game_base_bg = button_bg
            self.game_buttons[game] = b

        tk.Frame(sidebar, bg=self.PANEL_2).pack(fill="both", expand=True)

        self.accounts_button = self.beveled_button(
            sidebar,
            "Accounts",
            lambda: self.navigate(self.show_accounts_screen),
            anchor="w"
        )
        self.accounts_button.pack(
            fill="x",
            padx=10,
            pady=4
        )

        self.settings_button = self.beveled_button(
            sidebar,
            "Settings",
            lambda: self.navigate(self.show_settings_screen),
            anchor="w"
        )
        self.settings_button.pack(
            fill="x",
            padx=10,
            pady=4
        )

        self.log_button = self.beveled_button(
            sidebar,
            "Log",
            lambda: self.navigate(self.show_log_screen),
            anchor="w"
        )
        self.log_button.pack(
            fill="x",
            padx=10,
            pady=4
        )

        self.refresh_button = self.beveled_button(
            sidebar,
            "Refresh",
            self.refresh_all,
            anchor="w"
        )
        self.refresh_button.pack(
            fill="x",
            padx=10,
            pady=4
        )

        self.about_button = self.beveled_button(
            sidebar,
            "About",
            lambda: self.navigate(self.show_about_screen),
            anchor="w"
        )
        self.about_button.pack(
            fill="x",
            padx=10,
            pady=(4, 10)
        )

        content_host = tk.Frame(self.main_pane, bg=self.BG)
        self.main_pane.add(content_host, minsize=520)

        self.content = tk.Frame(content_host, bg=self.BG)
        self.content.pack(fill="both", expand=True, padx=12, pady=12)

    # ---------- game title ----------

    def set_game_title(self, parent, game):
        """
        Draw the selected game name as a large hard-edged title.
        """
        title = GAME_DISPLAY_TITLES.get(game, game)

        # Three layers: dark depth, mid-tone edge, then bright face.
        layers = [
            (6, 6, "#242424"),
            (3, 3, "#666666"),
            (0, 0, self.TEXT),
        ]

        refs = []

        for dx, dy, color in layers:
            label = tk.Label(
                parent,
                bg=self.PANEL,
                bd=0,
                highlightthickness=0
            )

            photo = self._hard_text_photo(
                title,
                36,
                color,
                align="center"
            )

            if photo is not None:
                label._text_photo = photo
                label.config(
                    image=photo,
                    text=""
                )
                refs.append(photo)
            else:
                label.config(
                    text=title,
                    fg=color,
                    font=(self.ui_font, 28, "bold")
                )

            label.place(
                relx=.5,
                rely=.5,
                x=dx,
                y=dy,
                anchor="center"
            )

        parent._game_title_refs = refs


    def get_installations(self):
        raw = self.installations_data.get("installations", [])
        cleaned = []

        for item in raw:
            normalized = normalize_installation(item)
            if normalized is not None:
                cleaned.append(normalized)

        self.installations_data["installations"] = cleaned
        return cleaned

    def save_installations(self):
        save_installations_file(self.installations_data)


    def installation_items(self):
        items = [{
            "label": "New Installation",
            "value": "__new_installation__",
            "actions": [],
            "row_type": "button",
            "keep_open": True,
        }]

        for installation in self.get_installations():
            name = installation["name"]

            items.append({
                "label": name,
                "value": name,
                "actions": [{
                    "label": "EDIT",
                    "command": lambda n=name: self.edit_installation(n)
                }],
            })

        return items

    def selected_installation_data(self):
        installs = self.get_installations()

        if not installs:
            return {
                "name": "",
                "version": ""
            }

        selected = self.config_data.get(
            "selected_installation",
            ""
        )

        for installation in installs:
            if installation["name"] == selected:
                return installation

        return installs[0]


    def _installation_changed(self, value):
        if value == "__new_installation__":
            self.create_installation()
            return

        self.config_data["selected_installation"] = value

        installation = self.selected_installation_data()
        version = installation.get("version", "")

        if version and hasattr(self, "version_dropdown"):
            self.version_dropdown.set(version, notify=False)

        save_config(self.config_data)

        dropdown = getattr(
            self,
            "installation_dropdown",
            None
        )
        if dropdown is not None:
            dropdown.close()


    def _version_changed(self, value):
        self.config_data["selected_java_version"] = value

        selected = self.config_data.get("selected_installation", "")
        for installation in self.get_installations():
            if installation["name"] == selected:
                installation["version"] = value
                break

        save_config(self.config_data)
        self.save_installations()

        if value:
            version_modstorage_dir(value)


    def create_installation(self):
        base = "New Installation"
        installations = self.get_installations()
        existing = {item["name"] for item in installations}

        name = base
        number = 2
        while name in existing:
            name = f"{base} {number}"
            number += 1

        current_version = ""
        if hasattr(self, "version_dropdown"):
            current_version = self.version_dropdown.get()

        installations.append({
            "name": name,
            "version": current_version,
            "vanilla": True,
            "mods": []
        })

        self.installations_data["installations"] = installations
        self.config_data["selected_installation"] = name

        self.save_installations()
        save_config(self.config_data)

        if current_version:
            version_modstorage_dir(current_version)

        dropdown = getattr(self, "installation_dropdown", None)

        if dropdown is not None:
            was_open = bool(
                dropdown.popup
                and dropdown.popup.winfo_exists()
            )

            dropdown.set_items(self.installation_items())
            dropdown.set(name, notify=False)

            if was_open:
                dropdown.close()
                self.after(1, dropdown.open)
        else:
            self.after(1, lambda: self.show_game("Java Edition"))


    def edit_installation(self, name):
        self.current_screen = "installation_edit"
        self.update_navigation_button_states()
        self.show_inline_notice(
            "Installation",
            "Placeholder",
            back_command=lambda: self.navigate(
                self.show_game,
                "Java Edition"
            )
        )

    # ---------- game screen ----------

    def update_navigation_button_states(self):
        """
        Disable the button for the page/game that is currently open.
        Disabled controls keep SML's solid-gray appearance and have no hover.
        """
        page_buttons = {
            "accounts": getattr(self, "accounts_button", None),
            "settings": getattr(self, "settings_button", None),
            "log": getattr(self, "log_button", None),
            "about": getattr(self, "about_button", None),
        }

        for page_name, button in page_buttons.items():
            if button is None:
                continue

            self.set_button_enabled(
                button,
                self.current_screen != page_name,
                tooltip=(
                    "You are already on this page."
                    if self.current_screen == page_name
                    else ""
                )
            )

        # Game buttons are disabled when that exact game page is open.
        for game_name, button in getattr(
            self,
            "game_buttons",
            {}
        ).items():
            active = (
                self.current_screen == "game"
                and self.selected_game == game_name
            )

            self.set_button_enabled(
                button,
                not active,
                tooltip=(
                    "You are already on this game page."
                    if active
                    else ""
                )
            )


    def show_game(self, game=None):
        if game:
            self.selected_game = game

        game = self.selected_game
        self.current_screen = "game"
        self.update_navigation_button_states()
        self.clear_content()

        # Keep the affiliation notice outside the launch panel while reserving
        # its space at the bottom of every game's main page.  Packing this first
        # makes it sit directly below the Play panel.
        affiliation_label = tk.Label(
            self.content,
            bg=self.BG,
            fg=self.MUTED
        )
        self._set_pixel_label_text(
            affiliation_label,
            "Not affiliated with Mojang/Microsoft",
            7,
            self.MUTED,
            align="left"
        )
        affiliation_label.pack(
            side="bottom",
            fill="x",
            anchor="w",
            padx=2,
            pady=(5, 0)
        )

        # Reserve the bottom launch bar before the rest of the game page.
        # This prevents the Java options panel from pushing it below the visible
        # client area.
        play_bar = tk.Frame(
            self.content,
            bg=self.PANEL_2,
            bd=3,
            relief="raised"
        )
        play_bar.pack(
            side="bottom",
            fill="x"
        )

        self.play_button = self.beveled_button(
            play_bar,
            "Play",
            self.play_selected,
            bg=self.GREEN,
            font_size=17
        )
        self.play_button.pack(
            fill="x",
            padx=8,
            pady=8,
            ipady=8
        )

        # Game-management tabs.
        top_tools = tk.Frame(
            self.content,
            bg=self.PANEL_2,
            bd=3,
            relief="raised"
        )
        top_tools.pack(
            side="top",
            fill="x",
            pady=(0, 9)
        )

        tools_inner = tk.Frame(
            top_tools,
            bg=self.PANEL_2
        )
        tools_inner.pack(
            fill="x",
            padx=7,
            pady=7
        )

        self.current_tool_buttons = []

        for label_text, action in GAME_TOOLS.get(
            game,
            []
        ):
            button = self.beveled_button(
                tools_inner,
                label_text,
                lambda a=action: self.run_tool(a),
                font_size=9
            )
            button.pack(
                side="left",
                padx=(0, 6)
            )
            self.current_tool_buttons.append(
                button
            )

        # Game title / account / installation panel.
        edition = self.panel(
            self.content
        )
        edition.pack(
            side="top",
            fill="x",
            pady=(0, 9)
        )

        title_box = tk.Frame(
            edition,
            bg=self.PANEL,
            height=118
        )
        title_box.pack(
            fill="x",
            padx=18,
            pady=(10, 0)
        )
        title_box.pack_propagate(False)

        self.set_game_title(
            title_box,
            game
        )

        controls = tk.Frame(
            edition,
            bg=self.PANEL
        )
        controls.pack(
            pady=(0, 12)
        )

        self.account_dropdown = CustomDropdown(
            controls,
            self,
            command=self._account_changed_custom,
            placeholder="Select account",
            tooltip="Select which Microsoft account this game should use."
        )
        self.account_dropdown.pack(
            side="left",
            padx=(0, 8)
            if game == "Java Edition"
            else 0
        )

        self.installation_dropdown = None

        if game == "Java Edition":
            installations = self.get_installations()

            if installations:
                selected = self.config_data.get(
                    "selected_installation",
                    ""
                )

                valid_names = {
                    installation["name"]
                    for installation in installations
                }

                if selected not in valid_names:
                    selected = installations[0]["name"]
                    self.config_data[
                        "selected_installation"
                    ] = selected
                    save_config(
                        self.config_data
                    )

                self.installation_dropdown = CustomDropdown(
                    controls,
                    self,
                    items=self.installation_items(),
                    value=selected,
                    command=self._installation_changed,
                    placeholder="Select installation",
                    tooltip="Choose a Java installation profile."
                )
                self.installation_dropdown.pack(
                    side="left"
                )
            else:
                self.new_installation_button = self.beveled_button(
                    controls,
                    "New Installation",
                    self.create_installation,
                    tooltip="Create your first Java installation profile."
                )
                self.new_installation_button.pack(
                    side="left"
                )

        # Main options panel. This is intentionally created for every game;
        # Java populates it with Version and Mods.
        self.options_panel = self.panel(
            self.content
        )
        self.options_panel.pack(
            side="top",
            fill="both",
            expand=True,
            pady=(0, 9)
        )

        options_inner = tk.Frame(
            self.options_panel,
            bg=self.PANEL
        )
        options_inner.pack(
            fill="both",
            expand=True,
            padx=16,
            pady=16
        )

        if game == "Java Edition":
            filter_row = tk.Frame(
                options_inner,
                bg=self.PANEL
            )
            filter_row.pack(
                fill="x",
                anchor="n",
                pady=(0, 12)
            )

            filter_label = tk.Label(
                filter_row,
                bg=self.PANEL,
                fg=self.TEXT
            )
            self._set_pixel_label_text(
                filter_label,
                "SHOW",
                10,
                self.TEXT
            )
            filter_label.pack(
                side="left",
                padx=(0, 14)
            )

            default_filters = {
                "Releases": True,
                "Release Candidates": True,
                "Pre-Releases": True,
                "Snapshots": True,
                "Mod Loaders": True,
                "Alpha": True,
                "Beta": True,
                "Classic": True,
                "Misc": True,
            }

            stored_filters = self.get_page_state(
                "java",
                "version_filters",
                default_filters
            )

            if not isinstance(
                stored_filters,
                dict
            ):
                stored_filters = dict(
                    default_filters
                )

            self.version_filter_widgets = {}

            for category in (
                "Releases",
                "Release Candidates",
                "Pre-Releases",
                "Snapshots",
                "Mod Loaders",
                "Alpha",
                "Beta",
                "Classic",
                "Misc",
            ):
                checkbox = PixelCheckbox(
                    filter_row,
                    self,
                    category,
                    value=bool(
                        stored_filters.get(
                            category,
                            True
                        )
                    ),
                    command=lambda checked, c=category: self._version_filter_changed(
                        c,
                        checked
                    )
                )
                checkbox.pack(
                    side="left",
                    padx=(0, 7)
                )
                self.version_filter_widgets[
                    category
                ] = checkbox

            version_row = tk.Frame(
                options_inner,
                bg=self.PANEL
            )
            version_row.pack(
                fill="x",
                anchor="n"
            )

            version_label = tk.Label(
                version_row,
                bg=self.PANEL,
                fg=self.TEXT
            )
            self._set_pixel_label_text(
                version_label,
                "VERSION",
                10,
                self.TEXT
            )
            version_label.pack(
                side="left",
                padx=(0, 14)
            )

            self.version_dropdown = CustomDropdown(
                version_row,
                self,
                command=self._version_changed,
                placeholder="Select version",
                tooltip="Choose the Minecraft version used by this installation."
            )
            self.version_dropdown.pack(
                side="left"
            )

            mods_row = tk.Frame(
                options_inner,
                bg=self.PANEL
            )
            mods_row.pack(
                fill="x",
                anchor="n",
                pady=(12, 0)
            )

            mods_label = tk.Label(
                mods_row,
                bg=self.PANEL,
                fg=self.TEXT
            )
            self._set_pixel_label_text(
                mods_label,
                "MODS",
                10,
                self.TEXT
            )
            mods_label.pack(
                side="left",
                padx=(0, 14)
            )

            self.edit_mods_button = self.beveled_button(
                mods_row,
                "Edit Mods",
                lambda: self.navigate(
                    self.show_mods_page
                ),
                font_size=9,
                tooltip="Choose which downloaded mods this installation uses."
            )
            self.edit_mods_button.pack(
                side="left"
            )

            selected_installation = self.selected_installation_data()
            selected_installation_mods = selected_installation.get(
                "mods",
                []
            )

            installation_mod_count = len(
                selected_installation_mods
                if isinstance(
                    selected_installation_mods,
                    list
                )
                else []
            )

            self.list_installation_mods_button = self.beveled_button(
                mods_row,
                f"List Installation Mods ({installation_mod_count})",
                lambda: self.navigate(
                    self.show_installation_mods_page
                ),
                font_size=9,
                tooltip="List every mod enabled for the selected installation."
            )
            self.list_installation_mods_button.pack(
                side="left",
                padx=(8, 0)
            )

        self.refresh_accounts()
        self.refresh_account_display_names()

        if game == "Java Edition":
            self.refresh_versions()
            self.update_mod_button_state()

        self.update_game_status()


    def refresh_account_display_names(self):
        accounts = self._ordered_accounts(
            self.auth.accounts()
        )

        if not accounts:
            return

        profile_cache = self._account_profile_cache()

        for account in accounts:
            hid = self._account_id(
                account
            )

            cached = profile_cache.get(
                hid,
                {}
            )

            if isinstance(
                cached,
                dict
            ):
                gamertag = str(
                    cached.get(
                        "gamertag",
                        ""
                    )
                ).strip()

                java_name = str(
                    cached.get(
                        "java_name",
                        ""
                    )
                ).strip()

                if gamertag:
                    self._cached_gamertags_by_hid[
                        hid
                    ] = gamertag

                if java_name:
                    self._cached_java_names_by_hid[
                        hid
                    ] = java_name

        if (
            self.current_screen == "game"
            and hasattr(
                self,
                "account_dropdown"
            )
        ):
            self.refresh_accounts()


    def update_mod_button_state(self):
        edit_button = getattr(
            self,
            "edit_mods_button",
            None
        )
        list_button = getattr(
            self,
            "list_installation_mods_button",
            None
        )

        installation = self.selected_installation_data()
        version = installation.get("version", "")
        account = self.config_data.get("selected_account", "")
        installation_name = installation.get("name", "")

        if edit_button is not None:
            if not installation_name:
                self.set_button_enabled(
                    edit_button,
                    False,
                    tooltip="Create or select an installation before editing mods."
                )
            elif not account:
                self.set_button_enabled(
                    edit_button,
                    False,
                    tooltip="Add and select a Microsoft account before editing mods."
                )
            elif not version:
                self.set_button_enabled(
                    edit_button,
                    False,
                    tooltip="Select a Minecraft version before editing mods."
                )
            else:
                self.set_button_enabled(
                    edit_button,
                    True,
                    tooltip="Choose downloaded mods or install compatible mods from Modrinth."
                )

        if list_button is not None:
            if not installation_name:
                self.set_button_enabled(
                    list_button,
                    False,
                    tooltip="Create or select an installation before listing its mods."
                )
            elif not version:
                self.set_button_enabled(
                    list_button,
                    False,
                    tooltip="Select a Minecraft version before listing its mods."
                )
            else:
                self.set_button_enabled(
                    list_button,
                    True,
                    tooltip="List every mod enabled for the selected installation."
                )


    def _toggle_installation_mod(self, filename):
        installation = self.selected_installation_data()

        if not installation.get("name"):
            return

        mods = installation.get("mods", [])
        if not isinstance(mods, list):
            mods = []

        if filename in mods:
            mods.remove(filename)
        else:
            mods.append(filename)

        installation["mods"] = mods
        installation["vanilla"] = len(mods) == 0

        self.save_installations()
        self.show_mods_page()

    def _mod_page_header(self, parent, text):
        label = tk.Label(
            parent,
            bg=self.PANEL,
            fg=self.TEXT
        )
        self._set_pixel_label_text(
            label,
            text,
            10,
            self.TEXT
        )
        label.pack(
            anchor="w",
            padx=12,
            pady=(10, 8)
        )

    def _make_scrollable_panel(self, parent):
        body = tk.Frame(
            parent,
            bg=self.PANEL
        )
        body.pack(
            fill="both",
            expand=True,
            padx=8,
            pady=(0, 8)
        )

        canvas = tk.Canvas(
            body,
            bg=self.PANEL,
            bd=0,
            highlightthickness=0
        )
        canvas.pack(
            side="left",
            fill="both",
            expand=True
        )

        scrollbar = PixelScrollbar(
            body,
            command=canvas.yview,
            width=14,
            launcher=self
        )
        scrollbar.pack(
            side="right",
            fill="y"
        )

        canvas.configure(
            yscrollcommand=scrollbar.set
        )

        inner = tk.Frame(
            canvas,
            bg=self.PANEL
        )

        window_id = canvas.create_window(
            (0, 0),
            window=inner,
            anchor="nw"
        )

        inner.bind(
            "<Configure>",
            lambda e: canvas.configure(
                scrollregion=canvas.bbox("all")
            )
        )

        canvas.bind(
            "<Configure>",
            lambda e: canvas.itemconfigure(
                window_id,
                width=e.width
            )
        )

        def wheel(event):
            if getattr(event, "delta", 0):
                direction = -1 if event.delta > 0 else 1
            elif getattr(event, "num", None) == 4:
                direction = -1
            else:
                direction = 1

            canvas.yview_scroll(
                direction,
                "units"
            )
            return "break"

        def bind_recursive(widget):
            widget.bind(
                "<MouseWheel>",
                wheel,
                add="+"
            )
            widget.bind(
                "<Button-4>",
                wheel,
                add="+"
            )
            widget.bind(
                "<Button-5>",
                wheel,
                add="+"
            )

            for child in widget.winfo_children():
                bind_recursive(child)

        inner._sml_bind_wheel = bind_recursive
        return inner

    def show_installation_mods_page(self):
        installation = self.selected_installation_data()
        installation_name = installation.get("name", "")
        installation_version = installation.get("version", "")

        if not installation_name or not installation_version:
            self.show_game("Java Edition")
            return

        self.current_screen = "installation_mods"
        self.update_navigation_button_states()
        self.clear_content()

        ensure_modref_for_storage()

        selected_mods = installation.get(
            "mods",
            []
        )
        if not isinstance(
            selected_mods,
            list
        ):
            selected_mods = []

        entries = []

        for filename in selected_mods:
            metadata = find_modref(
                installation_version,
                filename
            ) or {}

            display_name = str(
                metadata.get("display_name")
                or _fallback_mod_display_name(
                    filename
                )
            )

            entries.append({
                "display_name": display_name,
                "filename": str(filename),
            })

        entries.sort(
            key=lambda item: (
                item["display_name"].casefold(),
                item["filename"].casefold()
            )
        )

        self.top_title(
            self.content,
            f"INSTALLATION MODS - {installation_name}"
        )

        panel = self.panel(
            self.content
        )
        panel.pack(
            fill="both",
            expand=True
        )

        total = len(entries)
        count_text = (
            "1 total mod"
            if total == 1
            else f"{total} total mods"
        )

        count_label = tk.Label(
            panel,
            bg=self.PANEL,
            fg=self.TEXT,
            anchor="w"
        )
        self._set_pixel_label_text(
            count_label,
            count_text,
            10,
            self.TEXT
        )
        count_label.pack(
            anchor="w",
            padx=14,
            pady=(14, 10)
        )

        table_outer = tk.Frame(
            panel,
            bg=self.PANEL_3,
            bd=3,
            relief="sunken"
        )
        table_outer.pack(
            fill="both",
            expand=True,
            padx=14,
            pady=(0, 14)
        )

        self.installation_mod_columns = {}

        default_widths = {
            "#": 70,
            "Mod Name": 300,
            "JAR File": 430,
        }

        saved_widths = self.get_page_state(
            "installation_mods",
            "column_widths",
            {}
        )

        self.installation_mod_column_widths = dict(
            default_widths
        )

        if isinstance(
            saved_widths,
            dict
        ):
            for title in default_widths:
                try:
                    value = int(
                        saved_widths.get(
                            title,
                            default_widths[title]
                        )
                    )
                except Exception:
                    value = default_widths[title]

                self.installation_mod_column_widths[
                    title
                ] = max(
                    55,
                    value
                )

        self.installation_mod_column_min_widths = {
            "#": max(
                55,
                self._account_text_width("#") + 28
            ),
            "Mod Name": max(
                130,
                self._account_text_width(
                    "Mod Name"
                ) + 28
            ),
            "JAR File": max(
                130,
                self._account_text_width(
                    "JAR File"
                ) + 28
            ),
        }

        header = tk.Frame(
            table_outer,
            bg=self.PANEL_2,
            height=36
        )
        header.pack(
            fill="x"
        )
        header.pack_propagate(
            False
        )

        body = tk.Frame(
            table_outer,
            bg=self.PANEL_2
        )
        body.pack(
            fill="both",
            expand=True
        )

        column_titles = [
            "#",
            "Mod Name",
            "JAR File",
        ]

        for index, title in enumerate(
            column_titles
        ):
            width = self.installation_mod_column_widths[
                title
            ]

            header_frame = tk.Frame(
                header,
                bg=self.PANEL_2,
                width=width,
                height=36
            )
            header_frame.pack(
                side="left",
                fill="y"
            )
            header_frame.pack_propagate(
                False
            )

            header_label = tk.Label(
                header_frame,
                bg=self.PANEL_2,
                fg=self.TEXT,
                anchor="w",
                justify="left"
            )
            self._set_pixel_label_text(
                header_label,
                title,
                9,
                self.TEXT,
                align="left"
            )
            header_label.pack(
                fill="both",
                expand=True,
                padx=(8, 7)
            )

            column_body = tk.Frame(
                body,
                bg=self.PANEL_2,
                width=width,
                bd=0,
                highlightthickness=0
            )
            column_body.pack(
                side="left",
                fill="y"
            )
            column_body.pack_propagate(
                False
            )

            self.installation_mod_columns[
                title
            ] = {
                "header": header_frame,
                "header_label": header_label,
                "body": column_body,
            }

            # Exactly like the Accounts table: resize handles exist only
            # between header labels, never as full-height separators.
            if index < len(column_titles) - 1:
                handle = tk.Frame(
                    header_frame,
                    bg="#565656",
                    width=6,
                    cursor="sb_h_double_arrow"
                )
                handle.place(
                    relx=1.0,
                    rely=0,
                    relheight=1.0,
                    anchor="ne"
                )

                handle.bind(
                    "<Button-1>",
                    lambda e, t=title: self._begin_installation_mod_column_resize(
                        e,
                        t
                    )
                )
                handle.bind(
                    "<B1-Motion>",
                    lambda e, t=title: self._drag_installation_mod_column_resize(
                        e,
                        t
                    )
                )

        for row_index, entry in enumerate(
            entries,
            start=1
        ):
            values = {
                "#": f"{row_index}.",
                "Mod Name": entry[
                    "display_name"
                ],
                "JAR File": entry[
                    "filename"
                ],
            }

            for title in column_titles:
                column = self.installation_mod_columns[
                    title
                ]["body"]

                cell = tk.Frame(
                    column,
                    bg=self.PANEL_2,
                    height=36,
                    bd=0,
                    highlightthickness=0
                )
                cell.pack(
                    fill="x",
                    padx=0,
                    pady=1
                )
                cell.pack_propagate(
                    False
                )

                label = tk.Label(
                    cell,
                    bg=self.PANEL_2,
                    fg=(
                        self.MUTED
                        if title == "#"
                        else self.TEXT
                    ),
                    anchor="w"
                )

                max_width = max(
                    40,
                    self.installation_mod_column_widths[
                        title
                    ] - 14
                )

                self._set_pixel_label_text(
                    label,
                    values[title],
                    9,
                    (
                        self.MUTED
                        if title == "#"
                        else self.TEXT
                    ),
                    max_width=max_width,
                    align="left"
                )
                label.pack(
                    fill="both",
                    expand=True,
                    padx=7
                )

        bottom = tk.Frame(
            self.content,
            bg=self.BG
        )
        bottom.pack(
            fill="x",
            pady=(10, 0)
        )

        self.beveled_button(
            bottom,
            "Back",
            lambda: self.navigate(
                self.show_game,
                "Java Edition"
            )
        ).pack(
            side="left"
        )


    def _begin_installation_mod_column_resize(
        self,
        event,
        title
    ):
        self._installation_mod_resize_title = title
        self._installation_mod_resize_start_x = (
            event.x_root
        )
        self._installation_mod_resize_start_width = (
            self.installation_mod_column_widths.get(
                title,
                200
            )
        )


    def _drag_installation_mod_column_resize(
        self,
        event,
        title
    ):
        if getattr(
            self,
            "_installation_mod_resize_title",
            None
        ) != title:
            return

        delta = (
            event.x_root
            - self._installation_mod_resize_start_x
        )

        minimum = (
            self.installation_mod_column_min_widths.get(
                title,
                80
            )
        )

        new_width = max(
            minimum,
            self._installation_mod_resize_start_width
            + delta
        )

        self.installation_mod_column_widths[
            title
        ] = new_width

        column = self.installation_mod_columns.get(
            title
        )

        if not column:
            return

        column["header"].config(
            width=new_width
        )
        column["body"].config(
            width=new_width
        )

        # Column headers remain one line regardless of width.
        self._set_pixel_label_text(
            column["header_label"],
            title,
            9,
            self.TEXT,
            align="left"
        )

        self.set_page_state(
            "installation_mods",
            "column_widths",
            dict(
                self.installation_mod_column_widths
            )
        )



    def show_mods_page(self):
        ensure_modref_for_storage()

        installation = self.selected_installation_data()
        version = installation.get("version", "")
        account = self.config_data.get("selected_account", "")

        if not installation.get("name") or not version or not account:
            self.show_game("Java Edition")
            return

        self.current_screen = "mods"
        self.update_navigation_button_states()
        self.clear_content()

        self.top_title(
            self.content,
            f"MODS - {installation.get('name', '')}"
        )

        main = tk.Frame(
            self.content,
            bg=self.BG
        )
        main.pack(
            fill="both",
            expand=True
        )
        main.grid_columnconfigure(
            0,
            weight=1,
            uniform="mods"
        )
        main.grid_columnconfigure(
            1,
            weight=1,
            uniform="mods"
        )
        main.grid_rowconfigure(
            0,
            weight=1
        )

        # ---------------- left: local mod toggles ----------------
        local_panel = self.panel(main)
        local_panel.grid(
            row=0,
            column=0,
            sticky="nsew",
            padx=(0, 5)
        )

        self._mod_page_header(
            local_panel,
            "DOWNLOADED MODS"
        )

        local_inner = self._make_scrollable_panel(
            local_panel
        )

        storage = version_modstorage_dir(
            version
        )

        jar_files = [
            path.name
            for path in storage.iterdir()
            if path.is_file()
            and path.suffix.lower() == ".jar"
        ]

        mod_rows = []

        for filename in jar_files:
            metadata = find_modref(
                version,
                filename
            ) or {}

            display_name = str(
                metadata.get(
                    "display_name",
                    ""
                )
                or _fallback_mod_display_name(
                    filename
                )
            )

            mod_rows.append(
                (
                    display_name,
                    filename
                )
            )

        mod_rows.sort(
            key=lambda item: (
                item[0].casefold(),
                item[1].casefold()
            )
        )

        selected = set(
            installation.get(
                "mods",
                []
            )
        )

        if not mod_rows:
            empty = tk.Label(
                local_inner,
                bg=self.PANEL,
                fg=self.MUTED,
                text="No mods downloaded for this version."
            )
            empty.pack(
                anchor="w",
                padx=8,
                pady=8
            )
        else:
            for display_name, filename in mod_rows:
                row = tk.Frame(
                    local_inner,
                    bg=self.PANEL_2,
                    height=34
                )
                row.pack(
                    fill="x",
                    padx=4,
                    pady=2
                )
                row.pack_propagate(False)

                name_label = tk.Label(
                    row,
                    bg=self.PANEL_2,
                    fg=self.TEXT,
                    anchor="w"
                )
                self._set_pixel_label_text(
                    name_label,
                    display_name,
                    9,
                    self.TEXT,
                    max_width=300
                )

                Tooltip(
                    name_label,
                    filename,
                    launcher=self
                )
                name_label.pack(
                    side="left",
                    fill="x",
                    expand=True,
                    padx=7
                )

                enabled = filename in selected

                toggle = self.beveled_button(
                    row,
                    "ON" if enabled else "OFF",
                    lambda f=filename: self._toggle_installation_mod(f),
                    bg=self.GREEN if enabled else self.PANEL_3,
                    font_size=8,
                    tooltip=(
                        "Remove this mod from the installation."
                        if enabled
                        else "Include this mod in the installation."
                    )
                )

                # Keep ON and OFF controls exactly the same physical width.
                on_photo = self._hard_text_photo(
                    "ON",
                    8,
                    self.TEXT,
                    max_width=200
                )
                off_photo = self._hard_text_photo(
                    "OFF",
                    8,
                    self.TEXT,
                    max_width=200
                )
                toggle_width = max(
                    on_photo.width() if on_photo is not None else 32,
                    off_photo.width() if off_photo is not None else 40
                ) + 20
                toggle.config(
                    width=toggle_width
                )

                toggle.pack(
                    side="right",
                    padx=4,
                    pady=2
                )

        if hasattr(local_inner, "_sml_bind_wheel"):
            local_inner._sml_bind_wheel(local_inner)

        # ---------------- right: Modrinth ----------------
        remote_panel = self.panel(main)
        remote_panel.grid(
            row=0,
            column=1,
            sticky="nsew",
            padx=(5, 0)
        )

        self._mod_page_header(
            remote_panel,
            "MODRINTH"
        )

        search_row = tk.Frame(
            remote_panel,
            bg=self.PANEL
        )
        search_row.pack(
            fill="x",
            padx=8,
            pady=(0, 8)
        )

        self.modrinth_query = tk.StringVar()

        search_entry = tk.Entry(
            search_row,
            textvariable=self.modrinth_query,
            bg=self.PANEL_3,
            fg=self.TEXT,
            insertbackground=self.TEXT,
            relief="sunken",
            bd=3,
            font=(self.ui_font, 10)
        )
        search_entry.pack(
            side="left",
            fill="x",
            expand=True
        )

        search_button = self.beveled_button(
            search_row,
            "Search",
            self.search_modrinth_from_page,
            font_size=9,
            tooltip="Search Modrinth for mods compatible with this Minecraft version."
        )
        search_button.pack(
            side="left",
            padx=(6, 0)
        )

        self.modrinth_results_holder = self._make_scrollable_panel(
            remote_panel
        )

        hint = tk.Label(
            self.modrinth_results_holder,
            bg=self.PANEL,
            fg=self.MUTED,
            text=(
                "Search Modrinth for compatible mods.\n"
                "Downloaded JARs are stored in modstorage for this version."
            ),
            justify="left"
        )
        hint.pack(
            anchor="w",
            padx=8,
            pady=8
        )

        if hasattr(self.modrinth_results_holder, "_sml_bind_wheel"):
            self.modrinth_results_holder._sml_bind_wheel(
                self.modrinth_results_holder
            )

        bottom = tk.Frame(
            self.content,
            bg=self.BG
        )
        bottom.pack(
            fill="x",
            pady=(10, 0)
        )

        self.beveled_button(
            bottom,
            "Back",
            lambda: self.navigate(
                self.show_game,
                "Java Edition"
            )
        ).pack(
            side="left"
        )

    def search_modrinth_from_page(self):
        query = self.modrinth_query.get().strip()

        if not query:
            return

        holder = self.modrinth_results_holder

        for child in holder.winfo_children():
            child.destroy()

        loading = tk.Label(
            holder,
            bg=self.PANEL,
            fg=self.TEXT,
            text="Searching..."
        )
        loading.pack(
            anchor="w",
            padx=8,
            pady=8
        )

        installation = self.selected_installation_data()
        installation_version = installation.get(
            "version",
            ""
        )
        game_version = minecraft_game_version_from_installation_version(
            installation_version
        )

        def worker():
            try:
                hits = modrinth_search(
                    query,
                    game_version,
                    limit=25
                )
                self.dispatch_to_ui(
                    lambda h=hits: self._render_modrinth_results(
                        h
                    )
                )
            except Exception as exc:
                message = str(exc)
                self.dispatch_to_ui(
                    lambda m=message: self._render_modrinth_error(
                        m
                    )
                )

        threading.Thread(
            target=worker,
            daemon=True
        ).start()

    def _render_modrinth_error(self, message):
        holder = self.modrinth_results_holder

        for child in holder.winfo_children():
            child.destroy()

        label = tk.Label(
            holder,
            bg=self.PANEL,
            fg=self.TEXT,
            text=f"Modrinth search failed:\n{message}",
            justify="left",
            wraplength=360
        )
        label.pack(
            anchor="w",
            padx=8,
            pady=8
        )

    def _render_modrinth_results(self, hits):
        holder = self.modrinth_results_holder

        for child in holder.winfo_children():
            child.destroy()

        if not hits:
            label = tk.Label(
                holder,
                bg=self.PANEL,
                fg=self.MUTED,
                text="No compatible Modrinth projects found."
            )
            label.pack(
                anchor="w",
                padx=8,
                pady=8
            )
            return

        for hit in hits:
            row = tk.Frame(
                holder,
                bg=self.PANEL_2,
                bd=0
            )
            row.pack(
                fill="x",
                padx=4,
                pady=3
            )

            info = tk.Frame(
                row,
                bg=self.PANEL_2
            )
            info.pack(
                side="left",
                fill="both",
                expand=True,
                padx=7,
                pady=5
            )

            title = tk.Label(
                info,
                bg=self.PANEL_2,
                fg=self.TEXT,
                anchor="w"
            )
            self._set_pixel_label_text(
                title,
                hit.get("title", "Mod"),
                9,
                self.TEXT,
                max_width=260
            )
            title.pack(
                anchor="w"
            )

            description = tk.Label(
                info,
                bg=self.PANEL_2,
                fg=self.MUTED,
                text=hit.get("description", ""),
                justify="left",
                anchor="w",
                wraplength=280,
                font=(self.ui_font, 8)
            )
            description.pack(
                anchor="w",
                pady=(3, 0)
            )

            install = self.beveled_button(
                row,
                "Install",
                lambda project_id=hit.get("project_id"): self.install_modrinth_project(
                    project_id
                ),
                font_size=8,
                tooltip="Download the newest compatible file into this version's mod storage."
            )
            install.pack(
                side="right",
                padx=5,
                pady=5
            )

        if hasattr(holder, "_sml_bind_wheel"):
            holder._sml_bind_wheel(holder)

    def install_modrinth_project(self, project_id):
        if not project_id:
            return

        installation = self.selected_installation_data()
        installation_version = installation.get(
            "version",
            ""
        )

        def worker():
            try:
                result = download_modrinth_project(
                    project_id,
                    installation_version
                )

                filename = result["filename"]

                mods = installation.get(
                    "mods",
                    []
                )
                if not isinstance(mods, list):
                    mods = []

                if filename not in mods:
                    mods.append(filename)

                installation["mods"] = mods
                installation["vanilla"] = False

                self.save_installations()

                self.dispatch_to_ui(
                    self.show_mods_page
                )
            except Exception as exc:
                message = str(exc)
                self.dispatch_to_ui(
                    lambda m=message: self.show_inline_notice(
                        "Modrinth Install Failed",
                        m,
                        back_command=self.show_mods_page
                    )
                )

        threading.Thread(
            target=worker,
            daemon=True
        ).start()

    def _set_details(self, message):
        return

    def _set_tools_enabled(self, enabled):
        for button in getattr(
            self,
            "current_tool_buttons",
            []
        ):
            self.set_button_enabled(
                button,
                enabled,
                tooltip=(
                    ""
                    if enabled
                    else "This option is unavailable because this game is not currently available."
                )
            )


    def _set_play_mode(self, mode):
        mode = mode.upper()
        self.play_button._label_text = mode

        if mode.upper() == "BUY":
            self.play_button._real_command = self.buy_selected_game
            self.play_button._base_bg = "#8b6c24"

            self.set_button_enabled(
                self.play_button,
                True,
                tooltip="Open the official purchase page."
            )
        else:
            self.play_button._real_command = self.play_selected
            self.play_button._base_bg = self.GREEN

            self.set_button_enabled(
                self.play_button,
                True,
                tooltip="Launch the selected game."
            )


    def update_game_status(self):
        game = self.selected_game

        if game == "Java Edition":
            versions = java_versions(
                Path(
                    self.config_data.get(
                        "minecraft_dir",
                        str(MC_DIR)
                    )
                )
            )

            owned = self.game_available.get(
                "Java Edition"
            )

            if owned is False:
                self._set_play_mode("Buy")
                self._set_tools_enabled(False)
                self._set_details(
                    "Minecraft: Java Edition is not owned by the selected account."
                )
                return

            self._set_tools_enabled(True)

            if versions:
                self._set_play_mode("Play")
                self._set_details(
                    "Choose a saved Microsoft account and installed Java version above.\n\n"
                    "PLAY verifies the Java profile before starting the selected installation."
                )
            else:
                self.play_button._label_text = "Play"
                self.play_button._base_bg = self.GREEN_DISABLED
                self.set_button_enabled(
                    self.play_button,
                    False,
                    tooltip="No installed Minecraft Java versions were detected."
                )
                self._set_details(
                    "No installed Java versions were found in the selected .minecraft folder."
                )

            return

        installed = bool(
            self.games.get(game)
        )
        self.game_available[game] = installed

        if installed:
            self._set_play_mode("Play")
            self._set_tools_enabled(True)
            self._set_details(
                "Ready to launch. Windows/Xbox performs its normal entitlement check when the game starts."
            )
        else:
            self._set_play_mode("Buy")
            self._set_tools_enabled(False)
            self._set_details(
                "This game is not currently available through the Windows installation."
            )

    def buy_selected_game(self):
        url = GAME_BUY_URLS.get(
            self.selected_game
        )

        if url:
            webbrowser.open(url)


    def link_label(
        self,
        parent,
        text,
        url,
        *,
        font_size=9
    ):
        label = tk.Label(
            parent,
            bg=parent.cget("bg"),
            fg="#9fd3ff",
            cursor="hand2",
            anchor="w",
            justify="left"
        )

        self._set_pixel_label_text(
            label,
            text,
            font_size,
            "#9fd3ff",
            align="left"
        )

        underline = tk.Frame(
            label,
            bg="#9fd3ff",
            height=1
        )

        def open_target(_event=None):
            target = str(url)

            # Normal web links.
            if target.startswith(
                ("http://", "https://", "file:")
            ):
                webbrowser.open(target)
                return

            # Local path fallback.
            try:
                os.startfile(target)
            except Exception:
                webbrowser.open(target)

        def enter(_event=None):
            underline.place(
                relx=0,
                rely=1.0,
                relwidth=1.0,
                height=1,
                anchor="sw"
            )

        def leave(_event=None):
            underline.place_forget()

        label.bind(
            "<Button-1>",
            open_target
        )
        label.bind(
            "<Enter>",
            enter
        )
        label.bind(
            "<Leave>",
            leave
        )

        return label


    def show_inline_notice(self, title, message, back_command=None):
        self.clear_content()
        self.top_title(self.content, title.upper())

        p = self.panel(self.content)
        p.pack(fill="both", expand=True)

        tk.Label(
            p,
            text=message,
            bg=self.PANEL,
            fg=self.TEXT,
            justify="left",
            anchor="nw",
            wraplength=760,
            padx=24,
            pady=24,
            font=(self.ui_font, 11)
        ).pack(fill="both", expand=True)

        row = tk.Frame(self.content, bg=self.BG)
        row.pack(fill="x", pady=(10, 0))
        self.beveled_button(
            row,
            "Back",
            back_command or self.back_to_game
        ).pack(side="left")

    # ---------- accounts screen ----------

    def get_page_state(self, page_name, key=None, default=None):
        page_state = self.config_data.setdefault(
            "page_state",
            {}
        )

        state = page_state.setdefault(
            page_name,
            {}
        )

        if key is None:
            return state

        return state.get(
            key,
            default
        )

    def set_page_state(self, page_name, key, value):
        page_state = self.config_data.setdefault(
            "page_state",
            {}
        )

        state = page_state.setdefault(
            page_name,
            {}
        )

        state[key] = value
        save_config(
            self.config_data
        )

    def _account_profile_cache(self):
        profiles = self.account_metadata.setdefault(
            "profiles",
            {}
        )

        if not isinstance(
            profiles,
            dict
        ):
            profiles = {}
            self.account_metadata[
                "profiles"
            ] = profiles

        return profiles

    def save_account_metadata(self):
        save_account_metadata(
            self.account_metadata
        )


    def _ordered_accounts(self, accounts=None):
        if accounts is None:
            accounts = self.auth.accounts()

        accounts = list(accounts)
        by_id = {
            self._account_id(account): account
            for account in accounts
            if self._account_id(account)
        }

        saved_order = self.config_data.get(
            "account_order",
            []
        )

        if not isinstance(saved_order, list):
            saved_order = []

        ordered_ids = [
            hid
            for hid in saved_order
            if hid in by_id
        ]

        for account in accounts:
            hid = self._account_id(account)
            if hid and hid not in ordered_ids:
                ordered_ids.append(hid)

        if ordered_ids != saved_order:
            self.config_data[
                "account_order"
            ] = ordered_ids
            save_config(
                self.config_data
            )

        return [
            by_id[hid]
            for hid in ordered_ids
            if hid in by_id
        ]

    def _account_email(self, account):
        claims = account.get("id_token_claims") or {}

        return (
            account.get("username")
            or claims.get("preferred_username")
            or claims.get("email")
            or ""
        )

    def _account_microsoft_name(self, account):
        claims = account.get("id_token_claims") or {}

        name = (
            account.get("name")
            or claims.get("name")
            or claims.get("given_name")
            or ""
        )

        if name:
            return str(name)

        email = self._account_email(account)
        if "@" in email:
            return email.split("@", 1)[0]

        return email or "Microsoft account"

    def _account_id(self, account):
        return str(
            account.get(
                "home_account_id",
                ""
            )
        )

    def _set_account_cell_text(
        self,
        label,
        text,
        color=None,
        max_width=240,
        size=9
    ):
        display = text or "-"

        unavailable_values = {
            "Unavailable",
            "Unknown",
            "...",
            "Not available",
            "-",
        }

        final_color = color or self.TEXT

        if display in unavailable_values:
            final_color = "#b0b0b0"

        label.config(
            anchor="w",
            justify="left"
        )

        self._set_pixel_label_text(
            label,
            display,
            size,
            final_color,
            max_width=max_width,
            align="left"
        )

    def show_accounts_screen(self):
        self.current_screen = "accounts"
        self.update_navigation_button_states()
        self.clear_content()

        self.top_title(
            self.content,
            "ACCOUNTS"
        )

        panel = self.panel(
            self.content
        )
        panel.pack(
            fill="both",
            expand=True
        )

        table_outer = tk.Frame(
            panel,
            bg=self.PANEL_3,
            bd=3,
            relief="sunken"
        )
        table_outer.pack(
            fill="both",
            expand=True,
            padx=14,
            pady=14
        )

        self.account_columns = {}
        self.account_column_bodies = {}

        default_widths = {
            "Email": 300,
            "Microsoft Username": 240,
            "Minecraft Java Username": 245,
        }

        saved_widths = self.get_page_state(
            "accounts",
            "column_widths",
            {}
        )

        self.account_column_widths = dict(
            default_widths
        )

        if isinstance(saved_widths, dict):
            for title in default_widths:
                try:
                    saved = int(
                        saved_widths.get(
                            title,
                            default_widths[title]
                        )
                    )
                except Exception:
                    saved = default_widths[title]

                self.account_column_widths[
                    title
                ] = max(
                    80,
                    saved
                )

        self.account_column_min_widths = {
            "Email": 170,
            "Microsoft Username": 190,
            "Minecraft Java Username": 175,
        }

        privacy_labels = {
            "Email": "Email",
            "Microsoft Username": "Microsoft Username",
            "Minecraft Java Username": "Java Username",
        }

        for title in list(
            self.account_column_min_widths
        ):
            self.account_column_min_widths[
                title
            ] = max(
                self.account_column_min_widths[
                    title
                ],
                self._account_text_width(
                    title
                ) + 28,
                self._account_text_width(
                    privacy_labels[
                        title
                    ]
                ) + 38
            )

        self.account_drag_width = 34

        self.accounts_header = tk.Frame(
            table_outer,
            bg=self.PANEL_2,
            height=36
        )
        self.accounts_header.pack(
            fill="x"
        )
        self.accounts_header.pack_propagate(
            False
        )

        self.accounts_body = tk.Frame(
            table_outer,
            bg=self.PANEL_2
        )
        self.accounts_body.pack(
            fill="both",
            expand=True
        )

        # Fixed-width unnamed drag/reorder column.
        drag_header = tk.Frame(
            self.accounts_header,
            bg=self.PANEL_2,
            width=self.account_drag_width,
            height=36
        )
        drag_header.pack(
            side="left",
            fill="y"
        )
        drag_header.pack_propagate(
            False
        )

        drag_body = tk.Frame(
            self.accounts_body,
            bg=self.PANEL_2,
            width=self.account_drag_width,
            bd=0,
            highlightthickness=0
        )
        drag_body.pack(
            side="left",
            fill="y"
        )
        drag_body.pack_propagate(
            False
        )

        self.account_drag_body = drag_body

        column_titles = [
            "Email",
            "Microsoft Username",
            "Minecraft Java Username",
        ]

        for index, title in enumerate(
            column_titles
        ):
            width = self.account_column_widths[
                title
            ]

            header = tk.Frame(
                self.accounts_header,
                bg=self.PANEL_2,
                width=width,
                height=36
            )
            header.pack(
                side="left",
                fill="y"
            )
            header.pack_propagate(
                False
            )

            header_label = tk.Label(
                header,
                bg=self.PANEL_2,
                fg=self.TEXT,
                anchor="w",
                justify="left"
            )

            self._set_pixel_label_text(
                header_label,
                title,
                9,
                self.TEXT,
                align="left"
            )

            header_label.pack(
                fill="both",
                expand=True,
                padx=(8, 7)
            )

            body = tk.Frame(
                self.accounts_body,
                bg=self.PANEL_2,
                width=width,
                bd=0,
                highlightthickness=0
            )
            body.pack(
                side="left",
                fill="y"
            )
            body.pack_propagate(
                False
            )

            self.account_columns[
                title
            ] = {
                "header": header,
                "header_label": header_label,
                "body": body,
            }

            self.account_column_bodies[
                title
            ] = body

            # Resizers exist only between the column LABELS.
            if index < len(column_titles) - 1:
                handle = tk.Frame(
                    header,
                    bg="#565656",
                    width=6,
                    cursor="sb_h_double_arrow"
                )
                handle.place(
                    relx=1.0,
                    rely=0,
                    relheight=1.0,
                    anchor="ne"
                )

                handle.bind(
                    "<Button-1>",
                    lambda e, t=title: self._begin_account_column_resize(
                        e,
                        t
                    )
                )

                handle.bind(
                    "<B1-Motion>",
                    lambda e, t=title: self._drag_account_column_resize(
                        e,
                        t
                    )
                )

        # Account ID absorbs remaining space after the priority columns.
        self.selected_account_row = None
        self.screen_accounts = []
        self._account_row_cells = {}
        self._email_revealed = {}
        self._account_java_names = {}
        self._account_gamertags = {}
        self._account_java_errors = {}
        self._account_drag_source = None
        self._account_drag_target = None
        self._account_insert_line = None

        controls = tk.Frame(
            panel,
            bg=self.PANEL
        )
        controls.pack(
            fill="x",
            padx=14,
            pady=(0, 14)
        )

        self.beveled_button(
            controls,
            "Use Selected",
            self.use_selected_account,
            bg=self.GREEN
        ).pack(
            side="left"
        )

        self.beveled_button(
            controls,
            "Add Account",
            self.add_account
        ).pack(
            side="left",
            padx=8
        )

        self.beveled_button(
            controls,
            "Remove",
            self.remove_selected_account
        ).pack(
            side="left"
        )

        self.beveled_button(
            controls,
            "Refresh Profile",
            self.refresh_selected_account_profile,
            tooltip="Retry the Xbox and Minecraft profile lookup for the selected account."
        ).pack(
            side="left",
            padx=(8, 0)
        )

        self.refill_accounts_screen()

        self.back_bar(
            self.content
        )


    def _begin_account_column_resize(
        self,
        event,
        title
    ):
        self._account_resize_title = title
        self._account_resize_start_x = event.x_root
        self._account_resize_start_width = (
            self.account_column_widths.get(
                title,
                200
            )
        )

    def _drag_account_column_resize(
        self,
        event,
        title
    ):
        if getattr(
            self,
            "_account_resize_title",
            None
        ) != title:
            return

        delta = (
            event.x_root
            - self._account_resize_start_x
        )

        minimum = self.account_column_min_widths.get(
            title,
            120
        )

        new_width = max(
            minimum,
            self._account_resize_start_width
            + delta
        )

        self.account_column_widths[
            title
        ] = new_width

        column = self.account_columns.get(
            title
        )

        if not column:
            return

        column["header"].config(
            width=new_width
        )
        column["body"].config(
            width=new_width
        )

        self._refresh_account_header_text(
            title
        )

        self.set_page_state(
            "accounts",
            "column_widths",
            dict(
                self.account_column_widths
            )
        )

    def _refresh_account_header_text(
        self,
        title
    ):
        column = self.account_columns.get(
            title
        )

        if not column:
            return

        width = self.account_column_widths.get(
            title,
            200
        )

        self._set_pixel_label_text(
            column["header_label"],
            title,
            9,
            self.TEXT,
            align="left"
        )


    def _account_text_width(self, text, size=9):
        photo = self._hard_text_photo(
            text or "-",
            size,
            self.TEXT,
            max_width=2000,
            align="left"
        )

        if photo is None:
            return max(
                80,
                len(str(text or "")) * 9
            )

        return photo.width()

    def _auto_size_account_columns(
        self,
        force=False
    ):
        if not hasattr(
            self,
            "accounts_body"
        ):
            return

        try:
            available = self.accounts_body.winfo_width()
        except Exception:
            return

        if available <= 100:
            self.after(
                30,
                lambda: self._auto_size_account_columns(
                    force=force
                )
            )
            return

        current_ids = [
            self._account_id(account)
            for account in getattr(
                self,
                "screen_accounts",
                []
            )
            if self._account_id(account)
        ]

        current_id_set = sorted(
            current_ids
        )

        previous_ids = self.get_page_state(
            "accounts",
            "sized_for_accounts",
            []
        )

        saved_widths = self.get_page_state(
            "accounts",
            "column_widths",
            {}
        )

        # Preserve user-resized widths when revisiting the page with the same
        # account set. Adding/removing an account triggers a fresh prioritized
        # auto-size.
        if (
            not force
            and isinstance(saved_widths, dict)
            and saved_widths
            and current_id_set == sorted(previous_ids)
        ):
            for title, width in saved_widths.items():
                if title not in self.account_columns:
                    continue

                try:
                    width = int(width)
                except Exception:
                    continue

                minimum = self.account_column_min_widths.get(
                    title,
                    80
                )

                width = max(
                    minimum,
                    width
                )

                self.account_column_widths[
                    title
                ] = width

                column = self.account_columns[
                    title
                ]

                column["header"].config(
                    width=width
                )
                column["body"].config(
                    width=width
                )
                self._refresh_account_header_text(
                    title
                )

            self._refresh_email_censor_widths()
            return

        available -= self.account_drag_width

        accounts = getattr(
            self,
            "screen_accounts",
            []
        )

        # The label itself is part of the required width. Headers are never
        # wrapped onto a second line.
        email_need = max(
            self.account_column_min_widths["Email"],
            self._account_text_width("Email") + 28
        )

        ms_need = max(
            self.account_column_min_widths["Microsoft Username"],
            self._account_text_width("Microsoft Username") + 38
        )

        java_need = max(
            self.account_column_min_widths["Minecraft Java Username"],
            self._account_text_width("Minecraft Java Username") + 28
        )

        for index, account in enumerate(
            accounts
        ):
            email_need = max(
                email_need,
                self._account_text_width(
                    self._account_email(account)
                ) + 30
            )

            hid = self._account_id(account)

            microsoft_name = self._account_gamertags.get(
                index,
                self._cached_gamertags_by_hid.get(
                    hid,
                    self._account_microsoft_name(account)
                )
            )

            java_name = self._account_java_names.get(
                index,
                self._cached_java_names_by_hid.get(
                    hid,
                    "..."
                )
            )

            ms_need = max(
                ms_need,
                self._account_text_width(
                    microsoft_name
                ) + 24
            )

            java_need = max(
                java_need,
                self._account_text_width(
                    java_name
                ) + 24
            )

        # Priority order when space is tight:
        # Email -> Microsoft Username -> Java Username -> Account ID.
        email_need = min(
            email_need,
            430
        )
        ms_need = min(
            ms_need,
            340
        )
        java_need = min(
            java_need,
            360
        )

        remaining = available

        email_width = min(
            email_need,
            max(
                self.account_column_min_widths["Email"],
                remaining
                - self.account_column_min_widths["Microsoft Username"]
                - self.account_column_min_widths["Minecraft Java Username"]
            )
        )
        remaining -= email_width

        ms_width = min(
            ms_need,
            max(
                self.account_column_min_widths["Microsoft Username"],
                remaining
                - self.account_column_min_widths["Minecraft Java Username"]
            )
        )
        remaining -= ms_width

        java_width = max(
            self.account_column_min_widths["Minecraft Java Username"],
            remaining
        )

        widths = {
            "Email": email_width,
            "Microsoft Username": ms_width,
            "Minecraft Java Username": java_width,
        }

        for title, width in widths.items():
            self.account_column_widths[
                title
            ] = width

            column = self.account_columns.get(
                title
            )

            if not column:
                continue

            column["header"].config(
                width=width
            )
            column["body"].config(
                width=width
            )
            self._refresh_account_header_text(
                title
            )

        self.set_page_state(
            "accounts",
            "column_widths",
            dict(self.account_column_widths)
        )
        self.set_page_state(
            "accounts",
            "sized_for_accounts",
            current_id_set
        )

        self._refresh_email_censor_widths()


    def _longest_email_censor_width(self):
        longest = 78

        for account in getattr(
            self,
            "screen_accounts",
            []
        ):
            email = self._account_email(
                account
            )

            longest = max(
                longest,
                self._account_text_width(
                    email or "Email"
                ) + 12
            )

        # Leave room inside the email column.
        column_width = self.account_column_widths.get(
            "Email",
            260
        )

        return min(
            longest,
            max(78, column_width - 14)
        )

    def _refresh_email_censor_widths(self):
        """
        Kept under the original method name because existing sizing code calls
        it, but it now refreshes every account privacy rectangle.
        """
        email_width = self._longest_email_censor_width()

        field_columns = {
            "email_button": (
                "Email",
                email_width
            ),
            "microsoft_button": (
                "Microsoft Username",
                None
            ),
            "java_button": (
                "Minecraft Java Username",
                None
            ),
        }

        for row in getattr(
            self,
            "_account_row_cells",
            {}
        ).values():
            for key, (
                column_name,
                preferred_width
            ) in field_columns.items():
                button = row.get(
                    key
                )

                if button is None:
                    continue

                if preferred_width is None:
                    width = max(
                        78,
                        int(
                            self.account_column_widths.get(
                                column_name,
                                180
                            )
                        ) - 14
                    )
                else:
                    width = preferred_width

                button.config(
                    width=width
                )

                render = getattr(
                    button,
                    "_render_privacy",
                    None
                )

                if callable(render):
                    render()



    def _make_account_drag_cell(
        self,
        index
    ):
        cell = tk.Frame(
            self.account_drag_body,
            bg=self.PANEL_2,
            width=self.account_drag_width,
            height=36,
            bd=0,
            highlightthickness=0,
            cursor="fleur"
        )
        cell.pack(
            fill="x",
            padx=0,
            pady=1
        )
        cell.pack_propagate(
            False
        )

        label = tk.Label(
            cell,
            bg=self.PANEL_2,
            fg=self.TEXT,
            cursor="fleur",
            anchor="center"
        )

        self._set_pixel_label_text(
            label,
            "::",
            9,
            self.TEXT,
            align="center"
        )

        label.pack(
            fill="both",
            expand=True
        )

        for widget in (
            cell,
            label
        ):
            widget.bind(
                "<Button-1>",
                lambda e, idx=index: self._begin_account_reorder(
                    e,
                    idx
                )
            )

            widget.bind(
                "<B1-Motion>",
                self._drag_account_reorder
            )

            widget.bind(
                "<ButtonRelease-1>",
                self._finish_account_reorder
            )

        return cell, label

    def _begin_account_reorder(
        self,
        event,
        index
    ):
        self._account_drag_source = index
        self._account_drag_target = index
        self._update_account_insert_line(
            event.y_root
        )

    def _drag_account_reorder(
        self,
        event
    ):
        if self._account_drag_source is None:
            return

        self._update_account_insert_line(
            event.y_root
        )

    def _update_account_insert_line(
        self,
        y_root
    ):
        count = len(
            getattr(
                self,
                "screen_accounts",
                []
            )
        )

        if count <= 0:
            return

        body_y = self.accounts_body.winfo_rooty()
        local_y = y_root - body_y

        row_pitch = 38
        target = int(
            round(
                local_y / row_pitch
            )
        )

        target = max(
            0,
            min(
                count,
                target
            )
        )

        self._account_drag_target = target

        if (
            self._account_insert_line is None
            or not self._account_insert_line.winfo_exists()
        ):
            self._account_insert_line = tk.Frame(
                self.accounts_body,
                bg="#ffffff",
                height=2
            )

        y = target * row_pitch

        self._account_insert_line.place(
            x=0,
            y=y,
            relwidth=1.0,
            height=2
        )
        self._account_insert_line.lift()

    def _finish_account_reorder(
        self,
        _event=None
    ):
        source = self._account_drag_source
        target = self._account_drag_target

        self._account_drag_source = None
        self._account_drag_target = None

        if (
            self._account_insert_line is not None
            and self._account_insert_line.winfo_exists()
        ):
            self._account_insert_line.destroy()

        self._account_insert_line = None

        accounts = list(
            getattr(
                self,
                "screen_accounts",
                []
            )
        )

        if (
            source is None
            or target is None
            or not (
                0 <= source < len(accounts)
            )
        ):
            return

        account = accounts.pop(
            source
        )

        # Target describes a boundary in the original list. Once the source
        # is removed, boundaries after it shift left by one.
        if target > source:
            target -= 1

        target = max(
            0,
            min(
                len(accounts),
                target
            )
        )

        accounts.insert(
            target,
            account
        )

        new_order = [
            self._account_id(item)
            for item in accounts
            if self._account_id(item)
        ]

        saved_widths_before_reorder = dict(
            self.account_column_widths
        )

        self.config_data[
            "account_order"
        ] = new_order

        self.set_page_state(
            "accounts",
            "column_widths",
            saved_widths_before_reorder
        )
        self.set_page_state(
            "accounts",
            "sized_for_accounts",
            sorted(new_order)
        )

        save_config(
            self.config_data
        )

        selected_hid = self.config_data.get(
            "selected_account",
            ""
        )

        self.refill_accounts_screen()

        for idx, item in enumerate(
            self.screen_accounts
        ):
            if self._account_id(item) == selected_hid:
                self._select_account_row(
                    idx
                )
                break


    def _make_account_cell(
        self,
        body,
        index,
        text,
        max_width=220,
        tooltip_text=""
    ):
        cell = tk.Frame(
            body,
            bg=self.PANEL_2,
            height=36,
            bd=0,
            highlightthickness=0,
            cursor="hand2"
        )
        cell.pack(
            fill="x",
            padx=0,
            pady=1
        )
        cell.pack_propagate(False)

        label = tk.Label(
            cell,
            bg=self.PANEL_2,
            fg=self.TEXT,
            anchor="w",
            cursor="hand2"
        )
        self._set_account_cell_text(
            label,
            text,
            self.TEXT,
            max_width=max_width,
            size=9
        )
        label.pack(
            fill="both",
            expand=True,
            padx=7
        )

        if tooltip_text:
            Tooltip(
                label,
                tooltip_text,
                launcher=self
            )

        def select(
            _event=None,
            idx=index
        ):
            self._select_account_row(
                idx
            )

        cell.bind(
            "<Button-1>",
            select
        )
        label.bind(
            "<Button-1>",
            select
        )

        return cell, label

    def _make_privacy_account_cell(
        self,
        body,
        index,
        value,
        field_label,
        width=None,
        tooltip_text=""
    ):
        cell = tk.Frame(
            body,
            bg=self.PANEL_2,
            height=36,
            bd=0,
            highlightthickness=0,
            cursor="hand2"
        )
        cell.pack(
            fill="x",
            padx=0,
            pady=1
        )
        cell.pack_propagate(False)

        holder = tk.Frame(
            cell,
            bg=self.PANEL_2
        )
        holder.pack(
            fill="both",
            expand=True,
            padx=5,
            pady=4
        )

        button = tk.Button(
            holder,
            text="",
            bg="#000000",
            fg="#ffffff",
            activebackground="#000000",
            activeforeground="#ffffff",
            relief="solid",
            bd=2,
            highlightthickness=0,
            cursor="hand2",
            takefocus=False
        )
        button.pack(
            side="left",
            fill="y"
        )

        button._privacy_value = str(
            value or ""
        )
        button._privacy_label = str(
            field_label
        )
        button._privacy_revealed = False
        button._hover_value = 0.0
        button._hover_target = 0.0

        def render():
            actual = str(
                button._privacy_value
                or ""
            )
            loading = (
                not actual
                or actual.strip()
                in (
                    "...",
                    "Loading...",
                )
            )

            if button._privacy_revealed and actual:
                display = actual
            elif loading:
                display = "..."
            else:
                display = button._privacy_label

            photo = self._hard_text_photo(
                display,
                9,
                "#ffffff",
                max_width=2000
            )

            actual_photo = self._hard_text_photo(
                actual
                or "...",
                9,
                "#ffffff",
                max_width=2000
            )

            label_photo = self._hard_text_photo(
                button._privacy_label,
                9,
                "#ffffff",
                max_width=2000
            )

            wanted = (
                int(width)
                if width is not None
                else 78
            )

            for measured_photo in (
                actual_photo,
                label_photo,
            ):
                if measured_photo is not None:
                    wanted = max(
                        wanted,
                        measured_photo.width()
                        + 12
                    )

            # Never let the black rectangle extend underneath the next account
            # column. It fills the usable portion of its own column instead.
            try:
                column_title = {
                    "Email": "Email",
                    "Microsoft Username": "Microsoft Username",
                    "Java Username": "Minecraft Java Username",
                }.get(
                    button._privacy_label,
                    button._privacy_label
                )

                column_width = int(
                    self.account_column_widths.get(
                        column_title,
                        wanted + 14
                    )
                )

                wanted = min(
                    wanted,
                    max(
                        78,
                        column_width - 14
                    )
                )
            except Exception:
                pass

            if photo is not None:
                button._text_photo = photo
                button.config(
                    image=photo,
                    text="",
                    width=wanted
                )
            else:
                button.config(
                    image="",
                    text=display,
                    font=("Segoe UI", 9),
                    width=wanted
                )

        button._render_privacy = render

        def animate_hover():
            current = float(
                button._hover_value
            )
            target = float(
                button._hover_target
            )
            step = 0.14

            if abs(
                current - target
            ) < 0.02:
                current = target
            elif current < target:
                current = min(
                    target,
                    current + step
                )
            else:
                current = max(
                    target,
                    current - step
                )

            button._hover_value = current
            bg = self._mix_color(
                "#000000",
                "#303030",
                current
            )

            try:
                button.config(
                    bg=bg,
                    activebackground=bg
                )
            except tk.TclError:
                return

            if current != target:
                button.after(
                    16,
                    animate_hover
                )

        def toggle():
            self._select_account_row(
                index
            )
            button._privacy_revealed = (
                not button._privacy_revealed
            )
            render()

        button.config(
            command=toggle
        )
        button.bind(
            "<Enter>",
            lambda e: (
                setattr(
                    button,
                    "_hover_target",
                    1.0
                ),
                animate_hover()
            ),
            add="+"
        )
        button.bind(
            "<Leave>",
            lambda e: (
                setattr(
                    button,
                    "_hover_target",
                    0.0
                ),
                animate_hover()
            ),
            add="+"
        )

        cell.bind(
            "<Button-1>",
            lambda e, idx=index: self._select_account_row(
                idx
            )
        )

        if tooltip_text:
            Tooltip(
                button,
                tooltip_text,
                launcher=self
            )

        render()
        return cell, button


    def _set_privacy_button_value(
        self,
        button,
        value
    ):
        if button is None:
            return

        button._privacy_value = str(
            value or ""
        )

        render = getattr(
            button,
            "_render_privacy",
            None
        )

        if callable(render):
            render()


    def _make_email_cell(
        self,
        body,
        index,
        email,
        censor_width=None
    ):
        cell = tk.Frame(
            body,
            bg=self.PANEL_2,
            height=36,
            bd=0,
            highlightthickness=0,
            cursor="hand2"
        )
        cell.pack(
            fill="x",
            padx=0,
            pady=1
        )
        cell.pack_propagate(False)

        holder = tk.Frame(
            cell,
            bg=self.PANEL_2
        )
        holder.pack(
            fill="both",
            expand=True,
            padx=5,
            pady=4
        )

        button = tk.Button(
            holder,
            text="",
            bg="#000000",
            fg="#ffffff",
            activebackground="#000000",
            activeforeground="#ffffff",
            relief="solid",
            bd=2,
            highlightthickness=0,
            cursor="hand2",
            takefocus=False
        )
        button.pack(
            side="left",
            fill="y"
        )

        button._email = email
        button._account_index = index
        button._hover_value = 0.0
        button._hover_target = 0.0

        # Measure the FULL email once. The hidden rectangle will keep this
        # width even while it only displays the word "Email".
        full_email_photo = self._hard_text_photo(
            email or "Email",
            9,
            "#ffffff",
            max_width=1000
        )

        hidden_photo = self._hard_text_photo(
            "Email",
            9,
            "#ffffff",
            max_width=1000
        )

        wanted_width = (
            int(censor_width)
            if censor_width is not None
            else 78
        )

        if censor_width is None and full_email_photo is not None:
            wanted_width = max(
                wanted_width,
                full_email_photo.width() + 10
            )

        def render():
            revealed = self._email_revealed.get(
                index,
                False
            )

            if revealed and email:
                photo = full_email_photo
            else:
                photo = hidden_photo

            if photo is not None:
                button._text_photo = photo
                button.config(
                    image=photo,
                    text="",
                    width=wanted_width
                )
            else:
                button.config(
                    image="",
                    text=(
                        email
                        if revealed and email
                        else "Email"
                    ),
                    font=("Segoe UI", 9),
                    width=wanted_width
                )

        def animate_hover():
            current = float(
                getattr(
                    button,
                    "_hover_value",
                    0.0
                )
            )
            target = float(
                getattr(
                    button,
                    "_hover_target",
                    0.0
                )
            )

            step = 0.14

            if abs(current - target) < 0.02:
                current = target
            elif current < target:
                current = min(
                    target,
                    current + step
                )
            else:
                current = max(
                    target,
                    current - step
                )

            button._hover_value = current

            bg = self._mix_color(
                "#000000",
                "#303030",
                current
            )

            try:
                button.config(
                    bg=bg,
                    activebackground=bg
                )
            except tk.TclError:
                return

            if current != target:
                button.after(
                    16,
                    animate_hover
                )

        def set_hover(target):
            button._hover_target = float(
                target
            )
            animate_hover()

        def toggle():
            self._select_account_row(
                index
            )

            self._email_revealed[
                index
            ] = not self._email_revealed.get(
                index,
                False
            )

            render()

        button.config(
            command=toggle
        )

        button.bind(
            "<Enter>",
            lambda e: set_hover(1.0),
            add="+"
        )
        button.bind(
            "<Leave>",
            lambda e: set_hover(0.0),
            add="+"
        )

        cell.bind(
            "<Button-1>",
            lambda e, idx=index: self._select_account_row(idx)
        )

        holder.bind(
            "<Button-1>",
            lambda e, idx=index: self._select_account_row(idx)
        )

        Tooltip(
            button,
            "Click to reveal or hide the Microsoft sign-in email.",
            launcher=self
        )

        render()
        return cell, button


    def refill_accounts_screen(self):
        if not hasattr(
            self,
            "account_column_bodies"
        ):
            return

        for child in self.account_drag_body.winfo_children():
            child.destroy()

        for body in self.account_column_bodies.values():
            for child in body.winfo_children():
                child.destroy()

        self.screen_accounts = self._ordered_accounts(
            self.auth.accounts()
        )

        self._account_row_cells = {}
        self._email_revealed = {}
        self._account_java_names = {}
        self._account_gamertags = {}
        self._account_java_errors = {}

        selected_hid = self.config_data.get(
            "selected_account",
            ""
        )

        # Set an initial priority-based layout before creating privacy blocks.
        self.after_idle(
            lambda: self._auto_size_account_columns(
                force=True
            )
        )

        # All email privacy rectangles use the same width.
        longest_email_width = 78
        for account in self.screen_accounts:
            longest_email_width = max(
                longest_email_width,
                self._account_text_width(
                    self._account_email(account)
                    or "Email"
                ) + 12
            )

        for index, account in enumerate(
            self.screen_accounts
        ):
            email = self._account_email(
                account
            )

            account_id = self._account_id(
                account
            )

            self._email_revealed[
                index
            ] = False

            drag_cell, drag_label = self._make_account_drag_cell(
                index
            )

            censor_email = bool(
                self.config_data.get(
                    "censor_account_email",
                    True
                )
            )
            censor_microsoft = bool(
                self.config_data.get(
                    "censor_account_microsoft",
                    True
                )
            )
            censor_java = bool(
                self.config_data.get(
                    "censor_account_java",
                    False
                )
            )

            if censor_email:
                email_cell, email_button = self._make_privacy_account_cell(
                    self.account_column_bodies[
                        "Email"
                    ],
                    index,
                    email,
                    "Email",
                    width=longest_email_width,
                    tooltip_text="Click to reveal or hide the Microsoft sign-in email."
                )
                email_label = None
            else:
                email_cell, email_label = self._make_account_cell(
                    self.account_column_bodies[
                        "Email"
                    ],
                    index,
                    email,
                    max_width=max(
                        120,
                        self.account_column_widths.get(
                            "Email",
                            300
                        ) - 14
                    )
                )
                email_button = None

            cached_ms = self._cached_gamertags_by_hid.get(
                account_id,
                "..."
            )

            if censor_microsoft:
                ms_cell, ms_button = self._make_privacy_account_cell(
                    self.account_column_bodies[
                        "Microsoft Username"
                    ],
                    index,
                    cached_ms,
                    "Microsoft Username",
                    width=max(
                        78,
                        self.account_column_widths.get(
                            "Microsoft Username",
                            190
                        ) - 14
                    ),
                    tooltip_text="Click to reveal or hide the Microsoft/Xbox username."
                )
                ms_label = None
            else:
                ms_cell, ms_label = self._make_account_cell(
                    self.account_column_bodies[
                        "Microsoft Username"
                    ],
                    index,
                    cached_ms,
                    max_width=215,
                    tooltip_text="Xbox gamertag associated with this Microsoft account."
                )
                ms_button = None

            cached_java = self._cached_java_names_by_hid.get(
                account_id,
                "..."
            )

            if censor_java:
                java_cell, java_button = self._make_privacy_account_cell(
                    self.account_column_bodies[
                        "Minecraft Java Username"
                    ],
                    index,
                    cached_java,
                    "Java Username",
                    width=max(
                        78,
                        self.account_column_widths.get(
                            "Minecraft Java Username",
                            175
                        ) - 14
                    ),
                    tooltip_text="Click to reveal or hide the Minecraft Java username."
                )
                java_label = None
                java_tooltip = Tooltip(
                    java_button,
                    "Minecraft Java profile name.",
                    launcher=self
                )
            else:
                java_cell, java_label = self._make_account_cell(
                    self.account_column_bodies[
                        "Minecraft Java Username"
                    ],
                    index,
                    cached_java,
                    max_width=230
                )
                java_button = None
                java_tooltip = Tooltip(
                    java_label,
                    "Checking the Minecraft Java profile...",
                    launcher=self
                )

            self._account_row_cells[
                index
            ] = {
                "frames": [
                    drag_cell,
                    email_cell,
                    ms_cell,
                    java_cell
                ],
                "labels": [
                    label
                    for label in (
                        email_label,
                        ms_label,
                        java_label
                    )
                    if label is not None
                ],
                "drag_label": drag_label,
                "email_button": email_button,
                "email_label": email_label,
                "microsoft_button": ms_button,
                "microsoft_label": ms_label,
                "java_button": java_button,
                "java_label": java_label,
                "java_tooltip": java_tooltip,
            }

            if account_id == selected_hid:
                self._select_account_row(
                    index
                )

            self._fetch_account_identity(
                index,
                account_id,
                email
            )

        self.after_idle(
            self._refresh_email_censor_widths
        )


    def _fetch_account_identity(
        self,
        index,
        home_account_id,
        email
    ):
        if not home_account_id:
            return

        if home_account_id in self._identity_fetch_inflight:
            return

        profile_cache = self._account_profile_cache()
        cached = profile_cache.get(
            home_account_id,
            {}
        )

        if isinstance(cached, dict):
            cached_gamertag = str(
                cached.get(
                    "gamertag",
                    ""
                )
            ).strip()

            cached_java = str(
                cached.get(
                    "java_name",
                    ""
                )
            ).strip()

            cached_java_error = str(
                cached.get(
                    "java_error",
                    ""
                )
            ).strip()

            if cached_gamertag or cached_java:
                self._set_account_identity(
                    home_account_id,
                    cached_gamertag or "...",
                    cached_java or "...",
                    cached_java_error,
                    from_cache=True
                )

                # Names are display data. Do not continuously re-hit
                # Minecraft Services just because the Accounts page reopened.
                return

        self._identity_fetch_inflight.add(
            home_account_id
        )

        def worker():
            gamertag = ""
            xbox_xuid = ""
            java_name = ""
            java_error = ""

            try:
                xbox = self.auth.xbox_identity(
                    home_account_id
                )

                gamertag = xbox.get(
                    "gamertag",
                    ""
                )

                xbox_xuid = xbox.get(
                    "xuid",
                    ""
                )

            except Exception as exc:
                gamertag = "Unavailable"
                java_error = (
                    "Xbox identity lookup failed: "
                    + str(exc)
                )

            try:
                # One Minecraft Services profile resolution per account.
                # The result is cached in settings.json and reused on later
                # page visits instead of repeatedly calling login_with_xbox.
                session = self.auth.minecraft_session(
                    home_account_id
                )

                java_name = session.get(
                    "name",
                    ""
                ) or "Unavailable"

            except Exception as exc:
                java_error = str(exc)

                cached_name = local_launcher_java_profile_name(
                    Path(
                        self.config_data.get(
                            "minecraft_dir",
                            str(MC_DIR)
                        )
                    ),
                    email,
                    xbox_xuid
                )

                if cached_name:
                    java_name = cached_name
                    java_error = (
                        "Cached profile name. Minecraft Services could not "
                        "verify this Java profile through SML, so this account-"
                        "specific name was read from the official launcher's "
                        "local profile cache.\\n\\n"
                        + java_error
                    )
                else:
                    java_name = "Unavailable"

            def apply():
                self._identity_fetch_inflight.discard(
                    home_account_id
                )

                cache = self._account_profile_cache()
                cache[
                    home_account_id
                ] = {
                    "gamertag": gamertag or "Unavailable",
                    "java_name": java_name or "Unavailable",
                    "java_error": java_error,
                    "updated_at": int(time.time()),
                }

                self.save_account_metadata()

                self._set_account_identity(
                    home_account_id,
                    gamertag or "Unavailable",
                    java_name or "Unavailable",
                    java_error,
                    from_cache=False
                )

            self.after(
                0,
                apply
            )

        threading.Thread(
            target=worker,
            daemon=True
        ).start()


    def _set_account_identity(
        self,
        home_account_id,
        gamertag,
        java_name,
        java_error="",
        from_cache=False
    ):
        index = None

        for idx, account in enumerate(
            self.screen_accounts
        ):
            if self._account_id(account) == home_account_id:
                index = idx
                break

        if index is None:
            return

        hid = home_account_id

        self._cached_gamertags_by_hid[
            hid
        ] = gamertag

        self._cached_java_names_by_hid[
            hid
        ] = java_name

        self._account_gamertags[
            index
        ] = gamertag

        self._account_java_names[
            index
        ] = java_name

        self._account_java_errors[
            index
        ] = java_error

        row = self._account_row_cells.get(
            index
        )

        if not row:
            return

        selected = (
            self.selected_account_row
            == index
        )

        normal_color = (
            "#ffffff"
            if selected
            else self.TEXT
        )

        ms_button = row.get(
            "microsoft_button"
        )
        ms_label = row.get(
            "microsoft_label"
        )

        if ms_button is not None:
            self._set_privacy_button_value(
                ms_button,
                gamertag
            )

        if ms_label is not None:
            self._set_account_cell_text(
                ms_label,
                gamertag,
                normal_color,
                max_width=215,
                size=9
            )

        java_button = row.get(
            "java_button"
        )
        java_label = row.get(
            "java_label"
        )

        if java_button is not None:
            self._set_privacy_button_value(
                java_button,
                java_name
            )

        if java_label is not None:
            java_color = normal_color

            if java_error and java_name != "Unavailable":
                java_color = "#b8b8b8"

            self._set_account_cell_text(
                java_label,
                java_name,
                java_color,
                max_width=230,
                size=9
            )

        tooltip = row.get(
            "java_tooltip"
        )

        if tooltip is not None:
            if java_name == "Unavailable":
                tooltip.set_text(
                    java_error
                    or "Minecraft Java profile is unavailable."
                )
            elif java_error:
                tooltip.set_text(
                    java_error
                )
            else:
                tooltip.set_text(
                    "Minecraft Java profile name."
                )

        self.after_idle(
            self._auto_size_account_columns
        )


    def _select_account_row(self, index):
        self.selected_account_row = index

        for idx, row in getattr(
            self,
            "_account_row_cells",
            {}
        ).items():
            selected = (
                idx == index
            )

            bg = (
                self.GREEN
                if selected
                else self.PANEL_2
            )
            fg = (
                "#ffffff"
                if selected
                else self.TEXT
            )

            for frame in row.get(
                "frames",
                []
            ):
                frame.config(
                    bg=bg
                )

            drag_label = row.get(
                "drag_label"
            )

            if drag_label is not None:
                drag_label.config(
                    bg=bg
                )
                self._set_pixel_label_text(
                    drag_label,
                    "::",
                    9,
                    fg,
                    align="center"
                )

            for key in (
                "email_button",
                "microsoft_button",
                "java_button",
            ):
                button = row.get(
                    key
                )
                if button is not None:
                    try:
                        button.master.config(
                            bg=bg
                        )
                    except Exception:
                        pass

            email_label = row.get(
                "email_label"
            )
            if email_label is not None:
                self._set_account_cell_text(
                    email_label,
                    self._account_email(
                        self.screen_accounts[
                            idx
                        ]
                    ),
                    fg,
                    max_width=max(
                        120,
                        self.account_column_widths.get(
                            "Email",
                            300
                        ) - 14
                    ),
                    size=9
                )
                email_label.config(
                    bg=bg
                )

            ms_label = row.get(
                "microsoft_label"
            )
            if ms_label is not None:
                self._set_account_cell_text(
                    ms_label,
                    self._account_gamertags.get(
                        idx,
                        "..."
                    ),
                    fg,
                    max_width=215,
                    size=9
                )
                ms_label.config(
                    bg=bg
                )

            java_label = row.get(
                "java_label"
            )
            if java_label is not None:
                java_name = self._account_java_names.get(
                    idx,
                    "..."
                )
                java_color = fg

                if (
                    self._account_java_errors.get(
                        idx
                    )
                    and java_name != "Unavailable"
                ):
                    java_color = "#b8b8b8"

                self._set_account_cell_text(
                    java_label,
                    java_name,
                    java_color,
                    max_width=230,
                    size=9
                )
                java_label.config(
                    bg=bg
                )



    def refresh_selected_account_profile(self):
        index = getattr(
            self,
            "selected_account_row",
            None
        )

        if index is None:
            return

        if not (
            0 <= index < len(
                self.screen_accounts
            )
        ):
            return

        account = self.screen_accounts[
            index
        ]

        hid = self._account_id(
            account
        )
        email = self._account_email(
            account
        )

        self._account_profile_cache().pop(
            hid,
            None
        )
        self._cached_java_names_by_hid.pop(
            hid,
            None
        )
        self._cached_gamertags_by_hid.pop(
            hid,
            None
        )

        self.save_account_metadata()

        row = self._account_row_cells.get(
            index
        )

        if row:
            ms_button = row.get(
                "microsoft_button"
            )
            java_button = row.get(
                "java_button"
            )
            ms_label = row.get(
                "microsoft_label"
            )
            java_label = row.get(
                "java_label"
            )

            if ms_button is not None:
                self._set_privacy_button_value(
                    ms_button,
                    "..."
                )

            if java_button is not None:
                self._set_privacy_button_value(
                    java_button,
                    "..."
                )

            if ms_label is not None:
                self._set_account_cell_text(
                    ms_label,
                    "...",
                    "#b0b0b0",
                    max_width=215,
                    size=9
                )

            if java_label is not None:
                self._set_account_cell_text(
                    java_label,
                    "...",
                    "#b0b0b0",
                    max_width=230,
                    size=9
                )

        self._fetch_account_identity(
            index,
            hid,
            email
        )

    def add_account(self):
        try:
            self.auth.app()
        except Exception as exc:
            self.show_inline_notice(
                "Client ID required",
                str(exc)
            )
            return

        self.clear_content()
        self.top_title(
            self.content,
            "Add Account"
        )

        panel = self.panel(
            self.content
        )
        panel.pack(
            fill="both",
            expand=True
        )

        msg = tk.Label(
            panel,
            bg=self.PANEL,
            fg=self.TEXT,
            justify="left",
            anchor="w"
        )
        self._set_pixel_label_text(
            msg,
            "Requesting Microsoft sign-in code...",
            10,
            self.TEXT,
            max_width=720
        )
        msg.pack(
            fill="x",
            padx=24,
            pady=(30, 14)
        )

        code_var = tk.StringVar()

        code_entry = tk.Entry(
            panel,
            textvariable=code_var,
            state="readonly",
            justify="center",
            readonlybackground=self.BLACK,
            fg=self.TEXT,
            relief="sunken",
            bd=3,
            font=("Segoe UI", 20)
        )
        code_entry.pack(
            fill="x",
            padx=50,
            pady=10
        )

        button_row = tk.Frame(
            panel,
            bg=self.PANEL
        )
        button_row.pack(
            fill="x",
            padx=24,
            pady=18
        )

        self.beveled_button(
            button_row,
            "Back to Accounts",
            self.show_accounts_screen
        ).pack(
            side="left"
        )

        def callback(
            stage,
            payload
        ):
            if stage == "code":
                def show_code():
                    code_var.set(
                        payload.get(
                            "user_code",
                            ""
                        )
                    )

                    message = payload.get(
                        "message",
                        "Complete Microsoft sign-in in your browser."
                    )

                    self._set_pixel_label_text(
                        msg,
                        message,
                        10,
                        self.TEXT,
                        max_width=720
                    )

                    try:
                        os.startfile(
                            payload.get(
                                "verification_uri",
                                "https://microsoft.com/devicelogin"
                            )
                        )
                    except Exception:
                        pass

                self.after(
                    0,
                    show_code
                )

            elif stage == "done":
                self.after(
                    0,
                    self.show_accounts_screen
                )

            else:
                self.after(
                    0,
                    lambda: self.show_inline_notice(
                        "Sign-in failed",
                        str(payload),
                        back_command=self.show_accounts_screen
                    )
                )

        self.auth.add_account_device_flow(
            callback
        )

    def remove_selected_account(self):
        index = getattr(
            self,
            "selected_account_row",
            None
        )

        if index is None:
            return

        if not (
            0 <= index < len(
                self.screen_accounts
            )
        ):
            return

        account = self.screen_accounts[
            index
        ]

        home_account_id = self._account_id(
            account
        )

        if messagebox.askyesno(
            "Remove account",
            "Remove this saved sign-in?"
        ):
            self.auth.remove_account(
                home_account_id
            )

            self._account_profile_cache().pop(
                home_account_id,
                None
            )
            self._cached_java_names_by_hid.pop(
                home_account_id,
                None
            )
            self._cached_gamertags_by_hid.pop(
                home_account_id,
                None
            )

            self.save_account_metadata()

            if self.config_data.get(
                "selected_account"
            ) == home_account_id:
                self.config_data[
                    "selected_account"
                ] = ""
                save_config(
                    self.config_data
                )

            self.selected_account_row = None
            self.refill_accounts_screen()

    def use_selected_account(self):
        index = getattr(
            self,
            "selected_account_row",
            None
        )

        if index is None:
            return

        if not (
            0 <= index < len(
                self.screen_accounts
            )
        ):
            return

        home_account_id = self._account_id(
            self.screen_accounts[
                index
            ]
        )

        self.config_data[
            "selected_account"
        ] = home_account_id

        save_config(
            self.config_data
        )

        self.back_to_game()


    # ---------- settings screen ----------

    def show_settings_screen(self):
        self.current_screen = "settings"
        self.update_navigation_button_states()
        self.clear_content()
        self.top_title(self.content, "Settings")

        self.settings_section = "Launcher"
        self.settings_vars = {
            "client_id": tk.StringVar(
                value=self.config_data.get(
                    "client_id",
                    DEFAULT_CLIENT_ID
                ) or DEFAULT_CLIENT_ID
            ),
            "minecraft_dir": tk.StringVar(value=self.config_data.get("minecraft_dir", str(MC_DIR))),
            "java_memory_mb": tk.StringVar(value=str(self.config_data.get("java_memory_mb", 4096))),
            "bedrock_data_dir": tk.StringVar(value=self.config_data.get("bedrock_data_dir", "")),
            "dungeons_data_dir": tk.StringVar(value=self.config_data.get("dungeons_data_dir", "")),
            "dungeons2_data_dir": tk.StringVar(value=self.config_data.get("dungeons2_data_dir", "")),
            "legends_data_dir": tk.StringVar(value=self.config_data.get("legends_data_dir", "")),
            "date_format": tk.StringVar(
                value=self.config_data.get(
                    "date_format",
                    "MM/DD/YYYY"
                )
            ),
            "censor_account_email": tk.BooleanVar(
                value=bool(
                    self.config_data.get(
                        "censor_account_email",
                        True
                    )
                )
            ),
            "censor_account_microsoft": tk.BooleanVar(
                value=bool(
                    self.config_data.get(
                        "censor_account_microsoft",
                        True
                    )
                )
            ),
            "censor_account_java": tk.BooleanVar(
                value=bool(
                    self.config_data.get(
                        "censor_account_java",
                        False
                    )
                )
            ),
        }

        nav_outer = tk.Frame(self.content, bg=self.PANEL_2, bd=3, relief="raised")
        nav_outer.pack(fill="x", pady=(0, 8))
        nav = tk.Frame(nav_outer, bg=self.PANEL_2)
        nav.pack(fill="x", padx=7, pady=7)

        self.settings_nav_buttons = {}
        for section in ["Launcher", "Java", "Bedrock", "Dungeons", "Dungeons II", "Legends"]:
            b = self.beveled_button(
                nav,
                section,
                lambda s=section: self.show_settings_section(s),
                font_size=9
            )
            b.pack(side="left", padx=(0, 5))
            self.settings_nav_buttons[section] = b

        self.settings_body = self.panel(self.content)
        self.settings_body.pack(fill="both", expand=True)

        self.back_bar(self.content, self.save_settings)
        self.show_settings_section(
            self.get_page_state(
                "settings",
                "section",
                "Launcher"
            )
        )

    def browse_for_folder(self, variable):
        current = variable.get().strip()

        initial_dir = current
        if not initial_dir or not Path(initial_dir).exists():
            initial_dir = str(BASE_DIR)

        chosen = filedialog.askdirectory(
            parent=self,
            initialdir=initial_dir,
            mustexist=False
        )

        if chosen:
            variable.set(
                str(Path(chosen))
            )

    def browse_for_file(self, variable):
        current = variable.get().strip()

        current_path = Path(current) if current else None

        if current_path and current_path.exists():
            initial_dir = str(
                current_path.parent
                if current_path.is_file()
                else current_path
            )
        else:
            initial_dir = str(BASE_DIR)

        chosen = filedialog.askopenfilename(
            parent=self,
            initialdir=initial_dir
        )

        if chosen:
            variable.set(
                str(Path(chosen))
            )


    def settings_entry(
        self,
        parent,
        label,
        var,
        *,
        is_folder=False,
        is_file=False
    ):
        row = tk.Frame(
            parent,
            bg=self.PANEL,
            height=40
        )
        row.pack(
            fill="x",
            padx=16,
            pady=5
        )
        row.pack_propagate(False)

        # Measure the actual rasterized label and reserve that width.
        # This keeps option labels strictly single-line and prevents the
        # entry field from drawing across them.
        label_photo = self._hard_text_photo(
            label,
            9,
            self.TEXT,
            max_width=2000,
            align="left"
        )

        measured = (
            label_photo.width()
            if label_photo is not None
            else len(label) * 10
        )

        label_width = max(
            190,
            min(
                390,
                measured + 22
            )
        )

        label_holder = tk.Frame(
            row,
            bg=self.PANEL,
            width=label_width
        )
        label_holder.pack(
            side="left",
            fill="y"
        )
        label_holder.pack_propagate(False)

        label_widget = tk.Label(
            label_holder,
            bg=self.PANEL,
            fg=self.TEXT,
            anchor="w",
            justify="left"
        )

        if label_photo is not None:
            label_widget._text_photo = label_photo
            label_widget.config(
                image=label_photo,
                text=""
            )
        else:
            label_widget.config(
                text=label,
                font=("Segoe UI", 9)
            )

        label_widget.pack(
            side="left",
            anchor="w",
            pady=8
        )

        # Browse goes at the far right first, then the field consumes the
        # remaining horizontal space. Long labels therefore shorten the field.
        browse = None

        if is_folder or is_file:
            browse_command = (
                (lambda v=var: self.browse_for_folder(v))
                if is_folder
                else (lambda v=var: self.browse_for_file(v))
            )

            browse = self.beveled_button(
                row,
                "Browse",
                browse_command,
                font_size=9,
                tooltip=(
                    "Choose a folder."
                    if is_folder
                    else "Choose a file."
                )
            )
            browse.pack(
                side="right",
                padx=(7, 0)
            )

        entry = tk.Entry(
            row,
            textvariable=var,
            bg=self.PANEL_3,
            fg=self.TEXT,
            insertbackground=self.TEXT,
            relief="sunken",
            bd=3,
            font=("Segoe UI", 10)
        )

        entry.pack(
            side="left",
            fill="x",
            expand=True,
            ipady=2
        )

        return entry


    def settings_dropdown(
        self,
        parent,
        label,
        variable,
        choices
    ):
        row = tk.Frame(
            parent,
            bg=self.PANEL,
            height=40
        )
        row.pack(
            fill="x",
            padx=16,
            pady=5
        )
        row.pack_propagate(False)

        holder = tk.Frame(
            row,
            bg=self.PANEL,
            width=280
        )
        holder.pack(
            side="left",
            fill="y"
        )
        holder.pack_propagate(False)

        title = tk.Label(
            holder,
            bg=self.PANEL,
            fg=self.TEXT,
            anchor="w"
        )
        self._set_pixel_label_text(
            title,
            label,
            9,
            self.TEXT,
            align="left"
        )
        title.pack(
            side="left",
            pady=8
        )

        unique_choices = list(
            dict.fromkeys(
                str(value)
                for value in choices
            )
        )

        dropdown = CustomDropdown(
            row,
            self,
            items=[
                {
                    "label": value,
                    "value": value,
                }
                for value in unique_choices
            ],
            value=variable.get(),
            command=lambda value: variable.set(
                value
            )
        )
        dropdown.pack(
            side="left"
        )
        return dropdown


    def _set_account_censor_setting(
        self,
        key,
        checked
    ):
        value = bool(
            checked
        )

        variable = getattr(
            self,
            "settings_vars",
            {}
        ).get(
            key
        )

        if variable is not None:
            variable.set(
                value
            )

        self.config_data[
            key
        ] = value

        # Privacy preferences are harmless ordinary settings and should apply
        # even if the user leaves Settings through the sidebar instead of the
        # Back/Save control.
        save_config(
            self.config_data
        )


    def settings_privacy_checkboxes(
        self,
        parent
    ):
        row = tk.Frame(
            parent,
            bg=self.PANEL,
            height=40
        )
        row.pack(
            fill="x",
            padx=16,
            pady=5
        )
        row.pack_propagate(False)

        holder = tk.Frame(
            row,
            bg=self.PANEL,
            width=280
        )
        holder.pack(
            side="left",
            fill="y"
        )
        holder.pack_propagate(False)

        title = tk.Label(
            holder,
            bg=self.PANEL,
            fg=self.TEXT,
            anchor="w"
        )
        self._set_pixel_label_text(
            title,
            "Censor on Accounts page",
            9,
            self.TEXT,
            align="left"
        )
        title.pack(
            side="left",
            pady=8
        )

        specs = (
            (
                "Email",
                "censor_account_email"
            ),
            (
                "Microsoft Username",
                "censor_account_microsoft"
            ),
            (
                "Java Username",
                "censor_account_java"
            ),
        )

        for label, key in specs:
            box = PixelCheckbox(
                row,
                self,
                label,
                value=bool(
                    self.settings_vars[
                        key
                    ].get()
                ),
                command=lambda checked, k=key: self._set_account_censor_setting(
                    k,
                    checked
                ),
                font_size=8
            )
            box.pack(
                side="left",
                padx=(0, 10)
            )


    def open_launcher_folder(self):
        try:
            if os.name == "nt":
                os.startfile(
                    str(BASE_DIR)
                )
            else:
                subprocess.Popen(
                    [
                        "xdg-open",
                        str(BASE_DIR),
                    ]
                )
        except Exception as exc:
            self.show_inline_notice(
                "Launcher Folder",
                (
                    "Could not open the launcher folder.\n\n"
                    f"{BASE_DIR}\n\n"
                    f"{type(exc).__name__}: {exc}"
                ),
                back_command=self.show_settings_screen
            )


    def show_settings_section(self, section):
        self.set_page_state(
            "settings",
            "section",
            section
        )
        self.settings_section = section
        for name, button in self.settings_nav_buttons.items():
            button.config(bg=self.GREEN if name == section else self.PANEL_3)

        for child in self.settings_body.winfo_children():
            child.destroy()

        title_holder = tk.Frame(
            self.settings_body,
            bg=self.PANEL,
            height=46
        )
        title_holder.pack(
            fill="x",
            padx=16,
            pady=(10, 4)
        )
        title_holder.pack_propagate(False)

        section_title = tk.Label(
            title_holder,
            bg=self.PANEL,
            fg=self.TEXT,
            anchor="w"
        )
        self._set_pixel_label_text(
            section_title,
            section,
            15,
            self.TEXT
        )
        section_title.pack(
            side="left",
            anchor="w",
            pady=6
        )

        v = self.settings_vars
        if section == "Launcher":
            self.settings_entry(self.settings_body, "Microsoft App Client ID", v["client_id"])
            self.settings_dropdown(
                self.settings_body,
                "Date format",
                v["date_format"],
                [
                    "MM/DD/YYYY",
                    "DD/MM/YYYY",
                    "YYYY/MM/DD",
                    "MM-DD-YYYY",
                    "DD-MM-YYYY",
                    "YYYY-MM-DD",
                ]
            )
            self.settings_privacy_checkboxes(
                self.settings_body
            )

            folder_row = tk.Frame(
                self.settings_body,
                bg=self.PANEL
            )
            folder_row.pack(
                fill="x",
                padx=16,
                pady=(18, 8)
            )

            self.beveled_button(
                folder_row,
                "Browse Launcher Folder",
                self.open_launcher_folder,
                font_size=9,
                tooltip="Open the folder containing SML.py."
            ).pack(
                side="left"
            )

        elif section == "Java":
            self.settings_entry(self.settings_body, ".minecraft folder", v["minecraft_dir"],
            is_folder=True
        )
            self.settings_entry(self.settings_body, "Maximum RAM (MB)", v["java_memory_mb"])
        elif section == "Bedrock":
            self.settings_entry(self.settings_body, "Bedrock data folder", v["bedrock_data_dir"],
            is_folder=True
        )
        elif section == "Dungeons":
            self.settings_entry(self.settings_body, "Dungeons data/save folder", v["dungeons_data_dir"],
            is_folder=True
        )
        elif section == "Dungeons II":
            self.settings_entry(self.settings_body, "Dungeons II data/save folder", v["dungeons2_data_dir"],
            is_folder=True
        )
        elif section == "Legends":
            self.settings_entry(self.settings_body, "Legends data/save folder", v["legends_data_dir"],
            is_folder=True
        )

    def save_settings(self):
        v = self.settings_vars
        try:
            ram = max(512, int(v["java_memory_mb"].get()))
        except ValueError:
            self.show_inline_notice(
                "Invalid RAM",
                "Maximum RAM must be a number.",
                back_command=self.show_settings_screen
            )
            return

        self.config_data.update({
            "client_id": v["client_id"].get().strip(),
            "minecraft_dir": v["minecraft_dir"].get().strip(),
            "java_memory_mb": ram,
            "bedrock_data_dir": v["bedrock_data_dir"].get().strip(),
            "dungeons_data_dir": v["dungeons_data_dir"].get().strip(),
            "dungeons2_data_dir": v["dungeons2_data_dir"].get().strip(),
            "legends_data_dir": v["legends_data_dir"].get().strip(),
            "date_format": v["date_format"].get().strip()
            or "MM/DD/YYYY",
            "censor_account_email": bool(
                v["censor_account_email"].get()
            ),
            "censor_account_microsoft": bool(
                v["censor_account_microsoft"].get()
            ),
            "censor_account_java": bool(
                v["censor_account_java"].get()
            ),
        })
        save_config(self.config_data)
        self.auth = AuthManager(self.config_data)
        self.refresh_all()
        self.back_to_game()

    # ---------- log screen ----------

    def show_about_screen(self):
        self.current_screen = "about"
        self.update_navigation_button_states()
        self.clear_content()

        self.top_title(
            self.content,
            "About"
        )

        panel = self.panel(
            self.content
        )
        panel.pack(
            fill="both",
            expand=True
        )

        inner = tk.Frame(
            panel,
            bg=self.PANEL
        )
        inner.pack(
            fill="both",
            expand=True,
            padx=22,
            pady=20
        )

        title = tk.Label(
            inner,
            bg=self.PANEL,
            fg=self.TEXT,
            anchor="w"
        )
        self._set_pixel_label_text(
            title,
            APP_NAME,
            15,
            self.TEXT,
            align="left"
        )
        title.pack(
            anchor="w",
            pady=(0, 12)
        )

        def rich_paragraph(parts, height=2):
            text_widget = tk.Text(
                inner,
                bg=self.PANEL,
                fg=self.TEXT,
                bd=0,
                highlightthickness=0,
                relief="flat",
                wrap="word",
                height=height,
                width=96,
                padx=0,
                pady=0,
                cursor="arrow",
                font=("Segoe UI", 10),
                takefocus=False
            )

            text_widget.tag_configure(
                "normal",
                foreground=self.TEXT,
                font=("Segoe UI", 10)
            )

            for part_index, part in enumerate(parts):
                if isinstance(part, tuple):
                    label_text, target_url = part
                    tag_name = f"link_{part_index}"
                    text_widget.insert("end", label_text, tag_name)
                    text_widget.tag_configure(
                        tag_name,
                        foreground="#9fd3ff",
                        font=("Segoe UI", 10)
                    )

                    def open_link(_event=None, url=target_url):
                        if url:
                            webbrowser.open(url)

                    def enter_link(_event=None, tag=tag_name):
                        text_widget.config(cursor="hand2")
                        text_widget.tag_configure(
                            tag,
                            underline=True
                        )

                    def leave_link(_event=None, tag=tag_name):
                        text_widget.config(cursor="arrow")
                        text_widget.tag_configure(
                            tag,
                            underline=False
                        )

                    text_widget.tag_bind(
                        tag_name,
                        "<Button-1>",
                        open_link
                    )
                    text_widget.tag_bind(
                        tag_name,
                        "<Enter>",
                        enter_link
                    )
                    text_widget.tag_bind(
                        tag_name,
                        "<Leave>",
                        leave_link
                    )
                else:
                    text_widget.insert(
                        "end",
                        str(part),
                        "normal"
                    )

            text_widget.config(state="disabled")
            text_widget.pack(
                anchor="w",
                fill="x",
                pady=(0, 10)
            )
            return text_widget

        rich_paragraph([
            "Supple Minecraft Launcher (SML) is a small, independent third-party launcher for ",
            (
                "Minecraft",
                "https://www.minecraft.net/en-us"
            ),
            "."
        ], height=1)

        rich_paragraph([
            "Supple Minecraft Launcher is not an official Minecraft product and is not affiliated with, "
            "endorsed by, approved by, or associated with ",
            (
                "Microsoft",
                "https://www.microsoft.com/en-us"
            ),
            " or Mojang Studios."
        ], height=2)

        rich_paragraph([
            "Minecraft, its trademarks and game content belong to Microsoft and Mojang Studios. "
            "Supple Minecraft Launcher only provides tools for signing in, managing local installations, "
            "skins, worlds, downloaded versions, mods, and launching the games the user already has access to."
        ], height=3)

        rich_paragraph([
            "Microsoft sign-in is handled through Microsoft's authentication services. "
            "Supple Minecraft Launcher never asks for or stores your Microsoft password. Saved "
            "authentication data is kept locally and protected with Windows DPAPI."
        ], height=2)

        rich_paragraph([
            (
                "Omniarchive",
                "https://omniarchive.net/"
            ),
            " is used as a source for archived and historical Minecraft versions that are not available through Mojang's standard version manifest."
        ], height=2)

        rich_paragraph([
            (
                "Modrinth",
                "https://modrinth.com/"
            ),
            " is used to provide mod search and installation support from within the launcher."
        ], height=2)

        rich_paragraph([
            "Interface text uses ",
            (
                "GeoFont by Xetheon",
                "https://github.com/Zentheon/GeoFont"
            ),
            ", distributed under the SIL Open Font License 1.1."
        ], height=1)

        divider = tk.Frame(
            inner,
            bg="#4b4b4b",
            height=2
        )
        divider.pack(
            fill="x",
            pady=(0, 10)
        )

        links_title = tk.Label(
            inner,
            bg=self.PANEL,
            fg=self.TEXT,
            anchor="w"
        )
        self._set_pixel_label_text(
            links_title,
            "Links",
            9,
            self.TEXT,
            align="left"
        )
        links_title.pack(
            anchor="w",
            pady=(0, 10)
        )

        about_links = [
            (
                "Minecraft",
                "https://www.minecraft.net/en-us"
            ),
            (
                "Microsoft",
                "https://www.microsoft.com/en-us"
            ),
            (
                "Omniarchive",
                "https://omniarchive.net/"
            ),
            (
                "Modrinth",
                "https://modrinth.com/"
            ),
            (
                "GeoFont by Xetheon",
                "https://github.com/Zentheon/GeoFont"
            ),
            (
                "Supple Minecraft Launcher GitHub",
                "https://github.com/Tcloud7/SuppleMinecraftLauncher"
            ),
        ]

        for link_text, link_url in about_links:
            link = self.link_label(
                inner,
                link_text,
                link_url,
                font_size=9
            )
            link.pack(
                anchor="w",
                pady=(0, 6)
            )

        version_label = tk.Label(
            inner,
            bg=self.PANEL,
            fg=self.MUTED,
            anchor="w"
        )
        self._set_pixel_label_text(
            version_label,
            f"Version {APP_VERSION}",
            9,
            self.MUTED,
            align="left"
        )
        version_label.pack(
            anchor="w",
            pady=(4, 0)
        )

        self.back_bar(
            self.content
        )

    def show_log_screen(self):
        self.current_screen = "log"
        self.update_navigation_button_states()
        self.clear_content()
        self.top_title(self.content, "Log")

        p = self.panel(self.content)
        p.pack(fill="both", expand=True)

        textw = tk.Text(
            p, bg="#0d0d0d", fg="#dddddd",
            insertbackground="white", relief="sunken", bd=3,
            font=("Consolas", 9), wrap="none"
        )
        textw.pack(fill="both", expand=True, padx=10, pady=10)

        contents = LOG_FILE.read_text(encoding="utf-8", errors="replace") if LOG_FILE.exists() else ""
        textw.insert("1.0", contents)
        textw.see("end")
        textw.config(state="disabled")

        row = tk.Frame(p, bg=self.PANEL)
        row.pack(fill="x", padx=10, pady=(0, 10))
        self.beveled_button(row, "Refresh Log", self.show_log_screen).pack(side="left")
        if LOG_FILE.exists():
            self.beveled_button(row, "Open Log File", lambda: os.startfile(str(LOG_FILE))).pack(side="left", padx=7)

        self.back_bar(self.content)

    # ---------- navigation ----------

    def back_to_game(self):
        self.navigate(
            self.show_game,
            self.selected_game
        )

    # ---------- data refresh ----------

    def refresh_all(self):
        for folder in LOCAL_FOLDERS:
            try:
                folder.mkdir(parents=True, exist_ok=True)
            except Exception as exc:
                log(f"Could not create local folder {folder}: {exc}")

        threading.Thread(target=self._discover_worker, daemon=True).start()

        if self.current_screen == "game":
            self.after(0, lambda: self.show_game(self.selected_game))

    def _start_ui_dispatch_poll(self):
        if self._ui_dispatch_poll_started:
            return

        self._ui_dispatch_poll_started = True
        self.after(
            50,
            self._poll_ui_dispatch
        )

    def _poll_ui_dispatch(self):
        try:
            while True:
                callback = self._ui_dispatch_queue.get_nowait()
                try:
                    callback()
                except Exception as exc:
                    log(
                        "Queued UI callback failed: "
                        f"{type(exc).__name__}: {exc}"
                    )
        except queue.Empty:
            pass

        try:
            self.after(
                50,
                self._poll_ui_dispatch
            )
        except tk.TclError:
            self._ui_dispatch_poll_started = False

    def dispatch_to_ui(self, callback):
        self._ui_dispatch_queue.put(callback)


    def _start_discovery_poll(self):
        """
        Start one main-thread polling loop for background game discovery.
        Background threads must never call Tk methods directly.
        """
        if self._discovery_poll_started:
            return

        self._discovery_poll_started = True
        self.after(
            100,
            self._poll_discovery_results
        )

    def _poll_discovery_results(self):
        """
        Runs only on Tk's main thread. Apply every completed discovery result
        currently waiting in the thread-safe queue.
        """
        try:
            while True:
                result = self._discovery_results.get_nowait()

                if isinstance(result, Exception):
                    log(
                        "Game discovery failed: "
                        f"{type(result).__name__}: {result}"
                    )
                    continue

                self._apply_games(result)

        except queue.Empty:
            pass

        # Keep one lightweight polling loop alive for future Refresh presses.
        try:
            self.after(
                100,
                self._poll_discovery_results
            )
        except tk.TclError:
            # Window is closing/destroyed.
            self._discovery_poll_started = False

    def _discover_worker(self):
        try:
            games = discover_games()
            self._discovery_results.put(games)
        except Exception as exc:
            self._discovery_results.put(exc)


    def _apply_games(self, games):
        self.games = games

        for game in (
            "Bedrock",
            "Dungeons",
            "Dungeons II",
            "Legends"
        ):
            self.game_available[game] = bool(
                games.get(game)
            )

        if self.current_screen == "game":
            self.show_game(
                self.selected_game
            )

    def refresh_accounts(self):
        accounts = self._ordered_accounts(self.auth.accounts())
        self.account_map = {}
        items = []

        selected_hid = self.config_data.get(
            "selected_account",
            ""
        )

        for account in accounts:
            hid = account.get(
                "home_account_id",
                ""
            )

            # Java Edition should identify the account by its Minecraft Java
            # profile name. Other games use the Xbox/Microsoft-side username.
            if self.selected_game == "Java Edition":
                label = getattr(
                    self,
                    "_cached_java_names_by_hid",
                    {}
                ).get(
                    hid,
                    ""
                )

                if not label:
                    email = self._account_email(
                        account
                    )
                    label = local_launcher_java_profile_name(
                        Path(
                            self.config_data.get(
                                "minecraft_dir",
                                str(MC_DIR)
                            )
                        ),
                        email
                    )

                if not label:
                    label = "Java Profile"
            else:
                label = getattr(
                    self,
                    "_cached_gamertags_by_hid",
                    {}
                ).get(
                    hid,
                    ""
                )

                if not label:
                    label = self._account_microsoft_name(
                        account
                    )

            self.account_map[label] = hid

            items.append({
                "label": label,
                "value": hid,
                "actions": [],
            })

        if hasattr(self, "account_dropdown"):
            self.account_dropdown.set_items(
                items
            )

            if not items:
                self.config_data[
                    "selected_account"
                ] = ""

                save_config(
                    self.config_data
                )

                self.account_dropdown.set(
                    "",
                    notify=False
                )

                self.account_dropdown.set_enabled(
                    False,
                    tooltip="No Microsoft accounts have been added yet."
                )

                if self.current_screen == "game" and self.selected_game == "Java Edition":
                    self.update_mod_button_state()
                return

            self.account_dropdown.set_enabled(
                True,
                tooltip=(
                    "Select the Minecraft Java profile to use."
                    if self.selected_game == "Java Edition"
                    else "Select which Microsoft/Xbox account this game should use."
                )
            )

            valid_values = {
                item["value"]
                for item in items
            }

            if selected_hid in valid_values:
                self.account_dropdown.set(
                    selected_hid,
                    notify=False
                )
            else:
                selected_hid = items[0]["value"]

                self.config_data[
                    "selected_account"
                ] = selected_hid

                save_config(
                    self.config_data
                )

                self.account_dropdown.set(
                    selected_hid,
                    notify=False
                )

        if self.current_screen == "game" and self.selected_game == "Java Edition":
            self.update_mod_button_state()


    def _version_filter_changed(
        self,
        category,
        checked
    ):
        current = self.get_page_state(
            "java",
            "version_filters",
            {}
        )

        if not isinstance(
            current,
            dict
        ):
            current = {}

        current[category] = bool(
            checked
        )

        self.set_page_state(
            "java",
            "version_filters",
            current
        )

        self.refresh_versions()


    def _active_version_filters(self):
        defaults = {
            "Releases": True,
            "Release Candidates": True,
            "Pre-Releases": True,
            "Snapshots": True,
            "Mod Loaders": True,
            "Alpha": True,
            "Beta": True,
            "Classic": True,
            "Misc": True,
        }

        widgets = getattr(
            self,
            "version_filter_widgets",
            {}
        )

        if widgets:
            return {
                category: bool(
                    widget.get()
                )
                for category, widget in widgets.items()
            }

        stored = self.get_page_state(
            "java",
            "version_filters",
            defaults
        )

        if not isinstance(
            stored,
            dict
        ):
            return defaults

        return {
            category: bool(
                stored.get(
                    category,
                    default
                )
            )
            for category, default in defaults.items()
        }


    def _download_version_placeholder(
        self,
        version_id
    ):
        messagebox.showinfo(
            "Download Version",
            (
                f"Downloading {version_id} is not implemented yet.\n\n"
                "The version is present in the Omniarchive-derived index, "
                "so this button is reserved for the future downloader."
            )
        )


    def _refresh_mojang_latest_async(self):
        """Refresh Mojang's latest release/snapshot once per launcher run.

        The full Omniarchive-derived catalog is intentionally cached, but the
        two "Latest" shortcuts should track Mojang's live manifest instead of
        being frozen to the last catalog build.  This fetch is deliberately
        asynchronous so opening the Java page never waits on the network.
        """
        if (
            self._mojang_latest_checked_session
            or self._mojang_latest_fetch_inflight
        ):
            return

        current = load_versionref()
        if (
            not current.get("catalog_fetched")
            or int(current.get("schema_version", 0) or 0) < VERSIONREF_SCHEMA_VERSION
        ):
            # A full catalog rebuild already downloads Mojang's manifest and
            # stores its live latest IDs. Avoid racing two writers.
            return

        self._mojang_latest_checked_session = True
        self._mojang_latest_fetch_inflight = True

        def worker():
            try:
                mojang_catalog = fetch_mojang_version_catalog()
                latest = dict(mojang_catalog.pop("_latest", {}) or {})

                if not latest.get("release") and not latest.get("snapshot"):
                    return

                data = load_versionref()
                data["mojang_latest"] = latest

                versions = data.get("versions", [])
                by_id = {
                    str(item.get("id", "")): item
                    for item in versions
                    if isinstance(item, dict) and item.get("id")
                }

                # Ensure a brand-new Mojang release/snapshot can appear at the
                # top even when the long-lived historical catalog predates it.
                for kind in ("release", "snapshot"):
                    version_id = str(latest.get(kind, "") or "").strip()
                    if not version_id:
                        continue

                    meta = mojang_catalog.get(version_id, {})
                    item = by_id.get(version_id)

                    if item is None:
                        item = {
                            "id": version_id,
                            "display_id": version_id,
                            "aliases": [],
                            "release_date": str(meta.get("release_date", "") or ""),
                            "category": _version_category(version_id),
                            "installed": False,
                            "catalogued": True,
                            "archived": True,
                            "download_available": True,
                            "source": "Mojang",
                        }
                        versions.append(item)
                        by_id[version_id] = item
                    else:
                        item["catalogued"] = True
                        item["archived"] = True
                        item["download_available"] = True
                        item["source"] = "Mojang"
                        if meta.get("release_date"):
                            item["release_date"] = meta["release_date"]

                save_versionref(data)
                self.dispatch_to_ui(self.refresh_versions)

            except Exception as exc:
                log(
                    "Mojang latest-version refresh failed: "
                    f"{type(exc).__name__}: {exc}"
                )
            finally:
                self._mojang_latest_fetch_inflight = False

        threading.Thread(target=worker, daemon=True).start()


    def _ensure_version_catalog_async(self):
        data = load_versionref()

        if (
            data.get(
                "catalog_fetched"
            )
            and int(
                data.get(
                    "schema_version",
                    0
                )
                or 0
            )
            >= VERSIONREF_SCHEMA_VERSION
        ):
            return

        if self._version_catalog_fetch_inflight:
            return

        self._version_catalog_fetch_inflight = True

        def worker():
            try:
                response = requests.get(
                    OMNI_VERSION_DATA_URL,
                    timeout=30,
                    headers={
                        "User-Agent": "Supple-Launcher/0.1"
                    }
                )
                response.raise_for_status()

                catalog = _parse_omniarchive_derived_java_yaml(
                    response.text
                )

                if not catalog:
                    raise RuntimeError(
                        "The Omniarchive-derived version catalog was empty."
                    )

                try:
                    mojang_catalog = fetch_mojang_version_catalog()
                except Exception as exc:
                    log(
                        "Mojang version manifest fetch failed: "
                        f"{type(exc).__name__}: {exc}"
                    )
                    mojang_catalog = {}

                omni_archived = set()

                try:
                    omni_archived.update(
                        fetch_omniarchive_index_archived_versions()
                    )
                except Exception as exc:
                    log(
                        "Omniarchive index availability fetch failed: "
                        f"{type(exc).__name__}: {exc}"
                    )

                try:
                    omni_archived.update(
                        fetch_omniarchive_client_versions()
                    )
                except Exception as exc:
                    log(
                        "Omniarchive Vault scan failed: "
                        f"{type(exc).__name__}: {exc}"
                    )

                mojang_latest = dict(
                    mojang_catalog.get(
                        "_latest",
                        {}
                    )
                    if isinstance(
                        mojang_catalog,
                        dict
                    )
                    else {}
                )

                if isinstance(
                    mojang_catalog,
                    dict
                ):
                    mojang_catalog.pop(
                        "_latest",
                        None
                    )

                catalog = apply_version_sources(
                    catalog,
                    mojang_catalog,
                    omni_archived
                )

                mc_dir = Path(
                    self.config_data.get(
                        "minecraft_dir",
                        str(MC_DIR)
                    )
                )
                installed = java_versions(
                    mc_dir
                )

                installed_set = set(
                    installed
                )

                for item in catalog:
                    item["installed"] = (
                        item["id"]
                        in installed_set
                    )

                # Add local-only versions such as Fabric/Forge profiles.
                catalog_ids = {
                    item["id"]
                    for item in catalog
                }

                for version_id in installed:
                    if version_id in catalog_ids:
                        continue

                    catalog.append({
                        "id": version_id,
                        "release_date": _local_version_release_date(
                            mc_dir,
                            version_id
                        ),
                        "category": _version_category(
                            version_id
                        ),
                        "installed": True,
                        "catalogued": False,
                        "download_available": False,
                        "archived": True,
                        "source": (
                            _version_loader_source(
                                version_id
                            )
                            or "Local"
                        ),
                    })

                save_versionref({
                    "schema_version": VERSIONREF_SCHEMA_VERSION,
                    "catalog_fetched": True,
                    "fetched_at": datetime.now(
                        timezone.utc
                    ).isoformat(),
                    "source": "Omniarchive index",
                    "source_url": OMNI_INDEX_URL,
                    "mirror_url": OMNI_VERSION_DATA_URL,
                    "mojang_latest": mojang_latest,
                    "versions": catalog,
                })

                self.dispatch_to_ui(
                    self.refresh_versions
                )

            except Exception as exc:
                log(
                    "Version catalog fetch failed: "
                    f"{type(exc).__name__}: {exc}"
                )

            finally:
                self._version_catalog_fetch_inflight = False

        threading.Thread(
            target=worker,
            daemon=True
        ).start()


    def refresh_versions(self):
        mc_dir = Path(
            self.config_data.get(
                "minecraft_dir",
                str(MC_DIR)
            )
        )

        installed = java_versions(
            mc_dir
        )

        data = update_versionref_installed_state(
            mc_dir,
            installed
        )

        self._ensure_version_catalog_async()
        self._refresh_mojang_latest_async()

        if not hasattr(
            self,
            "version_dropdown"
        ):
            return

        active_filters = self._active_version_filters()
        date_format = self.config_data.get(
            "date_format",
            "MM/DD/YYYY"
        )
        installed_set = set(
            installed
        )

        def make_item(
            item,
            special_label=None
        ):
            version_id = str(
                item.get(
                    "id",
                    ""
                )
            ).strip()

            display_id = str(
                item.get(
                    "display_id",
                    ""
                )
                or version_id
            ).strip()

            owned_ids = {
                version_id,
                display_id,
            }
            if isinstance(item.get("aliases", []), list):
                owned_ids.update(
                    str(alias).strip()
                    for alias in item.get("aliases", [])
                    if str(alias).strip()
                )

            installed_here = bool(
                item.get("installed")
                or (owned_ids & installed_set)
            )
            catalogued = bool(
                item.get(
                    "catalogued"
                )
            )
            archived = bool(
                item.get(
                    "archived",
                    True
                )
            )

            source_text = str(
                item.get(
                    "source",
                    "Unknown"
                )
                or "Unknown"
            )

            actions = []

            if (
                not installed_here
                and catalogued
            ):
                can_download = bool(
                    archived
                    and item.get(
                        "download_available",
                        True
                    )
                )

                actions.append({
                    "label": "Download",
                    "enabled": can_download,
                    "tooltip": (
                        "Download support is not implemented yet."
                        if can_download
                        else "This version is documented but no archived client was found."
                    ),
                    "command": (
                        lambda v=version_id:
                        self._download_version_placeholder(
                            v
                        )
                    )
                })

            if installed_here:
                label_color = self.TEXT
            elif (
                catalogued
                and not archived
            ):
                label_color = "#d75b5b"
            else:
                label_color = "#000000"

            local_value = version_id

            if installed_here:
                possible_local_ids = [
                    version_id,
                    display_id,
                ]

                possible_local_ids.extend(
                    item.get(
                        "aliases",
                        []
                    )
                    if isinstance(
                        item.get(
                            "aliases",
                            []
                        ),
                        list
                    )
                    else []
                )

                for candidate in possible_local_ids:
                    if candidate in installed_set:
                        local_value = candidate
                        break

            return {
                "label": (
                    special_label
                    if special_label
                    else display_id
                ),
                "value": local_value,
                "right_text": _version_date_display(
                    item.get(
                        "release_date",
                        ""
                    ),
                    date_format
                ),
                "source_text": source_text,
                "label_color": label_color,
                "selectable": installed_here,
                "actions": actions,
                "_sort_date": str(
                    item.get(
                        "release_date",
                        ""
                    )
                    or ""
                ),
                "_installed": installed_here,
            }

        all_versions = [
            item
            for item in data.get(
                "versions",
                []
            )
            if str(
                item.get(
                    "id",
                    ""
                )
            ).strip()
        ]

        by_id = {
            str(
                item.get(
                    "id",
                    ""
                )
            ): item
            for item in all_versions
            if item.get(
                "id"
            )
        }

        mojang_latest = data.get(
            "mojang_latest",
            {}
        )

        if not isinstance(
            mojang_latest,
            dict
        ):
            mojang_latest = {}

        latest_release_id = str(
            mojang_latest.get(
                "release",
                ""
            )
            or ""
        )
        latest_snapshot_id = str(
            mojang_latest.get(
                "snapshot",
                ""
            )
            or ""
        )

        top_items = []

        latest_release = by_id.get(
            latest_release_id
        )

        if latest_release is not None:
            top_items.append(
                make_item(
                    latest_release,
                    (
                        "Latest Release - "
                        + str(
                            latest_release.get(
                                "display_id",
                                latest_release_id
                            )
                        )
                    )
                )
            )

        latest_snapshot = by_id.get(
            latest_snapshot_id
        )

        if latest_snapshot is not None:
            top_items.append(
                make_item(
                    latest_snapshot,
                    (
                        "Latest Snapshot - "
                        + str(
                            latest_snapshot.get(
                                "display_id",
                                latest_snapshot_id
                            )
                        )
                    )
                )
            )


        items = []

        for item in all_versions:
            category = str(
                item.get(
                    "category",
                    "Misc"
                )
            )

            if not active_filters.get(
                category,
                True
            ):
                continue

            items.append(
                make_item(
                    item
                )
            )

        def sort_key(row):
            date = row.get(
                "_sort_date",
                ""
            )
            installed_here = bool(
                row.get(
                    "_installed"
                )
            )

            if not date:
                return (
                    2
                    if installed_here
                    else 0,
                    "",
                    row["label"].casefold()
                )

            return (
                1,
                date,
                row["label"].casefold()
            )

        items.sort(
            key=sort_key,
            reverse=True
        )

        items = (
            top_items
            + items
        )

        for item in items:
            item.pop(
                "_sort_date",
                None
            )
            item.pop(
                "_installed",
                None
            )

        self.version_dropdown.set_items(
            items
        )

        if not installed:
            self.version_dropdown.set(
                "",
                notify=False
            )
            self.version_dropdown.set_enabled(
                bool(items),
                tooltip=(
                    "Browse Minecraft Java versions."
                    if items
                    else "No Java versions were detected."
                )
            )
            self.update_mod_button_state()
            return

        self.version_dropdown.set_enabled(
            True,
            tooltip=(
                "Installed versions are bright. "
                "Unavailable archived versions are black. "
                "Unarchived versions are red."
            )
        )

        installation = self.selected_installation_data()
        wanted = installation.get(
            "version",
            ""
        )

        if wanted not in installed_set:
            wanted = self.config_data.get(
                "selected_java_version",
                ""
            )

        if wanted in installed_set:
            self.version_dropdown.set(
                wanted,
                notify=False
            )
        else:
            first_installed = next(
                (
                    row["value"]
                    for row in items
                    if row.get(
                        "selectable"
                    )
                ),
                installed[-1]
            )

            self.version_dropdown.set(
                first_installed,
                notify=False
            )
            self._version_changed(
                first_installed
            )

        if (
            self.current_screen == "game"
            and self.selected_game
            == "Java Edition"
        ):
            self.update_mod_button_state()


    def _account_changed(self, _event=None):
        return
    def _account_changed_custom(self, home_account_id):
        self.config_data["selected_account"]=home_account_id; save_config(self.config_data)


    # ---------- management ----------

    def _open_path(self, path, description):
        path = Path(path)
        if path.exists():
            os.startfile(str(path))
        else:
            messagebox.showinfo(description, f"The folder was not found yet:\n\n{path}")

    def run_tool(self, action):
        action = str(action or "")

        action_map = {
            "java": "Java Edition",
            "bedrock": "Bedrock",
            "dungeons": "Dungeons",
            "dungeons2": "Dungeons II",
            "legends": "Legends",
        }

        prefix, _, suffix = action.partition("_")
        game = action_map.get(prefix, self.selected_game)

        if suffix == "main":
            self.navigate(
                self.show_game,
                game
            )
            return

        title = next(
            (
                label
                for label, candidate_action in GAME_TOOLS.get(game, [])
                if candidate_action == action
            ),
            suffix.replace("_", " ").title() or "Page"
        )

        self.current_screen = "game_placeholder"
        self.selected_game = game
        self.update_navigation_button_states()
        self.show_inline_notice(
            title,
            "Placeholder",
            back_command=lambda g=game: self.navigate(
                self.show_game,
                g
            )
        )

    # ---------- launch ----------

    def play_selected(self):
        if self.selected_game != "Java Edition":
            info = self.games.get(
                self.selected_game
            )

            if not info:
                self.buy_selected_game()
                return

            try:
                log(
                    f"Launching {self.selected_game}: "
                    f"{info['appid']}"
                )
                launch_aumid(
                    info["appid"]
                )
            except Exception as exc:
                log(
                    f"{self.selected_game} launch failed: "
                    f"{exc}"
                )
                messagebox.showerror(
                    "Launch failed",
                    str(exc)
                )
            return

        hid = self.config_data.get(
            "selected_account",
            ""
        )
        installation = self.selected_installation_data()
        version = installation.get("version", "")

        if not version and hasattr(self, "version_dropdown"):
            version = self.version_dropdown.get()

        if not hid:
            self.navigate(
                self.show_accounts_screen
            )
            return

        if not version:
            self._set_details(
                "No installed Java version is selected."
            )
            return

        self.config_data[
            "selected_java_version"
        ] = version
        save_config(
            self.config_data
        )

        self.play_button._base_bg = self.GREEN_DISABLED
        self.set_button_enabled(
            self.play_button,
            False,
            tooltip="Authenticating and preparing Java Edition..."
        )
        self._set_details(
            "Authenticating and verifying Java Edition..."
        )

        def worker():
            try:
                session = self.auth.minecraft_session(
                    hid
                )

                self.game_available[
                    "Java Edition"
                ] = True
                self.game_available[
                    "Bedrock"
                ] = True

                sync_installation_mods(
                    Path(
                        self.config_data.get(
                            "minecraft_dir",
                            str(MC_DIR)
                        )
                    ),
                    installation
                )

                launch_java(
                    Path(
                        self.config_data.get(
                            "minecraft_dir",
                            str(MC_DIR)
                        )
                    ),
                    version,
                    session,
                    int(
                        self.config_data.get(
                            "java_memory_mb",
                            4096
                        )
                    ),
                    self.config_data.get(
                        "client_id",
                        ""
                    ),
                )

                self.after(
                    0,
                    lambda: self._set_details(
                        f"Started {version} as "
                        f"{session['name']}."
                    )
                )

            except Exception as exc:
                log(
                    f"Java launch error: {exc}"
                )

                if (
                    "did not return a Minecraft: Java Edition profile"
                    in str(exc)
                ):
                    self.game_available[
                        "Java Edition"
                    ] = False
                    self.game_available[
                        "Bedrock"
                    ] = False

                self.after(
                    0,
                    lambda: self._set_details(
                        f"Java launch failed.\n\n{exc}"
                    )
                )

                self.after(
                    0,
                    self.update_game_status
                )

            finally:
                def restore():
                    if (
                        self.current_screen == "game"
                        and self.selected_game == "Java Edition"
                    ):
                        self.update_game_status()

                self.after(
                    0,
                    restore
                )

        threading.Thread(
            target=worker,
            daemon=True
        ).start()


if __name__ == "__main__":
    if os.name != "nt":
        raise SystemExit("This version currently supports Windows only.")
    Launcher().mainloop()
