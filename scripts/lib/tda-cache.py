#!/usr/bin/env python3
"""Compute the TDA Lake build cache keys.

Two keys are derived from the same validated inputs:

- the compatibility key, over `lean-toolchain`, `lake-manifest.json` and this
  helper's own bytes, which a lakefile-only change leaves unchanged; and
- the full key, over those same inputs plus the canonical `lakefile.toml`.

A restore can fall back from the full key to the compatibility key so a
lakefile-only change (for example, adding a `[[lean_lib]]`) still finds a
usable cache: Lake re-verifies source-content and dependency traces during
the build that follows, so a restored cache from a different lakefile can
never make it skip rebuilding something that changed.
"""

import hashlib
import json
from pathlib import Path
import sys

try:
    import tomllib
except ModuleNotFoundError:
    tomllib = None


ROOT = Path(__file__).resolve().parents[2]
DOMAIN_COMPAT = b"tda-build-v3-compat\0"
DOMAIN_FULL = b"tda-build-v3-full\0"


class CacheKeyError(Exception):
    """An input cannot be represented safely by this key schema."""


def read_nonempty(path, label):
    try:
        data = path.read_bytes()
    except OSError as error:
        detail = error.strerror or str(error)
        raise CacheKeyError(f"cannot read {label}: {detail}") from None
    if not data:
        raise CacheKeyError(f"{label} must not be empty")
    return data


def encode_value(value, location="$"):
    """Return the tagged canonical form for one supported TOML value."""
    if type(value) is dict:
        if any(type(key) is not str for key in value):
            raise CacheKeyError(f"unsupported TOML table key at {location}")
        items = []
        for key in sorted(value):
            items.append([key, encode_value(value[key], f"{location}.{key}")])
        return ["table", items]
    if type(value) is list:
        return ["array", [encode_value(item, f"{location}[{index}]")
                           for index, item in enumerate(value)]]
    if type(value) is str:
        return ["string", value]
    if type(value) is bool:
        return ["bool", value]
    if type(value) is int:
        return ["integer", str(value)]
    raise CacheKeyError(
        f"unsupported TOML value type {type(value).__name__} at {location}"
    )


def reject_json_constant(value):
    raise ValueError(f"invalid JSON constant {value}")


def framed_update(digest, name, payload):
    name_bytes = name.encode("ascii")
    digest.update(name_bytes + b"\0")
    digest.update(str(len(payload)).encode("ascii") + b"\0")
    digest.update(payload)


def read_inputs():
    """Read and validate every input, failing closed on anything unsafe to hash."""
    if tomllib is None:
        raise CacheKeyError("Python 3.11 or later with tomllib is required")

    alternative = ROOT / "lakefile.lean"
    if alternative.is_symlink() or alternative.exists():
        raise CacheKeyError("lakefile.lean is unsupported for the TDA cache key")

    toolchain = read_nonempty(ROOT / "lean-toolchain", "lean-toolchain")
    manifest = read_nonempty(ROOT / "lake-manifest.json", "lake-manifest.json")
    manifest_text = manifest.decode("utf-8")
    manifest_value = json.loads(manifest_text, parse_constant=reject_json_constant)
    if type(manifest_value) is not dict:
        raise CacheKeyError("lake-manifest.json must contain a JSON object")

    config_bytes = read_nonempty(ROOT / "lakefile.toml", "lakefile.toml")
    config_text = config_bytes.decode("utf-8")
    config = tomllib.loads(config_text)
    if type(config) is not dict:
        raise CacheKeyError("lakefile.toml must contain a TOML table")

    if "version" in config:
        version = config["version"]
        if type(version) is not str or not version:
            raise CacheKeyError("top-level package version must be a nonempty string")
        del config["version"]

    canonical_config = json.dumps(
        encode_value(config), ensure_ascii=False, separators=(",", ":"), allow_nan=False
    ).encode("utf-8")
    helper_bytes = read_nonempty(Path(__file__).resolve(), "scripts/lib/tda-cache.py")

    return toolchain, manifest, canonical_config, helper_bytes


def compat_key(toolchain, manifest, helper_bytes):
    digest = hashlib.sha256()
    digest.update(DOMAIN_COMPAT)
    for name, payload in (
        ("lean-toolchain", toolchain),
        ("lake-manifest.json", manifest),
        ("scripts/lib/tda-cache.py", helper_bytes),
    ):
        framed_update(digest, name, payload)
    return digest.hexdigest()


def full_key(toolchain, manifest, canonical_config, helper_bytes):
    digest = hashlib.sha256()
    digest.update(DOMAIN_FULL)
    for name, payload in (
        ("lean-toolchain", toolchain),
        ("lake-manifest.json", manifest),
        ("lakefile.toml", canonical_config),
        ("scripts/lib/tda-cache.py", helper_bytes),
    ):
        framed_update(digest, name, payload)
    return digest.hexdigest()


def cache_keys():
    """Return (compat, full) hex digests computed from the same validated inputs."""
    toolchain, manifest, canonical_config, helper_bytes = read_inputs()
    return (
        compat_key(toolchain, manifest, helper_bytes),
        full_key(toolchain, manifest, canonical_config, helper_bytes),
    )


def main(argv):
    if argv != ["key"]:
        print("usage: tda-cache.py key", file=sys.stderr)
        return 64
    try:
        compat, full = cache_keys()
    except (CacheKeyError, OSError, UnicodeError, ValueError, TypeError, RecursionError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    sys.stdout.write(f"compat={compat}\n")
    sys.stdout.write(f"full={full}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
