#!/usr/bin/env python3
"""Build the private E6 page manifest and deterministic ZIP from staged outputs."""

import argparse
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "evidence/e6-wasm"
MANIFEST = "evidence/e6-wasm/build-manifest.json"
PINS = {
    "rust/general_engine/src/lib.rs": "3fafdba15648738c43e1aa6893eccfcd73e4a1474352ba356a4e02ff31dff6e4",
    "weights/tiny_bytelm_v1.bin": "c3575e46dce2bc1027955f34d29e87c23540ea28c3ead3e80c329c5cc1abac87",
    "weights/mod113_v1.bin": "ec144a43c93fb16ca7e40f4792b5296adda78e8cb9dbf036fbf8a7890ecb6dfc",
}
PAGE = (
    "web/index.html", "web/app.js", "web/style.css", "web/general_engine_wasm.wasm",
    "weights/tiny_bytelm_v1.bin", "weights/mod113_v1.bin",
)
REFERENCE = "evidence/e6-wasm/native-general.json"
BUILD_INPUTS = (
    "rust/rust-toolchain.toml", "rust/general_engine/Cargo.toml", "rust/general_engine/Cargo.lock",
    "rust/general_engine_wasm/Cargo.toml", "rust/general_engine_wasm/Cargo.lock",
    "rust/general_engine_wasm/src/lib.rs", "rust/general_engine_wasm/examples/e6_native.rs",
    "web/build.sh",
)


def digest(name):
    buf = (ROOT / name).read_bytes()
    return {"bytes": len(buf), "sha256": hashlib.sha256(buf).hexdigest()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest-only", action="store_true")
    args = parser.parse_args()
    for name, expected in PINS.items():
        if digest(name)["sha256"] != expected:
            raise SystemExit(f"Frozen asset hash mismatch: {name}")
    if (ROOT / "web/general_engine_wasm.wasm").read_bytes()[:8] != b"\0asm\x01\0\0\0":
        raise SystemExit("Expected a Wasm v1 module")
    manifest = {
        "build": {
            "rust": "1.99.1 (58cf8f9c3)", "target": "wasm32-unknown-unknown",
            "profile": "release", "offline": True, "locked": True,
            "overflow_checks": True, "jobs": 2, "engine_dependency": "../general_engine",
        },
        "provenance": {
            "integration": "3f0de5de22cecea941fe586fca39a47fc305368a",
            "e4_engine": "e54c7ffab83521246e1f5372a92b57c1168fb756",
            "e5_weights": "b4a0bc8a2c0262cb31d853480769e99419659000",
            "e6_ui_base": "f6aa052a5f035ae7392d39d80cfb26c088464c7e",
        },
        "files": {name: digest(name) for name in (*PAGE, *BUILD_INPUTS, *PINS, REFERENCE)},
    }
    (ROOT / MANIFEST).write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    if args.manifest_only:
        return
    archive = EVIDENCE / "private-local-page.zip"
    with zipfile.ZipFile(archive, "w") as z:
        for name in sorted((*PAGE, MANIFEST, REFERENCE, "scripts/e6_browser_replay.js",
                            "evidence/e6-wasm/README.md")):
            entry = zipfile.ZipInfo(name, date_time=(2026, 11, 23, 0, 0, 0))
            entry.create_system = 3
            entry.external_attr = 0o100644 << 16
            z.writestr(entry, (ROOT / name).read_bytes(), compress_type=zipfile.ZIP_STORED)
    (EVIDENCE / "package.sha256").write_text(
        hashlib.sha256(archive.read_bytes()).hexdigest() + "  " + archive.name + "\n")
    print(archive)


if __name__ == "__main__":
    main()
