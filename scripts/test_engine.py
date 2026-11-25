#!/usr/bin/env python3
"""Exercise the runtime-weight engine and record real command costs."""
import json
import os
from pathlib import Path
import resource
import subprocess
import time

root = Path(__file__).resolve().parent.parent
out = root / "pilot/engine"
env = dict(os.environ, CARGO_BUILD_JOBS="4")
cmd = ["nice", "-n", "10", "cargo", "test", "--release", "--", "--nocapture", "--test-threads=1"]
start = time.monotonic()
with (out / "rust-tests.log").open("w") as log:
    result = subprocess.run(cmd, cwd=root / "rust/engine", env=env, stdout=log, stderr=subprocess.STDOUT)
receipt = {"command": cmd, "cwd": "rust/engine", "exit": result.returncode,
           "wall_seconds": time.monotonic() - start,
           "peak_rss_kib": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}
(out / "rust-tests.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps(receipt))
raise SystemExit(result.returncode)
