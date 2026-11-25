#!/usr/bin/env python3
"""Run one Lean module with the shared host's mandatory resource envelope."""
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time

root = Path(__file__).resolve().parent.parent
module = sys.argv[1]
label = sys.argv[2]
out = root / "pilot/engine"
env = dict(os.environ)
env["PATH"] = str(Path.home() / ".elan/bin") + ":" + env["PATH"]
env["XDG_RUNTIME_DIR"] = f"/run/user/{os.getuid()}"
env["CI"] = "1"
mem = subprocess.check_output(["free", "-g"], text=True)
available = int(next(line for line in mem.splitlines() if line.startswith("Mem:")).split()[-1])
if available < 12:
    raise SystemExit("Need 12 GiB available; refusing Lean check")
action = ["lake", "env", "leanchecker", module] if "--replay" in sys.argv[3:] else ["lake", "build", module]
cmd = ["flock", "/home/thomas/.hermes/cache/scratch/lean-single-check.lock",
       "systemd-run", "--user", "--scope", "-p", "MemoryMax=6G", "-p", "CPUQuota=200%",
       "env", "LEAN_NUM_THREADS=2", "CI=1", *action]
start = time.monotonic()
with (out / (label + ".log")).open("w") as log:
    result = subprocess.run(cmd, cwd=root / "lean", env=env, stdout=log, stderr=subprocess.STDOUT)
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
receipt = {"command": cmd, "module": module, "exit": result.returncode,
           "wall_seconds": time.monotonic() - start, "peak_rss_kib": usage.ru_maxrss,
           "available_gib_before": available, "rss_method": "getrusage(RUSAGE_CHILDREN), Linux KiB"}
(out / (label + ".json")).write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps(receipt))
raise SystemExit(result.returncode)
