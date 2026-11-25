#!/usr/bin/env python3
"""One-shot trained-engine build on an ALREADY AUTHORIZED dedicated Debian x86_64 box.

Local (no Lean, installs, network, provisioning or spend):
  scripts/box_trained.sh plan
  scripts/box_trained.sh dry-run --checkpoint /path/best.npz --out pilot/engine/box3-dry
  python3 -B scripts/box_trained_test.py

Dedicated box only (root, systemd, >=4 CPUs, >=16 GiB RAM, >=40 GiB free):
  sudo scripts/box_trained.sh run --dedicated-debian --repo <git-url-or-path> \
    --commit <full-40-character-sha> --checkpoint /path/best.npz --out /srv/box3-run

The output directory must not exist. All logs/receipts survive failures. An accepted.json
is written ONLY after build, exact axiom audit, fresh replay, independent nanoda, and
an unpermitted-axiom planted-fault control. This control tests the independent axiom
gate, not weight sensitivity or Rust execution. No box is created by this command.
The entire worker is capped at 12 GiB / 4 CPUs / 6 hours; Lake uses two threads.
Debian packages and Mathlib cache are transport dependencies, not proof conclusions.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
MODULE = "LcnExec.Engine.TrainedFinal"
THEOREM = "LcnExec.Engine.trained_engine_adds"
STANDARD = ["propext", "Classical.choice", "Quot.sound"]
TOOLCHAIN = "leanprover/lean4:v4.35.0"
AENEAS = "d1e177bb9fdc17fa62e730d524ac905ba19776ed"
ELAN_SHA = "42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63"
BINARY_PINS = {
    "nanoda_bin": "cbf13950fc4a48f635a0beceeb5ed32dd82568b870cfd081b6391c1f2cf02ba5",
    "leanexport": "f6a6483d518a11b323c28b9bac176d2220df0e9fc3230833815db9586669c074",
}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for b in iter(lambda: f.read(1024 * 1024), b""):
            h.update(b)
    return h.hexdigest()


def save(path, value):
    require(Path(path).name != "accepted.json", "acceptance requires the dedicated worker final gate")
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def write_acceptance(args, value):
    require(args.mode == "_worker" and os.environ.get("BOX_TRAINED_WORKER") == "1",
            "acceptance requires run's dedicated worker, never plan or dry-run")
    require(value.get("accepted") is True, "missing acceptance verdict")
    expected = {"charon-extract", "aeneas-extract", "build-gate4", "build-engine", "axioms",
                "theorem-statement", "fresh-replay", "export", "nanoda", "fault-build", "fault-export"}
    steps = value["steps"]
    require(all(sum(s["name"] == name and s["exit"] == 0 for s in steps) == 1 for name in expected),
            "acceptance missing a successful required step")
    require(sum(s["name"] == "fault-nanoda" and s["exit"] != 0 for s in steps) == 1,
            "acceptance missing fault rejection")
    extraction = json.loads((args.out / "extraction.json").read_text())
    require(extraction["byte_identical"] is True, "acceptance missing extraction comparison")
    # Exclusive creation prevents overwriting an earlier receipt. Generic save cannot write this name.
    with (args.out / "accepted.json").open("x") as target:
        target.write(json.dumps(value, indent=2, sort_keys=True) + "\n")


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


class Recorder:
    def __init__(self, out):
        self.out = Path(out)
        self.steps = []

    def run(self, name, argv, cwd=None, env=None, expected: int | None = 0, stdout=None):
        log = self.out / (name + ".log")
        start = time.monotonic()
        with log.open("wb") as err:
            if stdout is None:
                p = subprocess.run(argv, cwd=cwd, env=env, stdout=err, stderr=subprocess.STDOUT)
            else:
                with Path(stdout).open("wb") as target:
                    p = subprocess.run(argv, cwd=cwd, env=env, stdout=target, stderr=err)
        row = {"name": name, "argv": [str(x) for x in argv], "cwd": str(cwd or Path.cwd()),
               "exit": p.returncode, "wall_seconds": time.monotonic() - start,
               "log_sha256": sha(log), "stdout_file": str(stdout) if stdout else None,
               "rss_note": "worker cgroup capped; per-step RSS not measured"}
        save(self.out / (name + ".json"), row)
        self.steps.append(row)
        print(f"{name}: exit {p.returncode}, {row['wall_seconds']:.2f}s", flush=True)
        if expected is not None:
            require(p.returncode == expected, f"{name} failed: see {log}")
        return p.returncode


def source_manifest(project):
    paths = sorted([project / "TransformerInt.lean", *(project / "TransformerInt").rglob("*.lean")])
    return {p.relative_to(project).as_posix(): sha(p) for p in paths}


def pinned_manifest(root):
    result = {}
    for line in (root / "evidence/gate4/generated.sha256").read_text().splitlines():
        m = re.fullmatch(r"([0-9a-f]{64})  (TransformerInt(?:\.lean|/[A-Za-z0-9_./]+\.lean))", line)
        if m is None:
            raise RuntimeError("malformed frozen gate4 manifest")
        digest, name = m.groups()
        require(".." not in Path(name).parts and name not in result, "unsafe/duplicate manifest path")
        result[name] = digest
    require(bool(result), "empty frozen gate4 manifest")
    return result


def generate(root, checkpoint, out, rec, label):
    rec.run(label, [sys.executable, "-B", str(root / "scripts/gen_transformer_lean.py"),
                   str(checkpoint), str(out), "--rows", "all"], cwd=root)
    actual = source_manifest(out)
    expected = pinned_manifest(root)
    require(actual == expected, f"{label}: generated source inventory/hash differs from evidence/gate4/generated.sha256")
    return actual


def closure(root, module):
    seen = set()
    todo = [module]
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        p = root / (m.replace(".", "/") + ".lean")
        require(p.is_file(), f"missing local source {m}")
        seen.add(m)
        for line in p.read_text().splitlines():
            match = re.fullmatch(r"\s*(?:public\s+)?import\s+(TransformerInt[\w.]*)\s*", line)
            if match:
                todo.append(match[1])
    return sorted(seen)


def axiom_audit(text, theorem=THEOREM):
    # Consume a full record, including wrapped axiom lists. Never discard warnings or garbage.
    pattern = (r"\s*'" + re.escape(theorem) +
               r"'\s+(?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))\s*")
    m = re.fullmatch(pattern, text)
    if m is None:
        raise RuntimeError("axiom report missing, truncated, duplicated or contains diagnostics")
    axioms = [] if m[2] else [x.strip() for x in m[1].split(",")]
    require(len(set(axioms)) == len(axioms) and set(axioms) <= set(STANDARD), "unpermitted/duplicate axiom")
    return axioms


def nanoda_config(export, path):
    save(path, {"export_file_path": str(export), "use_stdin": False,
                "permitted_axioms": STANDARD, "unpermitted_axiom_hard_error": True,
                "nat_extension": True, "string_extension": True, "pp_declars": [],
                "pp_to_stdout": False, "print_success_message": True})


def nanoda_verdict(text):
    matches = re.findall(r"Checked ([0-9,]+) declarations with no typechecker errors", text)
    require(len(matches) == 1 and int(matches[0].replace(",", "")) > 0,
            "nanoda has no unique positive typechecker verdict")
    return {"checked_declarations": int(matches[0].replace(",", "")),
            "pretty_printer_errors": "pretty printer error" in text,
            "claim": "no typechecker errors on the exact exported bytes"}


def objects(roots):
    records = {}
    for root in roots:
        root = Path(root).resolve()
        # Lake lists optional, unbuilt dependencies in LEAN_PATH. A nonexistent
        # directory contributes no objects, just as it does for Lean's resolver.
        # Existing non-directories and an entirely empty inventory remain fatal.
        if not root.exists():
            continue
        require(root.is_dir(), f"object root is not a directory {root}")
        for p in sorted(root.rglob("*.olean*")):
            if p.is_file():
                records[str(p)] = sha(p)
    require(bool(records), "empty object inventory")
    return records


def estimate(root):
    build = (root / "evidence/gate4/timings.txt").read_text()
    replay = (root / "evidence/gate4/replay-summary.txt").read_text()
    bm = re.search(r"build_wall_seconds (\d+)", build)
    rm = re.search(r"(\d+) wall seconds", replay)
    if bm is None or rm is None:
        raise RuntimeError("missing recorded gate4 costs")
    b = int(bm[1])
    r = int(rm[1])
    # Only use current package's successful measured build/replay receipts, if available.
    measured = []
    for p in sorted((root / "pilot/engine").glob("trained3-*.json")):
        try:
            row = json.loads(p.read_text())
            if row.get("exit") == 0 and isinstance(row.get("wall_seconds"), (float, int)):
                measured.append({"path": p.relative_to(root).as_posix(), "sha256": sha(p),
                                 "wall_seconds": row["wall_seconds"], "peak_rss_kib": row.get("peak_rss_kib")})
        except (ValueError, OSError):
            pass
    own = sum(x["wall_seconds"] for x in measured)
    return {"status": "estimate, not a measured end-to-end run", "cpu_cores": 4,
            "lake_threads": 2, "machine_ram_gib": 16, "worker_memory_cap_gib": 12,
            "free_disk_gib_minimum": 40, "worker_wall_limit_seconds": 21600,
            "recorded_gate4_build_seconds": b, "recorded_gate4_replay_seconds": r,
            "gate4_time_sources": ["evidence/gate4/timings.txt", "evidence/gate4/replay-summary.txt"],
            "package3_successful_receipts": measured, "package3_recorded_seconds_sum": own,
            "extraction_bootstrap_allowance_seconds": 1800,
            "planning_seconds": 2 * (b + r + own) + 3600 + 1800,
            "pricing_note": "Illustrative assumption only, not a vendor quote. Obtain authorization and a live price before any rental.",
            "assumed_hourly_rate_usd": 1.0,
            "estimated_cost_usd_at_assumed_rate": (2 * (b + r + own) + 3600 + 1800) / 3600,
            "worker_deadline_cost_usd_at_assumed_rate": 21600 / 3600,
            "method": "Twice recorded gate4 build+replay plus current package pilot costs, plus 3600s bootstrap allowance and an additional unmeasured 1800s Rust/Charon bootstrap and extraction allowance. Fresh final replay and nanoda/export are unmeasured; the 6h hard deadline is not a completion guarantee.",
            "memory_method": "12 GiB worker budget for two Lean jobs plus imports/checker, on a 16 GiB machine. Full closure peak RSS unmeasured; fail rather than expand the cap."}


def dry_run(args):
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    rec = Recorder(out)
    status = {"mode": "dry-run", "proof_checks_run": False, "network_used": False,
              "accepted": False, "runner_sha256": sha(__file__)}
    try:
        checkpoint = args.checkpoint.resolve()
        rec.run("shell-syntax", ["bash", "-n", str(ROOT / "scripts/box_trained.sh")])
        first = generate(ROOT, checkpoint, out / "generate-a", rec, "generate-a")
        second = generate(ROOT, checkpoint, out / "generate-b", rec, "generate-b")
        require(first == second, "generator is nondeterministic")
        save(out / "generated.json", first)
        modules = closure(out / "generate-a", "TransformerInt.Gen.AllRows")
        save(out / "gate4-closure.json", modules)
        status.update({"checkpoint_sha256": sha(checkpoint), "matched_source_files": len(first),
                       "gate4_closure_modules": len(modules), "generator_deterministic": True})
        gen = ROOT / "scripts/gen_engine_trained.py"
        if gen.is_file():
            rec.run("engine-generator-check", [sys.executable, "-B", str(gen), str(checkpoint), "--gate-weights", str(out / "generate-a/TransformerInt/Gen"), "--check"], cwd=ROOT)
            status["engine_generator_check"] = "passed"
        else:
            status["engine_generator_check"] = "blocked: parent generator not present yet"
        save(out / "estimate.json", estimate(ROOT))
        status["light_checks"] = "passed"
        # Retain authenticated inventories/logs, not two duplicate generated source trees.
        shutil.rmtree(out / "generate-a")
        shutil.rmtree(out / "generate-b")
    except Exception as e:
        status["error"] = str(e)
        raise
    finally:
        save(out / "dry-run.json", status)
    print(json.dumps(status, indent=2))


def setup_project(repo, gate, project):
    # An isolated project, not a source change in the pinned checkout. One TransformerInt
    # root contains BOTH generated objects and model, never several partial search roots.
    shutil.copytree(repo / "lean", project, symlinks=True,
                    ignore=shutil.ignore_patterns(".lake", "TransformerInt"))
    shutil.copytree(gate / "TransformerInt", project / "TransformerInt")
    shutil.copy2(gate / "TransformerInt.lean", project / "TransformerInt.lean")
    lakefile = project / "lakefile.lean"
    text = lakefile.read_text()
    old = 'require aeneas from "../toolchain/aeneas/backends/lean"'
    require(text.count(old) == 1, "unexpected Aeneas require declaration")
    text = text.replace(old, 'require aeneas from ' + json.dumps(str(repo / "toolchain/aeneas/backends/lean")))
    old = 'roots := #[`TransformerInt.Model]'
    if old in text:
        require(text.count(old) == 1, "unexpected TransformerInt library roots")
        text = text.replace(old, 'roots := #[`TransformerInt]\n  globs := #[.andSubmodules `TransformerInt]')
    else:
        require(text.count('globs := #[.andSubmodules `TransformerInt]') == 1,
                "unexpected TransformerInt library globs")
    lakefile.write_text(text)
    # The recorded dependency graph stays pinned, only its path entry moves with this project.
    mf = project / "lake-manifest.json"
    manifest = json.loads(mf.read_text())
    for pkg in manifest["packages"]:
        if pkg["name"] == "aeneas":
            pkg["dir"] = str(repo / "toolchain/aeneas/backends/lean")
    save(mf, manifest)


def extract_engine(repo, out, rec, env):
    """Dedicated worker only: pinned tools, fresh LLBC and byte-exact Lean comparison.

    Output stays outside the checkout. No optional/excluded Charon arguments are accepted.
    This checks reproducibility, not translator correctness or a compiled Rust binary.
    """
    charon_pin = "a58d159210b3a36fedeaba4437bda896a8b12f0d"
    aeneas_tag = "nightly-2026.11.04-d1e177b"
    aeneas_sha = "955928facac9853047edee5c68dd35bb40840955e1a5ddda66668dcb3198d72e"
    require((repo / "toolchain/aeneas/charon-pin").read_text().splitlines()[-1] == charon_pin,
            "Charon source pin mismatch")
    work = out / "extraction"
    replace_directory(work)
    tools = work / "tools"
    tools.mkdir()
    archive = work / "aeneas.tar.gz"
    rec.run("aeneas-download", ["curl", "--fail", "--location", "--retry", "3", "--output", str(archive),
            f"https://github.com/AeneasVerif/aeneas/releases/download/{aeneas_tag}/aeneas-linux-x86_64.tar.gz"], env=env)
    require(sha(archive) == aeneas_sha, "Aeneas archive checksum mismatch")
    rec.run("aeneas-unpack", ["tar", "-xzf", str(archive), "-C", str(tools), "aeneas"], env=env)
    aeneas = tools / "aeneas"
    rec.run("aeneas-version", [str(aeneas), "-version"], env=env)
    require((out / "aeneas-version.log").read_text().strip() == f"aeneas {aeneas_tag}",
            "Aeneas version mismatch")
    charon_repo = work / "charon"
    rec.run("charon-clone", ["git", "clone", "https://github.com/AeneasVerif/charon", str(charon_repo)], env=env)
    rec.run("charon-checkout", ["git", "checkout", "--detach", charon_pin], cwd=charon_repo, env=env)
    require(subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=charon_repo, text=True).strip() == charon_pin,
            "Charon checkout mismatch")
    rec.run("charon-submodules", ["git", "submodule", "update", "--init", "--recursive"], cwd=charon_repo, env=env)
    rec.run("rust-nightly-install", ["rustup", "toolchain", "install", "nightly-2026-09-17", "--profile", "minimal",
            "--component", "rustc-dev,llvm-tools,rust-src,miri"], env=env)
    rec.run("rust-engine-install", ["rustup", "toolchain", "install", "1.99.1", "--profile", "minimal"], env=env)
    rec.run("charon-build", ["nice", "-n", "10", "cargo", "build", "--locked", "--bins"],
            cwd=charon_repo / "charon", env=env)
    charon = charon_repo / "charon/target/debug/charon"
    rec.run("charon-version", [str(charon), "version"], env=env)
    require(f"({charon_pin})" in (out / "charon-version.log").read_text(), "Charon version mismatch")
    return compare_extraction(repo, work, rec, env, charon, aeneas)


def compare_extraction(repo, work, rec, env, charon, aeneas):
    # Deliberately ignore ambient extraction options, compiler wrappers and target overrides.
    clean = {k: v for k, v in env.items() if not k.startswith(("CHARON", "AENEAS", "CARGO_", "RUST"))
             and k not in {"EXTRA_CHARON_ARGS"}}
    clean.update({k: env[k] for k in ("RUSTUP_HOME", "CARGO_HOME") if k in env})
    clean["CARGO_BUILD_JOBS"] = "4"
    clean["CARGO_TARGET_DIR"] = str(work / "engine-target")
    llbc = work / "engine.llbc"
    dest = work / "lean"
    dest.mkdir(exist_ok=False)
    committed = repo / "lean/LcnExec/Translated/Engine.lean"
    original = committed.read_bytes()
    source_hashes = {p.relative_to(repo).as_posix(): sha(p) for p in sorted((repo / "rust/engine").rglob("*"))
                     if p.is_file() and "target" not in p.parts}
    rec.run("charon-extract", [str(charon), "cargo", "--preset=aeneas", "--dest-file", str(llbc),
            "--abort-on-error", "--error-on-warnings", "--", "--lib"], cwd=repo / "rust/engine", env=clean)
    require(llbc.is_file() and llbc.stat().st_size > 0, "Charon produced no LLBC")
    rec.run("aeneas-extract", [str(aeneas), "-backend", "lean", "-abort-on-error", "-warnings-as-errors",
            "-dest", str(dest), str(llbc)], cwd=repo, env=clean)
    generated = dest / "Engine.lean"
    require(generated.is_file(), "Aeneas produced no Engine.lean")
    receipt = {"byte_identical": generated.read_bytes() == original,
               "committed_translation_sha256": sha(committed), "fresh_translation_sha256": sha(generated),
               "llbc_sha256": sha(llbc), "rust_sources": source_hashes,
               "charon_binary_sha256": sha(charon), "aeneas_binary_sha256": sha(aeneas),
               "usize_target": "x86_64 Linux, pinned Lean platform: 64 bits"}
    save(rec.out / "extraction.json", receipt)
    require(committed.read_bytes() == original, "committed translation changed during extraction")
    require(all(sha(repo / name) == digest for name, digest in source_hashes.items()),
            "Rust sources changed during extraction")
    require(receipt["byte_identical"], "fresh extraction differs byte-for-byte from committed Engine.lean")
    return receipt


def replace_directory(path):
    """Replace only a caller-selected private bootstrap directory, never follow aliases."""
    path = Path(path)
    if path.is_symlink() or path.is_file():
        path.unlink()
    elif path.exists():
        shutil.rmtree(path)
    path.mkdir(parents=True)


def bootstrap_environment(out, ambient):
    # No machine-global tool homes or caches survive a new run. In particular elan-init
    # cannot collide with proxies from an earlier failed bootstrap. Fresh replacement
    # is intentional: proof objects are never reused across run-mode attempts.
    env = {k: v for k, v in ambient.items()
           if not k.startswith(("CHARON", "AENEAS", "CARGO_", "RUST", "ELAN_", "LAKE_", "XDG_"))
           and k not in {"EXTRA_CHARON_ARGS", "LEAN_PATH"}}
    homes = {"HOME": "home", "TMPDIR": "tmp", "ELAN_HOME": "elan",
             "CARGO_HOME": "cargo", "RUSTUP_HOME": "rustup", "XDG_CACHE_HOME": "cache"}
    for key, name in homes.items():
        target = out / name
        replace_directory(target)
        env[key] = str(target)
    env.update(LEAN_NUM_THREADS="2", CI="1", PYTHONDONTWRITEBYTECODE="1", CARGO_BUILD_JOBS="4")
    env["PATH"] = str(out / "elan/bin") + ":/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
    return env


def bootstrap_elan(out, rec, env):
    archive = out / "elan.tar.gz"
    rec.run("elan-download", ["curl", "--fail", "--location", "--retry", "3", "--output", str(archive),
            "https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz"])
    require(sha(archive) == ELAN_SHA, "elan archive checksum mismatch")
    # tar overwrites a prior elan-init. Resetting the private home also repairs a
    # partially installed set of hardlinked proxies rather than trusting its state.
    replace_directory(Path(env["ELAN_HOME"]))
    rec.run("elan-unpack", ["tar", "-xzf", str(archive), "-C", str(out), "elan-init"])
    rec.run("elan-install", [str(out / "elan-init"), "-y", "--no-modify-path", "--default-toolchain", "none"], env=env)
    rec.run("toolchain-install", ["elan", "toolchain", "install", TOOLCHAIN], env=env)


def worker(args):
    require(args.mode == "_worker" and os.environ.get("BOX_TRAINED_WORKER") == "1",
            "worker only runs through run, never plan or dry-run")
    out = args.out.resolve()
    rec = Recorder(out)
    repo, project, gate = out / "repo", out / "project", out / "gate4"
    env = bootstrap_environment(out, os.environ)
    try:
        rec.run("clone", ["git", "clone", "--no-checkout", "--filter=blob:none", args.repo, str(repo)])
        rec.run("checkout", ["git", "checkout", "--detach", args.commit], cwd=repo)
        actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
        require(actual == args.commit, "checkout commit mismatch")
        require(sha(repo / "scripts/box_trained.py") == sha(__file__), "runner differs from selected commit")
        rec.run("submodule", ["git", "submodule", "update", "--init", "toolchain/aeneas"], cwd=repo)
        require(subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo / "toolchain/aeneas", text=True).strip() == AENEAS,
                "Aeneas submodule pin mismatch")
        require((repo / "lean/lean-toolchain").read_text().strip() == TOOLCHAIN, "Lean toolchain pin mismatch")
        allow = [x.split()[0] for x in (repo / "gates/allowlist").read_text().splitlines()
                 if x.strip() and not x.lstrip().startswith("#")]
        require(allow == STANDARD, "standard axiom allowlist changed")
        bootstrap_elan(out, rec, env)
        prefixfile = out / "lean-prefix.txt"
        rec.run("lean-prefix", ["elan", "run", TOOLCHAIN, "lean", "--print-prefix"], cwd=repo / "lean", env=env, stdout=prefixfile)
        prefix = Path(prefixfile.read_text().strip())
        binary_hashes = {name: sha(prefix / "bin" / name) for name in ["lean", "lake", "leanchecker", *BINARY_PINS]}
        for name, expected in BINARY_PINS.items():
            require(binary_hashes[name] == expected, f"{name} gate0(b) binary pin mismatch")
        save(out / "toolchain-binaries.json", binary_hashes)
        rec.run("lean-version", [str(prefix / "bin/lean"), "--version"], env=env)
        require("4.35.0" in (out / "lean-version.log").read_text() and
                "eb6cafb7290e8bd5f2937522d8d804f58f02bafc" in (out / "lean-version.log").read_text(), "Lean version mismatch")
        extract_engine(repo, out, rec, env)
        # Freeze the supplied bytes once. Also expose the historical gate4 sibling default
        # so the parent's no-argument generator check works on a genuinely fresh box.
        checkpoint = out / "inputs/best.npz"
        checkpoint.parent.mkdir()
        shutil.copyfile(args.checkpoint.resolve(), checkpoint)
        default_checkpoint = out / "lean-checked-network/transformer/runs/best.npz"
        default_checkpoint.parent.mkdir(parents=True)
        default_checkpoint.symlink_to(checkpoint)
        generate(repo, checkpoint, gate, rec, "generate-gate4")
        require((repo / "scripts/gen_engine_trained.py").is_file(), "parent generator missing")
        rec.run("engine-generator-check", [sys.executable, "-B", str(repo / "scripts/gen_engine_trained.py"), str(checkpoint), "--gate-weights", str(gate / "TransformerInt/Gen"), "--check"], cwd=repo, env=env)
        setup_project(repo, gate, project)
        require((project / "LcnExec/Engine/TrainedFinal.lean").is_file(), "parent final theorem module missing")
        sources = {p.relative_to(project).as_posix(): sha(p) for p in sorted(project.rglob("*.lean"))}
        sources.update({name: sha(project / name) for name in ["lakefile.lean", "lake-manifest.json", "lean-toolchain"]})
        save(out / "staged-sources.json", sources)
        save(out / "generated.json", source_manifest(gate))
        save(out / "estimate.json", estimate(repo))
        save(out / "gate4-closure.json", closure(gate, "TransformerInt.Gen.AllRows"))
        # Resolve the committed manifests, never lake update. Only Mathlib cache is borrowed.
        rec.run("mathlib-cache", ["lake", "exe", "cache", "get"], cwd=project, env=env)
        rec.run("build-gate4", ["lake", "build", "--no-cache", "TransformerInt.Gen.AllRows"], cwd=project, env=env)
        rec.run("build-engine", ["lake", "build", "--no-cache", "LcnExec.Engine.Trained", MODULE], cwd=project, env=env)
        audit = project / "BoxTrainedAxioms.lean"
        audit.write_text(f"import {MODULE}\n#print axioms {THEOREM}\n")
        rec.run("axioms", ["lake", "env", "lean", str(audit)], cwd=project, env=env)
        save(out / "axiom-audit.json", {"theorem": THEOREM, "axioms": axiom_audit((out / "axioms.log").read_text())})
        statement = project / "BoxTrainedStatement.lean"
        statement.write_text(f"import {MODULE}\nset_option pp.all true in\n#check @{THEOREM}\n")
        rec.run("theorem-statement", ["lake", "env", "lean", str(statement)], cwd=project, env=env)
        pathfile = out / "lean-path.txt"
        rec.run("lean-path", ["lake", "env", "printenv", "LEAN_PATH"], cwd=project, env=env, stdout=pathfile)
        # Resolve relative Lake paths at the project, add the core toolchain explicitly.
        object_roots = [(project / x).resolve() for x in pathfile.read_text().strip().split(":") if x]
        object_roots.append(prefix / "lib/lean")
        save(out / "object-search-roots.json", {
            "roots": [str(p) for p in object_roots],
            "absent_empty_roots": [str(p) for p in object_roots if not p.exists()],
            "policy": "Nonexistent search directories contain no objects; existing non-directories and an empty total inventory are fatal."})
        before = objects(object_roots)
        save(out / "objects-before.json", before)
        rec.run("fresh-replay", ["lake", "env", "leanchecker", "--fresh", MODULE], cwd=project, env=env)
        export = out / "trained-engine.ndjson"
        rec.run("export", ["lake", "env", str(prefix / "bin/leanexport"), MODULE, "--", THEOREM], cwd=project, env=env, stdout=export)
        require(export.stat().st_size > 0, "empty theorem export")
        config = out / "nanoda-config.json"
        nanoda_config(export, config)
        rec.run("nanoda", [str(prefix / "bin/nanoda_bin"), str(config)], env=env)
        verdict = nanoda_verdict((out / "nanoda.log").read_text())
        # A Lean-accepted malicious axiom must fail nanoda for the exact intended reason.
        fault = project / "BoxTrainedFault.lean"
        fault.write_text("namespace BoxTrainedFault\naxiom bad : False\ntheorem uses_bad : False := bad\nend BoxTrainedFault\n")
        rec.run("fault-build", ["lake", "env", "lean", "-o", str(project / "BoxTrainedFault.olean"), str(fault)], cwd=project, env=env)
        fault_export = out / "fault.ndjson"
        faultenv = dict(env, LEAN_PATH=str(project) + ":" + pathfile.read_text().strip())
        # Call the exporter directly so Lake cannot rewrite the control module's search path.
        faultenv["PATH"] = str(prefix / "bin") + ":" + env["PATH"]
        rec.run("fault-export", [str(prefix / "bin/leanexport"), "BoxTrainedFault", "--", "BoxTrainedFault.uses_bad"], cwd=project, env=faultenv, stdout=fault_export)
        faultconfig = out / "fault-nanoda-config.json"
        nanoda_config(fault_export, faultconfig)
        code = rec.run("fault-nanoda", [str(prefix / "bin/nanoda_bin"), str(faultconfig)], env=env, expected=None)
        faultlog = (out / "fault-nanoda.log").read_text()
        require(code != 0 and re.search(r'unpermitted axiom\s+"BoxTrainedFault.bad"', faultlog),
                "fault did not fail for the intended unpermitted axiom")
        after = objects(object_roots)
        save(out / "objects-after.json", after)
        require(before == after, "proof objects changed during replay/export/independent check")
        require(all(sha(project / name) == digest for name, digest in sources.items()),
                "staged proof sources/configuration changed during checking")
        finalobject = project / ".lake/build/lib/lean" / (MODULE.replace(".", "/") + ".olean")
        require(str(finalobject.resolve()) in before, "final object missing from checked inventory")
        require(subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"], cwd=repo, text=True) == "", "pinned checkout changed")
        write_acceptance(args, {"accepted": True, "commit": actual, "module": MODULE, "theorem": THEOREM,
             "runner_sha256": sha(__file__), "checkpoint_sha256": sha(checkpoint),
             "export_sha256": sha(export), "export_bytes": export.stat().st_size,
             "final_olean_sha256": sha(finalobject), "objects_manifest_sha256": sha(out / "objects-before.json"),
             "staged_sources_sha256": sha(out / "staged-sources.json"),
             "generated_manifest_sha256": sha(out / "generated.json"),
             "toolchain_binaries_sha256": sha(out / "toolchain-binaries.json"), "nanoda": verdict,
             "extraction_receipt_sha256": sha(out / "extraction.json"),
             "fault": "Lean-accepted unpermitted axiom rejected by independent checker",
             "fault_source_sha256": sha(fault), "fault_export_sha256": sha(fault_export),
             "steps": rec.steps, "scope": "Lean theorem only, not the compiler/translator or executable behavior"})
    except Exception as e:
        save(out / "failed.json", {"accepted": False, "error": str(e), "steps": rec.steps})
        raise


def run(args):
    require(args.dedicated_debian, "run requires --dedicated-debian; NEVER run on the shared agent host")
    require(os.geteuid() == 0, "run as root on the already authorized dedicated box")
    require(platform.machine() == "x86_64", "pins are for x86_64 Linux only")
    require(Path("/etc/debian_version").is_file() and Path("/run/systemd/system").is_dir(), "requires Debian with running systemd")
    require(re.fullmatch(r"[0-9a-f]{40}", args.commit or ""), "--commit must be a full lowercase 40-character SHA")
    require(args.repo and args.checkpoint.is_file(), "requires accessible --repo and --checkpoint")
    require((os.cpu_count() or 0) >= 4, "need at least 4 CPU cores")
    mm = re.search(r"MemTotal:\s+(\d+)", Path("/proc/meminfo").read_text())
    if mm is None:
        raise RuntimeError("cannot read total host memory")
    memory = int(mm[1])
    require(memory >= 15 * 1024**2, "need nominal 16 GiB machine RAM")
    out = args.out.resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    require(shutil.disk_usage(out.parent).free >= 40 * 1024**3, "need 40 GiB free disk")
    out.mkdir(exist_ok=False)
    rec = Recorder(out)
    save(out / "host.json", {"hostname": platform.node(), "platform": platform.platform(),
         "cpus": os.cpu_count(), "mem_total_kib": memory, "free_disk_bytes": shutil.disk_usage(out).free,
         "requested_commit": args.commit, "runner_sha256": sha(__file__)})
    rec.run("apt-update", ["apt-get", "update"])
    aptenv = dict(os.environ, DEBIAN_FRONTEND="noninteractive")
    rec.run("apt-install", ["apt-get", "install", "-y", "git", "curl", "ca-certificates", "tar", "gzip", "zstd",
                           "build-essential", "pkg-config", "libgmp-dev", "python3", "util-linux", "coreutils", "rustup"], env=aptenv)
    rec.run("bounded-worker", ["systemd-run", "--scope", "--quiet", "-p", "MemoryMax=12G", "-p", "MemorySwapMax=0",
            "-p", "CPUQuota=400%", "timeout", "--signal=TERM", "--kill-after=60", "21600",
            sys.executable, "-B", str(Path(__file__).resolve()), "_worker", "--repo", args.repo,
            "--commit", args.commit, "--checkpoint", str(args.checkpoint.resolve()), "--out", str(out)],
            env=dict(os.environ, BOX_TRAINED_WORKER="1"))
    require((out / "accepted.json").is_file(), "worker exited without acceptance receipt")
    print(f"Accepted receipt: {out / 'accepted.json'}")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=["plan", "dry-run", "run", "_worker"])
    parser.add_argument("--out", type=Path)
    parser.add_argument("--checkpoint", type=Path)
    parser.add_argument("--repo")
    parser.add_argument("--commit")
    parser.add_argument("--dedicated-debian", action="store_true")
    args = parser.parse_args()
    if args.mode == "plan":
        print(json.dumps(estimate(ROOT), indent=2))
        return
    require(args.out is not None and args.checkpoint is not None, "--out and --checkpoint are required")
    if args.mode == "dry-run":
        dry_run(args)
    elif args.mode == "run":
        run(args)
    else:
        # Internal entry cannot be mistaken for permission to bypass the bounded wrapper.
        require(os.environ.get("BOX_TRAINED_WORKER") == "1", "internal worker; use run --dedicated-debian")
        worker(args)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError) as error:
        print(f"box_trained: {error}", file=sys.stderr)
        sys.exit(1)
