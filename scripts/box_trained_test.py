#!/usr/bin/env python3
"""Lightweight runner regressions. No Lean, network, installs or paid calls."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("box_trained", HERE / "box_trained.py")
assert spec is not None and spec.loader is not None
box = importlib.util.module_from_spec(spec)
spec.loader.exec_module(box)


class BoxTrainedTests(unittest.TestCase):
    def scratch(self):
        self.assertIn("TMPDIR", os.environ, "tests need the session scratch directory")
        temp = tempfile.TemporaryDirectory(prefix="box-trained-test-", dir=os.environ["TMPDIR"])
        self.addCleanup(temp.cleanup)
        return Path(temp.name)

    def test_bootstrap_homes_repeat_clean_replacement(self):
        root = self.scratch()
        ambient = dict(os.environ, ELAN_TOOLCHAIN="hostile", LAKE_HOME="outside", LEAN_PATH="outside",
                       XDG_CACHE_HOME="outside", RUSTUP_TOOLCHAIN="outside")
        first = box.bootstrap_environment(root, ambient)
        for key in ["HOME", "TMPDIR", "ELAN_HOME", "CARGO_HOME", "RUSTUP_HOME", "XDG_CACHE_HOME"]:
            (Path(first[key]) / "stale-partial-state").write_text("fixture")
        second = box.bootstrap_environment(root, ambient)
        self.assertEqual(first, second)
        for key in ["HOME", "TMPDIR", "ELAN_HOME", "CARGO_HOME", "RUSTUP_HOME", "XDG_CACHE_HOME"]:
            self.assertEqual(list(Path(second[key]).iterdir()), [])
        for key in ["ELAN_TOOLCHAIN", "LAKE_HOME", "LEAN_PATH", "RUSTUP_TOOLCHAIN"]:
            self.assertNotIn(key, second)

    def test_bootstrap_replaces_alias_without_following(self):
        root = self.scratch()
        outside = root / "outside"
        outside.mkdir()
        (outside / "preserve").write_text("fixture")
        alias = root / "private"
        alias.symlink_to(outside, target_is_directory=True)
        box.replace_directory(alias)
        self.assertFalse(alias.is_symlink())
        self.assertTrue((outside / "preserve").is_file())
        self.assertEqual(list(alias.iterdir()), [])

    def test_elan_and_toolchain_bootstrap_twice(self):
        root = self.scratch()
        env = box.bootstrap_environment(root, os.environ)
        calls = []
        class FixtureRecorder:
            def run(self, name, argv, **kwargs):
                calls.append((name, argv))
                if name == "elan-download":
                    (root / "elan.tar.gz").write_bytes(b"synthetic pinned archive")
                if name == "elan-install":
                    home = Path(env["ELAN_HOME"])
                    self_fixture.assertEqual(list(home.iterdir()), [])
                    (home / "bin").mkdir()
                    (home / "bin/lean").write_text("partial proxy fixture")
                if name == "toolchain-install":
                    self_fixture.assertEqual(argv, ["elan", "toolchain", "install", box.TOOLCHAIN])
                    (Path(env["ELAN_HOME"]) / "toolchains").mkdir()
        self_fixture = self
        import hashlib
        with patch.object(box, "ELAN_SHA", hashlib.sha256(b"synthetic pinned archive").hexdigest()):
            box.bootstrap_elan(root, FixtureRecorder(), env)
            box.bootstrap_elan(root, FixtureRecorder(), env)
        self.assertEqual([n for n, _ in calls].count("elan-install"), 2)
        self.assertEqual([n for n, _ in calls].count("toolchain-install"), 2)
        with patch.object(box, "ELAN_SHA", "0" * 64), self.assertRaisesRegex(RuntimeError, "checksum mismatch"):
            box.bootstrap_elan(root, FixtureRecorder(), env)

    def test_charon_aeneas_bootstrap_twice(self):
        root = self.scratch()
        repo, out = root / "repo", root / "out"
        (repo / "toolchain/aeneas").mkdir(parents=True)
        pin = "a58d159210b3a36fedeaba4437bda896a8b12f0d"
        (repo / "toolchain/aeneas/charon-pin").write_text(pin + "\n")
        out.mkdir()
        calls = []
        class FixtureRecorder:
            def run(self, name, argv, **kwargs):
                calls.append((name, argv))
                if name == "aeneas-download":
                    self_fixture.assertFalse((out / "extraction/stale").exists())
                if name == "aeneas-version":
                    (out / "aeneas-version.log").write_text("aeneas nightly-2026.11.04-d1e177b\n")
                if name == "charon-version":
                    (out / "charon-version.log").write_text("charon (" + pin + ")\n")
        self_fixture = self
        with patch.object(box, "sha", return_value="955928facac9853047edee5c68dd35bb40840955e1a5ddda66668dcb3198d72e"), \
             patch.object(box.subprocess, "check_output", return_value=pin + "\n"), \
             patch.object(box, "compare_extraction", return_value={"fixture": True}):
            for _ in range(2):
                (out / "extraction").mkdir(exist_ok=True)
                (out / "extraction/stale").write_text("partial Charon/Aeneas fixture")
                box.extract_engine(repo, out, FixtureRecorder(), {})
        for name in ["aeneas-download", "aeneas-unpack", "charon-clone", "charon-checkout",
                     "charon-submodules", "rust-nightly-install", "rust-engine-install", "charon-build"]:
            self.assertEqual([n for n, _ in calls].count(name), 2)

    def test_axioms_wrapped(self):
        text = f"'{box.THEOREM}' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
        self.assertEqual(box.axiom_audit(text), box.STANDARD)

    def test_axioms_none(self):
        self.assertEqual(box.axiom_audit(f"'{box.THEOREM}' does not depend on any axioms\n"), [])

    def test_axiom_bad_records(self):
        prefix = f"'{box.THEOREM}' depends on axioms: "
        for text in ["", prefix + "[bad]", prefix + "[propext, propext]", prefix + "[propext", prefix + "[]",
                     prefix + "[propext]\nwarning: bad", prefix + "[propext]\n" + prefix + "[propext]",
                     "'Other.theorem' depends on axioms: [propext]"]:
            with self.subTest(text=text), self.assertRaises(RuntimeError):
                box.axiom_audit(text)

    def test_nanoda_positive(self):
        actual = box.nanoda_verdict('Checked 4,901 declarations with no typechecker errors, 1 pretty printer errors: [\n"Unable to print axioms",\n]')
        self.assertEqual(actual["checked_declarations"], 4901)
        self.assertTrue(actual["pretty_printer_errors"])

    def test_nanoda_rejects_missing_duplicate_failure(self):
        positive = "Checked 10 declarations with no typechecker errors"
        for text in ["", "Checked 10 declarations with 1 typechecker errors", positive + "\n" + positive,
                     "Checked 0 declarations with no typechecker errors"]:
            with self.subTest(text=text), self.assertRaises(RuntimeError):
                box.nanoda_verdict(text)

    def test_nanoda_hard_error_config(self):
        root = self.scratch()
        box.nanoda_config(root / "export", root / "config")
        config = json.loads((root / "config").read_text())
        self.assertIs(config["unpermitted_axiom_hard_error"], True)
        self.assertEqual(config["permitted_axioms"], box.STANDARD)
        self.assertTrue(config["nat_extension"])

    def test_frozen_manifest(self):
        manifest = box.pinned_manifest(box.ROOT)
        self.assertEqual(len(manifest), 139)
        self.assertIn("TransformerInt/Gen/Row112.lean", manifest)
        self.assertIn("TransformerInt/Gen/AllRows.lean", manifest)

    def test_manifest_rejects_duplicate(self):
        root = self.scratch()
        (root / "evidence/gate4").mkdir(parents=True)
        line = "a" * 64 + "  TransformerInt.lean\n"
        (root / "evidence/gate4/generated.sha256").write_text(line * 2)
        with self.assertRaises(RuntimeError):
            box.pinned_manifest(root)

    def test_closure_requires_sources(self):
        with self.assertRaisesRegex(RuntimeError, "missing local source"):
            box.closure(self.scratch(), "TransformerInt.Gen.AllRows")

    def test_object_hash_change(self):
        root = self.scratch()
        (root / "A.olean").write_bytes(b"before")
        (root / "A.olean.private").write_bytes(b"private")
        before = box.objects([root])
        (root / "A.olean").write_bytes(b"after")
        self.assertNotEqual(before, box.objects([root]))
        self.assertEqual(len(before), 2)

    def test_object_inventory_absent_optional_root(self):
        root = self.scratch()
        (root / "Required.olean").write_bytes(b"required")
        absent = root / "Cli/.lake/build/lib/lean"
        self.assertEqual(box.objects([root]), box.objects([absent, root]))
        # A newly appearing object is not silently excluded from the after-scan.
        before = box.objects([root, absent])
        absent.mkdir(parents=True)
        (absent / "New.olean").write_bytes(b"new")
        self.assertNotEqual(before, box.objects([root, absent]))

    def test_object_inventory_empty_and_non_directory_rejected(self):
        root = self.scratch()
        with self.assertRaisesRegex(RuntimeError, "empty object inventory"):
            box.objects([root / "absent"])
        bad = root / "not-directory"
        bad.write_bytes(b"not a directory")
        with self.assertRaisesRegex(RuntimeError, "not a directory"):
            box.objects([bad])

    def test_recorder_preserves_failure_exit_and_log(self):
        root = self.scratch()
        rec = box.Recorder(root)
        with self.assertRaisesRegex(RuntimeError, "failure failed"):
            rec.run("failure", [sys.executable, "-c", 'print("real process failed"); raise SystemExit(7)'])
        receipt = json.loads((root / "failure.json").read_text())
        self.assertEqual(receipt["exit"], 7)
        self.assertEqual(receipt["log_sha256"], box.sha(root / "failure.log"))
        self.assertFalse((root / "accepted.json").exists())

    def test_project_staging(self):
        root = self.scratch()
        repo, gate, project = root / "repo", root / "gate", root / "project"
        (repo / "lean/LcnExec/Engine").mkdir(parents=True)
        (repo / "lean/LcnExec/Engine/TrainedFinal.lean").write_text("-- test fixture only\n")
        for name in ["lakefile.lean", "lake-manifest.json", "lean-toolchain"]:
            (repo / "lean" / name).write_bytes((box.ROOT / "lean" / name).read_bytes())
        (repo / "lean/TransformerInt").symlink_to("../old-model")
        (gate / "TransformerInt/Gen").mkdir(parents=True)
        (gate / "TransformerInt.lean").write_text("import TransformerInt.Model\n")
        (gate / "TransformerInt/Model.lean").write_text("-- model fixture\n")
        (gate / "TransformerInt/Gen/AllRows.lean").write_text("-- all rows fixture\n")
        box.setup_project(repo, gate, project)
        self.assertFalse((project / "TransformerInt").is_symlink())
        self.assertTrue((project / "TransformerInt/Gen/AllRows.lean").exists())
        self.assertTrue((repo / "lean/TransformerInt").is_symlink())
        self.assertIn('globs := #[.andSubmodules `TransformerInt]', (project / "lakefile.lean").read_text())
        manifest = json.loads((project / "lake-manifest.json").read_text())
        aeneas = next(p for p in manifest["packages"] if p["name"] == "aeneas")
        self.assertEqual(aeneas["dir"], str(repo / "toolchain/aeneas/backends/lean"))
        self.assertEqual(next(p for p in manifest["packages"] if p["name"] == "mathlib")["rev"],
                         "56a005855ea17e0b0958f73ec801ae140b0a1679")

    def test_run_guard_no_side_effect(self):
        root = self.scratch()
        args = argparse.Namespace(dedicated_debian=False, out=root / "must-not-exist")
        with self.assertRaisesRegex(RuntimeError, "dedicated-debian"):
            box.run(args)
        self.assertFalse(args.out.exists())

    def extraction_fixture(self, kind="same"):
        root = self.scratch()
        repo, work, out = root / "repo", root / "work", root / "out"
        (repo / "rust/engine/src").mkdir(parents=True)
        (repo / "rust/engine/src/lib.rs").write_text("// synthetic extraction fixture only\n")
        (repo / "lean/LcnExec/Translated").mkdir(parents=True)
        (repo / "lean/LcnExec/Translated/Engine.lean").write_bytes(b"fixture translation\n")
        work.mkdir()
        out.mkdir()
        charon, aeneas = root / "charon", root / "aeneas"
        charon.write_text("#!" + sys.executable + "\n" +
            "import os, pathlib, sys\n" +
            "assert '--exclude' not in ' '.join(sys.argv)\n" +
            "assert 'CHARON_ARGS' not in os.environ and 'RUSTFLAGS' not in os.environ\n" +
            "assert os.environ['CARGO_BUILD_JOBS'] == '4'\n" +
            ("raise SystemExit(7)\n" if kind == "charon-fail" else
             "pathlib.Path(sys.argv[sys.argv.index('--dest-file')+1]).write_bytes(b'fixture llbc')\n"))
        output = b"fixture translation\n" if kind == "same" else b"fixture translation\r\n"
        aeneas.write_text("#!" + sys.executable + "\n" +
            "import pathlib, sys\n" +
            ("raise SystemExit(8)\n" if kind == "aeneas-fail" else
             "pass\n" if kind == "missing" else
             f"(pathlib.Path(sys.argv[sys.argv.index('-dest')+1])/'Engine.lean').write_bytes({output!r})\n"))
        charon.chmod(0o755)
        aeneas.chmod(0o755)
        return repo, work, out, charon, aeneas

    def test_extraction_byte_identical(self):
        repo, work, out, charon, aeneas = self.extraction_fixture()
        env = dict(os.environ, CHARON_ARGS="--exclude engine::predict", RUSTFLAGS="--cfg bad")
        receipt = box.compare_extraction(repo, work, box.Recorder(out), env, charon, aeneas)
        self.assertTrue(receipt["byte_identical"])
        self.assertEqual(receipt["committed_translation_sha256"], receipt["fresh_translation_sha256"])
        command = json.loads((out / "charon-extract.json").read_text())["argv"]
        self.assertEqual(command[1:3], ["cargo", "--preset=aeneas"])
        self.assertEqual(command[-4:], ["--abort-on-error", "--error-on-warnings", "--", "--lib"])
        self.assertFalse((out / "accepted.json").exists())

    def test_extraction_rejects_byte_drift(self):
        repo, work, out, charon, aeneas = self.extraction_fixture("changed")
        with self.assertRaisesRegex(RuntimeError, "differs byte-for-byte"):
            box.compare_extraction(repo, work, box.Recorder(out), dict(os.environ), charon, aeneas)
        self.assertFalse(json.loads((out / "extraction.json").read_text())["byte_identical"])
        self.assertEqual((repo / "lean/LcnExec/Translated/Engine.lean").read_bytes(), b"fixture translation\n")
        self.assertFalse((out / "accepted.json").exists())

    def test_extraction_rejects_failures_and_missing_output(self):
        for kind in ["charon-fail", "aeneas-fail", "missing"]:
            with self.subTest(kind=kind):
                repo, work, out, charon, aeneas = self.extraction_fixture(kind)
                with self.assertRaises(RuntimeError):
                    box.compare_extraction(repo, work, box.Recorder(out), dict(os.environ), charon, aeneas)
                self.assertFalse((out / "accepted.json").exists())

    def test_acceptance_denied_outside_worker(self):
        root = self.scratch()
        with patch.dict(os.environ, {"BOX_TRAINED_WORKER": "1"}):
            for mode in ["plan", "dry-run", "run"]:
                with self.subTest(mode=mode), self.assertRaisesRegex(RuntimeError, "never plan or dry-run"):
                    box.write_acceptance(argparse.Namespace(mode=mode, out=root), {"accepted": True})
        with self.assertRaisesRegex(RuntimeError, "dedicated worker final gate"):
            box.save(root / "accepted.json", {"accepted": True})
        self.assertFalse((root / "accepted.json").exists())

    def test_acceptance_requires_completed_gates(self):
        root = self.scratch()
        with patch.dict(os.environ, {"BOX_TRAINED_WORKER": "1"}):
            with self.assertRaisesRegex(RuntimeError, "missing a successful required step"):
                box.write_acceptance(argparse.Namespace(mode="_worker", out=root), {"accepted": True, "steps": []})
        self.assertFalse((root / "accepted.json").exists())

    def test_worker_rejects_plan_and_dry_run_before_side_effects(self):
        root = self.scratch()
        with patch.dict(os.environ, {"BOX_TRAINED_WORKER": "1"}):
            for mode in ["plan", "dry-run"]:
                with self.subTest(mode=mode), self.assertRaisesRegex(RuntimeError, "never plan or dry-run"):
                    box.worker(argparse.Namespace(mode=mode, out=root / "out"))
        self.assertFalse((root / "out").exists())

    def test_acceptance_requires_worker_marker(self):
        root = self.scratch()
        with patch.dict(os.environ):
            os.environ.pop("BOX_TRAINED_WORKER", None)
            with self.assertRaisesRegex(RuntimeError, "dedicated worker"):
                box.write_acceptance(argparse.Namespace(mode="_worker", out=root), {"accepted": True})
        self.assertFalse((root / "accepted.json").exists())

    def test_plan_cannot_produce_acceptance(self):
        root = self.scratch()
        result = subprocess.run(["bash", str(HERE / "box_trained.sh"), "plan", "--out", str(root / "out")],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("estimate", json.loads(result.stdout)["status"])
        self.assertFalse((root / "out").exists())

    def test_dry_run_cannot_produce_acceptance(self):
        root = self.scratch()
        args = argparse.Namespace(mode="dry-run", out=root / "out", checkpoint=root / "checkpoint")
        args.checkpoint.write_bytes(b"synthetic dry-run fixture")
        def generate_fixture(repo, checkpoint, target, recorder, label):
            (target / "TransformerInt/Gen").mkdir(parents=True)
            (target / "TransformerInt/Gen/AllRows.lean").write_text("-- synthetic fixture\n")
            return {"fixture": "synthetic"}
        # Exercise the real dry-run path without pretending to run a generator or proof.
        with patch.object(box, "generate", side_effect=generate_fixture), patch.object(box.Recorder, "run", return_value=0), \
             patch.object(box, "extract_engine", side_effect=AssertionError("dry-run must not extract")), \
             patch.dict(os.environ, {"BOX_TRAINED_WORKER": "1"}):
            box.dry_run(args)
        status = json.loads((args.out / "dry-run.json").read_text())
        self.assertIs(status["accepted"], False)
        self.assertIs(status["proof_checks_run"], False)
        self.assertFalse((args.out / "accepted.json").exists())

    def test_internal_worker_guard(self):
        root = self.scratch()
        env = dict(os.environ)
        env.pop("BOX_TRAINED_WORKER", None)
        result = subprocess.run([sys.executable, "-B", str(HERE / "box_trained.py"), "_worker", "--out", str(root / "out"),
                                 "--checkpoint", str(root / "checkpoint")], env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("internal worker", result.stderr)
        self.assertFalse((root / "out").exists())


if __name__ == "__main__":
    unittest.main(verbosity=2)
