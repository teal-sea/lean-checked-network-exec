#!/usr/bin/env python3
"""Light generation tests. Kernel acceptance is recorded separately."""
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
sys.dont_write_bytecode = True
import gen_engine_trained as g

class GenerationTests(unittest.TestCase):
    def test_real_regeneration(self):
        cp = Path(os.environ['TRAINED_CHECKPOINT'])
        self.assertEqual(g.gen.sha256_file(cp), g.gen.CHECKPOINT_SHA256)
        t = g.gen.load_quantised(cp)
        first, second = g.render(t), g.render(t)
        self.assertEqual(first, second)
        self.assertEqual(len(first), 10)
        for path, text in first.items():
            self.assertEqual((g.ROOT/path).read_text(), text)
            self.assertNotIn('sorry',text)
            self.assertNotIn('native_decide',text)
        # All fields occur in the representation and LoadBounds witness.
        weights = first['lean/LcnExec/Engine/Trained/Weights.lean']
        for field, *_ in g.FIELDS + g.VECTORS:
            self.assertIn(f'{field} := {field}', weights)
            self.assertIn(f'{field} := {field}_bound', weights)
        print('real generation sha256', hashlib.sha256(''.join(first.values()).encode()).hexdigest())

    def test_modified_checkpoint_is_rejected(self):
        cp=Path(os.environ['TRAINED_CHECKPOINT'])
        with tempfile.TemporaryDirectory() as d:
            changed=Path(d)/'changed.npz'
            data=bytearray(cp.read_bytes()); data[len(data)//2]^=1; changed.write_bytes(data)
            p=subprocess.run([sys.executable,'-B',str(g.ROOT/'scripts/gen_engine_trained.py'),str(changed),'--check'],capture_output=True,text=True)
            self.assertNotEqual(p.returncode,0)
            self.assertIn('checkpoint hash mismatch',p.stderr)

if __name__=='__main__': unittest.main(verbosity=2)
