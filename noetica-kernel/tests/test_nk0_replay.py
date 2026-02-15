import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(__file__))
sys.path.append(os.path.join(ROOT, "src"))

from noetica_parser import parse_module
from nsc_kernel.nsc_runtime import run_sequence
from nsc_kernel.nsc_replay import replay_and_verify


class TestNK0Replay(unittest.TestCase):
    def test_replay_valid(self):
        with open(os.path.join(ROOT, "examples", "hello_nk0.nk"), "r", encoding="utf-8") as f:
            source = f.read()
        mod = parse_module(source)
        calls = [{"x": 1.0, "y": 1.0}, {"x": 2.0, "y": 3.0}]
        receipts = run_sequence(mod, "add", calls, initial_store={})

        def step_fn(store, step_id):
            if step_id == 0:
                return {"x": 1.0, "y": 1.0, "z": 2.0}
            return {"x": 2.0, "y": 3.0, "z": 5.0}

        ok, msg = replay_and_verify({}, receipts, step_fn)
        self.assertTrue(ok, msg)


if __name__ == "__main__":
    unittest.main()
