import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(__file__))
sys.path.append(os.path.join(ROOT, "src"))

from nk0_parser import parse_module
from nk0_runtime import run_function
from nk0_replay import replay_and_verify


class TestNK0NegativeCases(unittest.TestCase):
    def test_unsafe_expression_rejected(self):
        source = """
module Unsafe {
  budget 1.0;
  invariant true;
  fn bad(x: Real) -> Real {
    return (x).__class__;
  }
}
"""
        mod = parse_module(source)
        with self.assertRaises(ValueError):
            run_function(mod, "bad", {}, {"x": 1.0})

    def test_replay_input_hash_mismatch(self):
        source = """
module Simple {
  budget 1.0;
  invariant x >= 0;
  fn add(x: Real, y: Real) -> Real {
    let z = x + y;
    return z;
  }
}
"""
        mod = parse_module(source)
        _, _, r = run_function(mod, "add", {}, {"x": 1.0, "y": 1.0})

        def bad_step(store, step_id):
            return {"x": 9.0, "y": 9.0, "z": 18.0}

        ok, msg = replay_and_verify({}, [r], bad_step)
        self.assertFalse(ok)
        self.assertTrue(
          "input_hash mismatch" in msg or "output_hash mismatch" in msg,
          msg,
        )


if __name__ == "__main__":
    unittest.main()
