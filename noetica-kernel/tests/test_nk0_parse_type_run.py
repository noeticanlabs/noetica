import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(__file__))
sys.path.append(os.path.join(ROOT, "src"))

from noetica_parser import parse_module
from noetica_typecheck import typecheck_module
from nsc_kernel.nsc_runtime import run_function


class TestNK0ParseTypeRun(unittest.TestCase):
    def test_parse_type_run(self):
        with open(os.path.join(ROOT, "examples", "hello_nk0.nk"), "r", encoding="utf-8") as f:
            source = f.read()
        mod = parse_module(source)
        typecheck_module(mod)
        result, store, receipt = run_function(mod, "add", {}, {"x": 1.5, "y": 2.0})
        self.assertEqual(result, 3.5)
        self.assertIn("z", store)
        self.assertEqual(receipt.step_id, 0)


if __name__ == "__main__":
    unittest.main()
