import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(__file__))
sys.path.append(os.path.join(ROOT, "ref"))

from ck0_reference_model import simulate, verify_chain, CK0Receipt


class TestCK0NegativeCases(unittest.TestCase):
    def test_bad_prev_hash_fails(self):
        receipts, _ = simulate({"V": 0.0, "D": 0.0}, [{"E_k": 0.1, "C_k": 0.0, "B_k": 0.2}], d_max=10.0)
        bad = list(receipts)
        bad[0] = CK0Receipt(**{**bad[0].__dict__, "prev_receipt_hash": "1" * 64})
        ok, msg = verify_chain(bad, d_max=10.0)
        self.assertFalse(ok)
        self.assertIn("prev hash mismatch", msg)


if __name__ == "__main__":
    unittest.main()
