import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(__file__))
sys.path.append(os.path.join(ROOT, "ref"))

from ck0_reference_model import simulate, verify_chain


class TestCK0ReferenceModel(unittest.TestCase):
    def test_chain_verifies(self):
        receipts, final_state = simulate(
            {"V": 0.1, "D": 0.0},
            [
                {"E_k": 0.4, "C_k": 0.2, "B_k": 0.3, "rule_id": "r"},
                {"E_k": 0.1, "C_k": 0.1, "B_k": 0.3, "rule_id": "r"},
            ],
            d_max=10.0,
        )
        ok, msg = verify_chain(receipts, d_max=10.0)
        self.assertTrue(ok, msg)
        self.assertGreaterEqual(final_state["V"], 0.0)

    def test_budget_violation_raises(self):
        with self.assertRaises(ValueError):
            simulate({"V": 0.0, "D": 0.0}, [{"E_k": 0.1, "C_k": 0.5, "B_k": 0.1}], d_max=10.0)


if __name__ == "__main__":
    unittest.main()
