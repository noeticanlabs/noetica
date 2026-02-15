"""
NSC Golden Vector Test Runner

This module provides the test runner for NSC golden vectors.
It verifies that the NSC kernel produces deterministic, reproducible results.

Usage:
    python -m nsc_kernel.tests.test_golden_vectors
"""

import json
import os
import sys
import unittest
from pathlib import Path
from typing import Any, Dict, List, Tuple

# Add src to path for imports
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "nsc-kernel" / "src"))
sys.path.insert(0, str(ROOT / "noetica-kernel" / "src"))

# Import NSC modules
try:
    from nsc_canon import hash_obj
    from nsc_receipts import make_receipt, verify_chain
    from nsc_runtime import run_function
    from noetica_ast import ModuleDef, FunctionDef
except ImportError as e:
    print(f"Error: Could not import NSC modules: {e}")
    print("Please ensure the environment is set up correctly.")
    sys.exit(1)


def load_module_from_json(data: Dict[str, Any]) -> ModuleDef:
    """Create a ModuleDef from input JSON data."""
    module_data = data["module"]
    
    functions = []
    for fn in module_data.get("functions", []):
        functions.append(FunctionDef(
            name=fn["name"],
            params=fn.get("params", []),
            ret_type=fn.get("ret_type", "Real"),
            body=fn.get("body", [])
        ))
    
    return ModuleDef(
        name=module_data["name"],
        imports=module_data.get("imports", []),
        invariants=module_data.get("invariants", []),
        budget=module_data.get("budget", 1.0),
        functions=functions
    )


def receipt_to_dict(receipt) -> Dict[str, Any]:
    """Convert a Receipt dataclass to a dictionary."""
    return {
        "step_id": receipt.step_id,
        "rule_id": receipt.rule_id,
        "input_hash": receipt.input_hash,
        "output_hash": receipt.output_hash,
        "V_k": receipt.V_k,
        "V_k1": receipt.V_k1,
        "dV_k": receipt.dV_k,
        "B_k": receipt.B_k,
        "D_k": receipt.D_k,
        "D_k1": receipt.D_k1,
        "prev_receipt_hash": receipt.prev_receipt_hash,
        "status": receipt.status,
        "error_code": receipt.error_code,
        "error_detail": receipt.error_detail,
        "spec_version": receipt.spec_version,
        "schema_version": receipt.schema_version,
    }


class TestGoldenVectors(unittest.TestCase):
    """Test cases for NSC golden vectors."""
    
    @classmethod
    def setUpClass(cls):
        """Load the golden vector test cases."""
        cls.vectors_dir = ROOT / "nsc-kernel" / "test_vectors" / "action_v1"
        cls.test_cases = []
        
        # Load manifest
        manifest_path = cls.vectors_dir / "manifest.json"
        if manifest_path.exists():
            with open(manifest_path) as f:
                manifest = json.load(f)
                cls.test_cases = [tc["id"] for tc in manifest.get("test_cases", [])]
    
    def test_01_simple_write(self):
        """Test case 01: Simple variable write."""
        self._run_test_case("01_simple_write")
    
    def test_02_function_call(self):
        """Test case 02: Function call."""
        self._run_test_case("02_function_call")
    
    def test_03_assert_pass(self):
        """Test case 03: Assertion that passes."""
        self._run_test_case("03_assert_pass")
    
    def test_04_assert_fail(self):
        """Test case 04: Assertion that fails."""
        self._run_test_case("04_assert_fail")
    
    def test_05_budget_violation(self):
        """Test case 05: Budget violation."""
        self._run_test_case("05_budget_violation")
    
    def _run_test_case(self, test_id: str):
        """Run a single golden vector test case."""
        test_dir = self.vectors_dir / test_id
        
        # Load input
        input_path = test_dir / "input.json"
        with open(input_path) as f:
            input_data = json.load(f)
        
        # Load expected output
        expected_path = test_dir / "expected_receipts.json"
        with open(expected_path) as f:
            expected_data = json.load(f)
        
        # Create module from input
        module = load_module_from_json(input_data)
        initial_store = input_data.get("initial_store", {})
        calls = input_data.get("calls", [{}])
        
        # Execute
        receipts = []
        store = dict(initial_store)
        prev_hash = "0" * 64
        
        for call_args in calls:
            try:
                result, store, receipt = run_function(
                    module,
                    "main",
                    store,
                    call_args,
                    prev_receipt_hash=prev_hash,
                    step_id=len(receipts),
                )
                receipts.append(receipt)
                prev_hash = receipt.receipt_hash
            except Exception as e:
                # For failure cases, we may get an exception
                print(f"  Exception (expected for failure cases): {e}")
                break
        
        # Verify receipts
        expected_receipts = expected_data.get("receipts", [])
        
        # Check number of receipts
        self.assertEqual(
            len(receipts), 
            len(expected_receipts),
            f"Receipt count mismatch for {test_id}"
        )
        
        # Check each receipt
        for i, (receipt, expected) in enumerate(zip(receipts, expected_receipts)):
            rdict = receipt_to_dict(receipt)
            
            # Check status
            self.assertEqual(
                rdict["status"],
                expected.get("status", "OK"),
                f"Status mismatch at step {i} for {test_id}"
            )
            
            # Check governance values
            if "V_k1" in expected and expected["V_k1"] != "auto-computed":
                self.assertAlmostEqual(
                    rdict["V_k1"],
                    expected["V_k1"],
                    places=5,
                    msg=f"V_k1 mismatch at step {i} for {test_id}"
                )
            
            if "D_k1" in expected and expected["D_k1"] != "auto-computed":
                self.assertAlmostEqual(
                    rdict["D_k1"],
                    expected["D_k1"],
                    places=5,
                    msg=f"D_k1 mismatch at step {i} for {test_id}"
                )


def main():
    """Run the golden vector tests."""
    # Discover and run tests
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromTestCase(TestGoldenVectors)
    
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Return exit code
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())
