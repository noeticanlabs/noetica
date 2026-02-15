#!/usr/bin/env python3
"""
Noetica Orchestration Script

This script demonstrates the 3-kernel flow:
1. Noetica parses and emits actions (semantic kernel)
2. NSC executes actions and produces receipts (execution kernel)
3. Coherence certifies debt (governance kernel)

This is the "demo truth" - what CI should run.
"""

import json
import sys
from pathlib import Path

# Add parent to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from noetica_kernel.noetica_parser import parse_module
from noetica_kernel.noetica_typecheck import typecheck_module
from noetica_kernel.noetica_actions import ActionEmitter

# Note: NSC imports - this is the kernel boundary
from nsc_kernel.nsc_runtime import run_function, run_sequence
from nsc_kernel.nsc_receipts import verify_chain
from coherence_kernel.coherence_callback import create_coherence_callback


def run_program(program_source: str, fn_name: str, initial_store: dict, args: dict):
    """
    Run a Noetica program through the full kernel pipeline.
    
    Args:
        program_source: Noetica program source code
        fn_name: Function to execute
        initial_store: Initial variable store
        args: Function arguments
        
    Returns:
        dict with result, store, receipts, and verification status
    """
    # Step 1: Noetica parses the program
    print("=== Noetica Kernel (Parsing) ===")
    module = parse_module(program_source)
    print(f"Parsed module: {module.name}")
    
    # Step 2: Noetica typechecks
    print("\n=== Noetica Kernel (Type Checking) ===")
    typecheck_module(module)
    print("Type checking passed")
    
    # Step 3: Emit actions (Noetica → NSC boundary)
    print("\n=== Noetica Kernel (Action Emission) ===")
    emitter = ActionEmitter()
    # TODO: Integrate action emission with actual program execution
    # For now, we directly run via NSC
    print("Action emitter ready")
    
    # Step 4: NSC executes the program
    print("\n=== NSC Kernel (Execution) ===")
    result, store, receipt = run_function(
        module, 
        fn_name, 
        initial_store, 
        args
    )
    print(f"Execution result: {result}")
    print(f"Final store: {store}")
    print(f"Receipt: {receipt.status}")
    
    # Step 5: Coherence certifies debt (optional demo)
    print("\n=== Coherence Kernel (Debt Certification) ===")
    coherence = create_coherence_callback(stub_mode=True)
    cert = coherence.request_certification(
        V_k=receipt.V_k1,
        B_k=receipt.B_k,
        residuals=[],  # Would come from actual program
        step_id=receipt.step_id
    )
    print(f"Certified debt: {cert.D_k}")
    print(f"Debt total: {cert.debt_total}")
    
    return {
        "result": result,
        "store": store,
        "receipt": receipt.__dict__,
        "certification": {
            "D_k": cert.D_k,
            "debt_total": cert.debt_total,
            "valid": cert.valid
        }
    }


def main():
    """Main entry point."""
    # Demo program
    demo_program = """
module demo {
    budget: 1.0;
    
    invariants: [
        "x >= 0"
    ];
    
    function incr(x: int) -> int {
        let y = x + 1;
        assert "y > x";
        return y;
    }
}
"""
    
    # Run the program
    result = run_program(
        program_source=demo_program,
        fn_name="incr",
        initial_store={},
        args={"x": 5}
    )
    
    print("\n=== Final Result ===")
    print(json.dumps(result, indent=2, default=str))
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
