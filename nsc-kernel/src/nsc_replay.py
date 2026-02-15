"""
NSC Replay Module

Provides replay verification for deterministic execution.
Verifies that execution can be reproduced from initial state and receipts.
"""

from typing import List, Dict, Any, Callable

from nsc_receipts import verify_chain
from nsc_canon import hash_obj


def replay_and_verify(
    initial_store: Dict[str, Any],
    receipts: List[Any],
    step_fn: Callable[[Dict[str, Any], int], Dict[str, Any]],
) -> tuple[bool, str]:
    """
    Replay execution and verify against receipts.
    
    This verifies:
    1. Receipt chain integrity (no tampering)
    2. Each step's input matches the previous output
    3. Each step's output matches the recorded output
    
    Returns (True, "replay ok") if verification succeeds,
    or (False, error_message) if verification fails.
    """
    ok, msg = verify_chain(receipts)
    if not ok:
        return False, msg

    store = dict(initial_store)
    for r in receipts:
        if hash_obj(store) != r.input_hash:
            return False, f"input_hash mismatch at step {r.step_id}"
        store_next = step_fn(store, r.step_id)
        if hash_obj(store_next) != r.output_hash:
            return False, f"output_hash mismatch at step {r.step_id}"
        store = store_next
    return True, "replay ok"
