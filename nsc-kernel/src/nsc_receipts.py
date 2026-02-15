"""
NSC Receipt Module

Provides receipt chain generation and verification for deterministic execution.
Receipts provide tamper-evidence for NSC execution steps.
"""

from dataclasses import dataclass, asdict
from typing import Any, Dict, Iterable, Tuple

from nsc_canon import hash_obj


@dataclass(frozen=True)
class Receipt:
    """Tamper-evident receipt for NSC execution steps."""
    step_id: int
    rule_id: str
    input_hash: str
    output_hash: str
    V_k: float
    V_k1: float
    dV_k: float
    B_k: float
    D_k: float
    D_k1: float
    prev_receipt_hash: str
    receipt_hash: str
    status: str = "OK"
    error_code: str = "OK"
    error_detail: str | None = None
    spec_version: str = "1.0.0"
    schema_version: str = "1.0.0"


def make_receipt(payload: Dict[str, Any]) -> Receipt:
    """
    Create a receipt from a payload dictionary.
    
    The receipt_hash is computed automatically from the other fields.
    """
    tmp = dict(payload)
    tmp.pop("receipt_hash", None)
    payload.setdefault("status", "OK")
    payload.setdefault("error_code", "OK")
    payload.setdefault("error_detail", None)
    payload.setdefault("spec_version", "1.0.0")
    payload.setdefault("schema_version", "1.0.0")
    payload["receipt_hash"] = hash_obj(tmp)
    return Receipt(**payload)


def verify_chain(receipts: Iterable[Receipt]) -> Tuple[bool, str]:
    """
    Verify the integrity of a receipt chain.
    
    Returns (True, "ok") if valid, or (False, error_message) if invalid.
    """
    prev = "0" * 64
    for r in receipts:
        if r.prev_receipt_hash != prev:
            return False, f"prev hash mismatch at step {r.step_id}"
        tmp = asdict(r)
        rh = tmp.pop("receipt_hash")
        if hash_obj(tmp) != rh:
            return False, f"receipt hash mismatch at step {r.step_id}"
        prev = rh
    return True, "ok"
