import hashlib
import json
from dataclasses import dataclass, asdict
from typing import Any, Dict, Iterable, Tuple


def canonical_json(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def hash_obj(obj: Any) -> str:
    return sha256_hex(canonical_json(obj))


@dataclass(frozen=True)
class Receipt:
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


def make_receipt(payload: Dict[str, Any]) -> Receipt:
    tmp = dict(payload)
    tmp.pop("receipt_hash", None)
    payload["receipt_hash"] = hash_obj(tmp)
    return Receipt(**payload)


def verify_chain(receipts: Iterable[Receipt]) -> Tuple[bool, str]:
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
