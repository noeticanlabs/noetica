import hashlib
import json
from dataclasses import dataclass, asdict
from typing import Any, Dict, List, Tuple


def canonical_json(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def hash_obj(obj: Any) -> str:
    return sha256_hex(canonical_json(obj))


@dataclass(frozen=True)
class CK0Receipt:
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


def compute_step(V_k: float, V_prev: float, E_k: float, C_k: float, B_k: float, D_k: float, is_first: bool) -> Dict[str, float]:
    V_k1 = max(0.0, V_k + E_k - C_k)
    dV_k = 0.0 if is_first else max(0.0, V_k - V_prev)
    D_k1 = max(0.0, D_k + dV_k - B_k)
    return {"V_k1": V_k1, "dV_k": dV_k, "D_k1": D_k1}


def make_receipt(payload: Dict[str, Any]) -> CK0Receipt:
    tmp = dict(payload)
    tmp.pop("receipt_hash", None)
    payload["receipt_hash"] = hash_obj(tmp)
    return CK0Receipt(**payload)


def verify_chain(receipts: List[CK0Receipt], d_max: float) -> Tuple[bool, str]:
    prev = "0" * 64
    last_v = 0.0
    for i, r in enumerate(receipts):
        if r.prev_receipt_hash != prev:
            return False, f"prev hash mismatch at step {r.step_id}"
        data = asdict(r)
        rh = data.pop("receipt_hash")
        if hash_obj(data) != rh:
            return False, f"receipt hash mismatch at step {r.step_id}"
        expected_dv = 0.0 if i == 0 else max(0.0, r.V_k - last_v)
        if abs(expected_dv - r.dV_k) > 1e-12:
            return False, f"dV mismatch at step {r.step_id}"
        if r.D_k1 > d_max:
            return False, f"invalidation required at step {r.step_id}"
        last_v = r.V_k
        prev = rh
    return True, "ok"


def simulate(initial_state: Dict[str, Any], plan: List[Dict[str, float]], d_max: float = 10.0) -> Tuple[List[CK0Receipt], Dict[str, Any]]:
    state = dict(initial_state)
    V_prev = 0.0
    V_k = float(state.get("V", 0.0))
    D_k = float(state.get("D", 0.0))
    receipts: List[CK0Receipt] = []
    prev_hash = "0" * 64

    for step_id, item in enumerate(plan):
        E_k = float(item["E_k"])
        C_k = float(item["C_k"])
        B_k = float(item["B_k"])
        if C_k < 0 or B_k < 0 or C_k > B_k:
            raise ValueError(f"budget violation at step {step_id}")

        step = compute_step(V_k, V_prev, E_k, C_k, B_k, D_k, is_first=(step_id == 0))
        V_k1 = step["V_k1"]
        dV_k = step["dV_k"]
        D_k1 = step["D_k1"]

        state_in = {"V": V_k, "D": D_k}
        state_out = {"V": V_k1, "D": D_k1}
        payload = {
            "step_id": step_id,
            "rule_id": item.get("rule_id", "ck0.step"),
            "input_hash": hash_obj(state_in),
            "output_hash": hash_obj(state_out),
            "V_k": V_k,
            "V_k1": V_k1,
            "dV_k": dV_k,
            "B_k": B_k,
            "D_k": D_k,
            "D_k1": D_k1,
            "prev_receipt_hash": prev_hash,
        }
        receipt = make_receipt(payload)
        receipts.append(receipt)
        prev_hash = receipt.receipt_hash

        V_prev, V_k, D_k = V_k, V_k1, D_k1
        if D_k > d_max:
            break

    return receipts, {"V": V_k, "D": D_k}
