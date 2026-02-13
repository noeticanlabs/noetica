import hashlib
from typing import Any, Dict, List, Tuple

from nk0_ast import ModuleDef
from nk0_receipts import hash_obj, make_receipt, Receipt


def _safe_eval(expr: str, env: Dict[str, Any]) -> Any:
    return eval(expr, {"__builtins__": {}}, dict(env))


def _module_hash(module: ModuleDef) -> str:
    source = f"{module.name}|{module.budget}|{len(module.functions)}"
    return hashlib.sha256(source.encode("utf-8")).hexdigest()


def _violation(module: ModuleDef, store: Dict[str, Any]) -> float:
    if not module.invariants:
        return 0.0
    ok = all(bool(_safe_eval(inv, store)) for inv in module.invariants)
    return 0.0 if ok else 1.0


def run_function(
    module: ModuleDef,
    fn_name: str,
    initial_store: Dict[str, Any],
    args: Dict[str, Any],
    prev_receipt_hash: str = "0" * 64,
    step_id: int = 0,
    D_k: float = 0.0,
    V_prev: float = 0.0,
) -> Tuple[Any, Dict[str, Any], Receipt]:
    fn = next((f for f in module.functions if f.name == fn_name), None)
    if fn is None:
        raise ValueError(f"unknown function: {fn_name}")

    store = dict(initial_store)
    in_hash = hash_obj(store)

    for name, _ in fn.params:
        if name not in args:
            raise ValueError(f"missing argument: {name}")
        store[name] = args[name]

    V_k = _violation(module, store)
    result = None

    for stmt in fn.body:
        if stmt.startswith("let "):
            lhs, rhs = stmt[4:].split("=", 1)
            store[lhs.strip()] = _safe_eval(rhs.strip().rstrip(";"), store)
        elif stmt.startswith("assert "):
            pred = stmt[len("assert "):].strip().rstrip(";")
            if not bool(_safe_eval(pred, store)):
                V_k1 = 1.0
                dV_k = max(0.0, V_k - V_prev)
                D_k1 = max(0.0, D_k + dV_k - module.budget)
                receipt = make_receipt(
                    {
                        "step_id": step_id,
                        "rule_id": f"{_module_hash(module)}:{fn_name}",
                        "input_hash": in_hash,
                        "output_hash": hash_obj(store),
                        "V_k": V_k,
                        "V_k1": V_k1,
                        "dV_k": dV_k,
                        "B_k": module.budget,
                        "D_k": D_k,
                        "D_k1": D_k1,
                        "prev_receipt_hash": prev_receipt_hash,
                        "status": "FAILED_ASSERT",
                    }
                )
                return None, store, receipt
        elif stmt.startswith("return "):
            result = _safe_eval(stmt[len("return "):].strip().rstrip(";"), store)
            break
        else:
            raise ValueError(f"unsupported statement: {stmt}")

    V_k1 = _violation(module, store)
    dV_k = max(0.0, V_k - V_prev)
    D_k1 = max(0.0, D_k + dV_k - module.budget)

    receipt = make_receipt(
        {
            "step_id": step_id,
            "rule_id": f"{_module_hash(module)}:{fn_name}",
            "input_hash": in_hash,
            "output_hash": hash_obj(store),
            "V_k": V_k,
            "V_k1": V_k1,
            "dV_k": dV_k,
            "B_k": module.budget,
            "D_k": D_k,
            "D_k1": D_k1,
            "prev_receipt_hash": prev_receipt_hash,
            "status": "OK",
        }
    )
    return result, store, receipt


def run_sequence(module: ModuleDef, fn_name: str, calls: List[Dict[str, Any]], initial_store: Dict[str, Any]) -> List[Receipt]:
    receipts: List[Receipt] = []
    store = dict(initial_store)
    prev_hash = "0" * 64
    D_k = 0.0
    V_prev = 0.0
    for step_id, args in enumerate(calls):
        _, store, r = run_function(
            module,
            fn_name,
            store,
            args,
            prev_receipt_hash=prev_hash,
            step_id=step_id,
            D_k=D_k,
            V_prev=V_prev,
        )
        receipts.append(r)
        prev_hash = r.receipt_hash
        D_k = r.D_k1
        V_prev = r.V_k
    return receipts
