"""
NSC Runtime Module

Deterministic execution substrate for Noetica actions.
Executes actions, emits receipts, and enforces governance contracts.
"""

import ast
from typing import Any, Dict, List, Tuple

# Note: ModuleDef is a semantic type from Noetica.
# In the long term, NSC should only receive action JSON, not AST types.
# This import represents a boundary crossing that should be addressed in future refactoring.
from noetica_kernel.noetica_ast import ModuleDef

from nsc_receipts import make_receipt, Receipt
from nsc_canon import hash_obj


def _safe_eval(expr: str, env: Dict[str, Any]) -> Any:
    """Safely evaluate an expression in a given environment."""
    node = ast.parse(expr, mode="eval").body

    def eval_node(n: ast.AST) -> Any:
        if isinstance(n, ast.Constant):
            return n.value
        if isinstance(n, ast.Name):
            if n.id not in env:
                raise ValueError(f"unknown symbol: {n.id}")
            return env[n.id]
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, (ast.UAdd, ast.USub)):
            val = eval_node(n.operand)
            if not isinstance(val, (int, float)):
                raise ValueError("unary ops require Real")
            return +val if isinstance(n.op, ast.UAdd) else -val
        if isinstance(n, ast.BinOp) and isinstance(n.op, (ast.Add, ast.Sub, ast.Mult, ast.Div)):
            left = eval_node(n.left)
            right = eval_node(n.right)
            if not isinstance(left, (int, float)) or not isinstance(right, (int, float)):
                raise ValueError("arithmetic ops require Real")
            if isinstance(n.op, ast.Add):
                return left + right
            if isinstance(n.op, ast.Sub):
                return left - right
            if isinstance(n.op, ast.Mult):
                return left * right
            return left / right
        if isinstance(n, ast.Compare):
            if len(n.ops) != 1 or len(n.comparators) != 1:
                raise ValueError("unsupported compare")
            left = eval_node(n.left)
            right = eval_node(n.comparators[0])
            op = n.ops[0]
            if isinstance(op, ast.Eq):
                return left == right
            if not isinstance(left, (int, float)) or not isinstance(right, (int, float)):
                raise ValueError("<= and >= require Real")
            if isinstance(op, ast.LtE):
                return left <= right
            if isinstance(op, ast.GtE):
                return left >= right
        raise ValueError(f"unsupported expression: {expr}")

    return eval_node(node)


def _module_hash(module: ModuleDef) -> str:
    """Compute hash of module definition for receipt rule_id."""
    data = {
        "name": module.name,
        "imports": module.imports,
        "invariants": module.invariants,
        "budget": module.budget,
        "functions": [
            {
                "name": fn.name,
                "params": fn.params,
                "ret_type": fn.ret_type,
                "body": fn.body,
            }
            for fn in module.functions
        ],
    }
    return hash_obj(data)


def _violation(module: ModuleDef, store: Dict[str, Any]) -> float:
    """Compute violation measure (0.0 = no violation, 1.0 = violated)."""
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
    """
    Execute a function step and produce a receipt.
    
    Returns (result, store, receipt) tuple.
    """
    fn = next((f for f in module.functions if f.name == fn_name), None)
    if fn is None:
        raise ValueError(f"unknown function: {fn_name}")

    store = dict(initial_store)
    in_hash = hash_obj(store)

    for name, _ in fn.params:
        if name not in args:
            raise ValueError(f"missing argument: {name}")
        store[name] = args[name]

    V_k = V_prev
    result = None

    for stmt in fn.body:
        if stmt.startswith("let "):
            lhs, rhs = stmt[4:].split("=", 1)
            store[lhs.strip()] = _safe_eval(rhs.strip().rstrip(";"), store)
        elif stmt.startswith("assert "):
            pred = stmt[len("assert "):].strip().rstrip(";")
            if not bool(_safe_eval(pred, store)):
                V_k1 = 1.0
                dV_k = max(0.0, V_k1 - V_k)
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
                        "error_code": "FAILED_ASSERT",
                        "error_detail": "assertion failed",
                        "spec_version": "1.0.0",
                        "schema_version": "1.0.0",
                    }
                )
                return None, store, receipt
        elif stmt.startswith("return "):
            result = _safe_eval(stmt[len("return "):].strip().rstrip(";"), store)
            break
        else:
            raise ValueError(f"unsupported statement: {stmt}")

    V_k1 = _violation(module, store)
    dV_k = max(0.0, V_k1 - V_k)
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
            "error_code": "OK",
            "error_detail": None,
            "spec_version": "1.0.0",
            "schema_version": "1.0.0",
        }
    )
    return result, store, receipt


def run_sequence(
    module: ModuleDef, 
    fn_name: str, 
    calls: List[Dict[str, Any]], 
    initial_store: Dict[str, Any]
) -> List[Receipt]:
    """
    Execute a sequence of function calls and return all receipts.
    
    This is the main entry point for running a program.
    """
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
        V_prev = r.V_k1
    return receipts
