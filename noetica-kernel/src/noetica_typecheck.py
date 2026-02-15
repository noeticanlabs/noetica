import ast
from typing import Dict

from noetica_ast import ModuleDef


def _infer_expr_type(expr: str, env: Dict[str, str]) -> str:
    node = ast.parse(expr, mode="eval").body
    if isinstance(node, ast.Constant):
        if isinstance(node.value, bool):
            return "Bool"
        if isinstance(node.value, (int, float)):
            return "Real"
        if isinstance(node.value, str):
            return "Field"
    if isinstance(node, ast.Name):
        if node.id not in env:
            raise TypeError(f"unknown symbol: {node.id}")
        return env[node.id]
    if isinstance(node, ast.BinOp):
        lt = _infer_expr_type(ast.unparse(node.left), env)
        rt = _infer_expr_type(ast.unparse(node.right), env)
        if lt == rt == "Real":
            return "Real"
        raise TypeError("arithmetic ops require Real")
    if isinstance(node, ast.Compare):
        if len(node.ops) != 1 or len(node.comparators) != 1:
            raise TypeError("unsupported compare")
        lt = _infer_expr_type(ast.unparse(node.left), env)
        rt = _infer_expr_type(ast.unparse(node.comparators[0]), env)
        op = node.ops[0]
        if isinstance(op, ast.Eq):
            if lt != rt:
                raise TypeError("== requires same type")
            return "Bool"
        if isinstance(op, (ast.LtE, ast.GtE)):
            if lt == rt == "Real":
                return "Bool"
            raise TypeError("<= and >= require Real")
    raise TypeError(f"unsupported expression: {expr}")


def typecheck_module(module: ModuleDef) -> None:
    if module.budget < 0:
        raise TypeError("budget must be non-negative")

    for fn in module.functions:
        env: Dict[str, str] = {name: typ for name, typ in fn.params}
        saw_return = False
        for stmt in fn.body:
            if stmt.startswith("let "):
                lhs, rhs = stmt[4:].split("=", 1)
                name = lhs.strip()
                expr = rhs.strip().rstrip(";")
                env[name] = _infer_expr_type(expr, env)
            elif stmt.startswith("assert "):
                expr = stmt[len("assert "):].strip().rstrip(";")
                if _infer_expr_type(expr, env) != "Bool":
                    raise TypeError("assert requires Bool expression")
            elif stmt.startswith("return "):
                expr = stmt[len("return "):].strip().rstrip(";")
                et = _infer_expr_type(expr, env)
                if et != fn.ret_type:
                    raise TypeError(f"return type mismatch in {fn.name}: expected {fn.ret_type}, got {et}")
                saw_return = True
            else:
                raise TypeError(f"unsupported statement in {fn.name}: {stmt}")
        if not saw_return:
            raise TypeError(f"function {fn.name} missing return")

    for inv in module.invariants:
        # Invariants are checked with store-provided values at runtime.
        # Syntactically validate as expression.
        ast.parse(inv, mode="eval")
