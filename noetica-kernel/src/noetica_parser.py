import re
from typing import List, Tuple

from noetica_ast import FunctionDef, ModuleDef


MODULE_RE = re.compile(r"module\s+([A-Za-z_][A-Za-z0-9_]*)\s*\{(.*)\}\s*$", re.S)
IMPORT_RE = re.compile(r"import\s+([A-Za-z_][A-Za-z0-9_]*)\s*;")
INVARIANT_RE = re.compile(r"invariant\s+(.+?)\s*;")
BUDGET_RE = re.compile(r"budget\s+(-?\d+(?:\.\d+)?)\s*;")
FN_RE = re.compile(
    r"fn\s+([A-Za-z_][A-Za-z0-9_]*)\s*\((.*?)\)\s*->\s*(Real|Bool|State|Field)\s*\{(.*?)\}",
    re.S,
)


def _parse_params(param_src: str) -> List[Tuple[str, str]]:
    src = param_src.strip()
    if not src:
        return []
    params = []
    for part in src.split(","):
        part = part.strip()
        name, typ = [x.strip() for x in part.split(":", 1)]
        params.append((name, typ))
    return params


def parse_module(source: str) -> ModuleDef:
    m = MODULE_RE.match(source.strip())
    if not m:
        raise ValueError("invalid module syntax")
    name, body = m.group(1), m.group(2)

    imports = IMPORT_RE.findall(body)
    invariants = [x.strip() for x in INVARIANT_RE.findall(body)]

    budget_match = BUDGET_RE.search(body)
    if not budget_match:
        raise ValueError("missing budget declaration")
    budget = float(budget_match.group(1))

    functions = []
    for fnm in FN_RE.finditer(body):
        fname, params_src, ret_type, block = fnm.groups()
        params = _parse_params(params_src)
        stmts = [line.strip() for line in block.splitlines() if line.strip()]
        functions.append(FunctionDef(name=fname, params=params, ret_type=ret_type, body=stmts))

    if not functions:
        raise ValueError("module must declare at least one function")

    return ModuleDef(name=name, imports=imports, invariants=invariants, budget=budget, functions=functions)
