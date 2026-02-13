from dataclasses import dataclass
from typing import List, Tuple


@dataclass(frozen=True)
class FunctionDef:
    name: str
    params: List[Tuple[str, str]]
    ret_type: str
    body: List[str]


@dataclass(frozen=True)
class ModuleDef:
    name: str
    imports: List[str]
    invariants: List[str]
    budget: float
    functions: List[FunctionDef]
