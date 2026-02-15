"""
Noetica Action Emitter Module

Provides action construction and emission for the Noetica semantic kernel.
Actions are the stable ABI between Noetica and NSC.

Action Types:
- WRITE: Write a value to a variable
- CALL: Invoke an operation  
- ASSERT: Assert a predicate
- REPAIR: Request repair hint
- SOLVE: Solve a residual
- MEASURE: Compute a metric
"""

from typing import Any, Dict, List, Optional
import json


# Action type constants
ACTION_WRITE = "WRITE"
ACTION_CALL = "CALL"
ACTION_ASSERT = "ASSERT"
ACTION_REPAIR = "REPAIR"
ACTION_SOLVE = "SOLVE"
ACTION_MEASURE = "MEASURE"


class ActionEmitter:
    """
    Emits deterministic action streams for NSC execution.
    
    This is the primary interface between Noetica (semantics) and NSC (execution).
    All actions are guaranteed to be valid according to action.schema.json.
    """
    
    def __init__(self):
        self._actions: List[Dict[str, Any]] = []
        self._step_id = 0
    
    def emit_write(self, var: str, value: Any) -> Dict[str, Any]:
        """Emit a WRITE action."""
        action = {
            "type": ACTION_WRITE,
            "var": var,
            "value": value,
            "step_id": self._step_id,
            "nonce": f"step_{self._step_id}",
        }
        self._step_id += 1
        self._actions.append(action)
        return action
    
    def emit_call(self, op_id: str, args: List[Any]) -> Dict[str, Any]:
        """Emit a CALL action."""
        action = {
            "type": ACTION_CALL,
            "op_id": op_id,
            "args": args,
            "step_id": self._step_id,
            "nonce": f"step_{self._step_id}",
        }
        self._step_id += 1
        self._actions.append(action)
        return action
    
    def emit_assert(self, pred: str) -> Dict[str, Any]:
        """Emit an ASSERT action."""
        action = {
            "type": ACTION_ASSERT,
            "pred": pred,
            "step_id": self._step_id,
            "nonce": f"step_{self._step_id}",
        }
        self._step_id += 1
        self._actions.append(action)
        return action
    
    def emit_repair(self, hint: str) -> Dict[str, Any]:
        """Emit a REPAIR action."""
        action = {
            "type": ACTION_REPAIR,
            "hint": hint,
            "step_id": self._step_id,
            "nonce": f"step_{self._step_id}",
        }
        self._step_id += 1
        self._actions.append(action)
        return action
    
    def emit_solve(self, residual_id: str, params: Dict[str, Any]) -> Dict[str, Any]:
        """Emit a SOLVE action."""
        action = {
            "type": ACTION_SOLVE,
            "residual_id": residual_id,
            "params": params,
            "step_id": self._step_id,
            "nonce": f"step_{self._step_id}",
        }
        self._step_id += 1
        self._actions.append(action)
        return action
    
    def emit_measure(self, metric_id: str, params: Dict[str, Any]) -> Dict[str, Any]:
        """Emit a MEASURE action."""
        action = {
            "type": ACTION_MEASURE,
            "metric_id": metric_id,
            "params": params,
            "step_id": self._step_id,
            "nonce": f"step_{self._step_id}",
        }
        self._step_id += 1
        self._actions.append(action)
        return action
    
    def get_actions(self) -> List[Dict[str, Any]]:
        """Get all emitted actions."""
        return list(self._actions)
    
    def reset(self):
        """Reset the emitter for a new program."""
        self._actions = []
        self._step_id = 0
    
    def __iter__(self):
        """Iterate over emitted actions."""
        return iter(self._actions)
    
    def __len__(self):
        return len(self._actions)


def canonical_action(action: dict) -> bytes:
    """
    Canonicalize an action for deterministic hashing.
    
    This follows the rules in noetica-kernels/SPEC/action_algebra.md:
    - Keys sorted alphabetically
    - No whitespace (compact JSON)
    - UTF-8 encoding
    """
    return json.dumps(action, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def action_to_json(action: dict) -> str:
    """Serialize action to JSON string."""
    return json.dumps(action, sort_keys=True)


def validate_action(action: dict) -> tuple[bool, Optional[str]]:
    """
    Validate an action against the action schema.
    
    Returns (True, None) if valid, or (False, error_message) if invalid.
    
    Note: Full schema validation requires jsonschema library.
    This is a basic structural validation.
    """
    if "type" not in action:
        return False, "missing required field: type"
    
    action_type = action["type"]
    valid_types = {ACTION_WRITE, ACTION_CALL, ACTION_ASSERT, ACTION_REPAIR, ACTION_SOLVE, ACTION_MEASURE}
    
    if action_type not in valid_types:
        return False, f"invalid action type: {action_type}"
    
    # Type-specific validation
    if action_type == ACTION_WRITE:
        if "var" not in action or "value" not in action:
            return False, "WRITE requires 'var' and 'value'"
    
    elif action_type == ACTION_CALL:
        if "op_id" not in action or "args" not in action:
            return False, "CALL requires 'op_id' and 'args'"
    
    elif action_type == ACTION_ASSERT:
        if "pred" not in action:
            return False, "ASSERT requires 'pred'"
    
    elif action_type == ACTION_REPAIR:
        if "hint" not in action:
            return False, "REPAIR requires 'hint'"
    
    elif action_type == ACTION_SOLVE:
        if "residual_id" not in action or "params" not in action:
            return False, "SOLVE requires 'residual_id' and 'params'"
    
    elif action_type == ACTION_MEASURE:
        if "metric_id" not in action or "params" not in action:
            return False, "MEASURE requires 'metric_id' and 'params'"
    
    return True, None
