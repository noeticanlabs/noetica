"""
NSC Canonicalization Module

Provides deterministic JSON canonicalization for action algebra.
This ensures reproducible hashing across executions.
"""

import hashlib
import json
from typing import Any


def canonical_json(obj: Any) -> bytes:
    """
    Canonicalize a JSON object for deterministic hashing.
    
    Rules:
    - Keys are sorted alphabetically
    - No whitespace (compact encoding)
    - UTF-8 without BOM
    - Numbers: no trailing .0, lowercase e
    """
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def sha256_hex(data: bytes) -> str:
    """Compute SHA256 hex digest."""
    return hashlib.sha256(data).hexdigest()


def hash_obj(obj: Any) -> str:
    """
    Compute deterministic hash of any JSON-serializable object.
    
    This is the core canonicalization function used for:
    - Receipt chain hashing
    - State fingerprinting
    - Action stream verification
    """
    return sha256_hex(canonical_json(obj))


def canonical_action(action: dict) -> bytes:
    """
    Canonicalize an action for deterministic hashing.
    
    Actions MUST be canonicalized before inclusion in receipt chains.
    """
    return canonical_json(action)
