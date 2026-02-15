# NSC Rails Specification

## Overview

Rails define permitted update directions or action classes for execution. They provide deterministic constraints on state transitions.

---

## Rail Modes

### Reject Mode

Invalid steps are rejected entirely:

```
RailReject: if step not in permitted_set → reject
```

### Project Mode

Steps are projected onto permitted subspace:

```
RailProject: step' = project(step, permitted_subspace)
```

Projection is deterministic and logged in receipt.

---

## Rail Definition

```json
{
  "rail": {
    "mode": "reject|project",
    "constraints": [
      { "type": "direction", "value": [1, 0, 0] },
      { "type": "bound", "max": 100.0 },
      { "type": "action_whitelist": ["WRITE", "CALL"] }
    ]
  }
}
```

---

## Rail Enforcement

### Check Function

```
check_rail(action, rail) → (bool, projected_action)
```

1. If mode is "reject":
   - Check action against whitelist/blacklist
   - Return (valid, action)

2. If mode is "project":
   - Apply deterministic projection
   - Return (true, projected_action)

---

## Integration with Receipts

Rail enforcement is logged in receipts:

```json
{
  "rail_enforcement": {
    "mode": "project",
    "original_action": { ... },
    "projected_action": { ... },
    "projection_function": "..."
  }
}
```

---

## Schema

See `nsc-kernel/schemas/nsc_rail.schema.json` for JSON Schema definition.
