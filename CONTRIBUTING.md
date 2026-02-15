# Contributing to Noetica

## Kernel Boundary Rules

This project implements a **3-kernel architecture** with strict boundaries. All contributors must understand and respect these boundaries.

### The Three Kernels

| Kernel | Name | Responsibility |
|--------|------|-----------------|
| **NSC** | Deterministic Governed Execution Substrate | Runtime execution, receipts, replay, contracts, rails, canonicalization enforcement |
| **Noetica** | Semantic Language Kernel | Glyphs → AST/IR → types → reduction → action emission |
| **Coherence** | Certified Debt Governance | Residual-energy geometry, curvature/budget law, debt certification, proof artifacts |

### Action Algebra (Stable ABI)

The **Action Algebra** is the only stable ABI between kernels:

- **Noetica → NSC**: Actions are emitted as JSON objects
- **NSC → Coherence**: Debt queries via callback interface
- **No kernel reaches across boundaries** except through these defined interfaces

### Action Schema

All actions must validate against `noetica-kernels/schemas/action.schema.json`.

### Versioning

- **Action Algebra**: `action_algebra_version = MAJOR.MINOR`
- Changes to the action schema require:
  1. Version bump (MAJOR if breaking)
  2. Compatibility note in CHANGELOG
  3. Golden vector updates if canonicalization changes

## Development Rules

### No Compiled Artifacts in PRs

Do not commit:
- `__pycache__/` directories
- `*.pyc` files
- `.pyo` files
- Build artifacts (`dist/`, `build/`, `*.egg-info/`)

These are automatically excluded via `.gitignore`.

### Import Boundaries

| From | Can Import |
|------|------------|
| `noetica-kernel/src/*` | `noetica-kernel/src/*`, `noetica-kernels/schemas/*` |
| `nsc-kernel/src/*` | `nsc-kernel/src/*`, `noetica-kernels/schemas/*` |
| `coherence-kernel/src/*` | `coherence-kernel/src/*` |

**Forbidden**: NSC must NOT import Noetica's AST/parser/typecheck modules. Noetica must NOT import NSC's receipts/replay.

### Testing Requirements

Before submitting a PR, ensure:

1. **Determinism tests pass** - same program + input → identical action stream
2. **Boundary tests pass** - kernel isolation is verified
3. **ABI compatibility tests pass** - actions validate against schema

### Pull Request Guidelines

1. Create a feature branch
2. Follow the kernel responsibility table above
3. Update relevant SPEC documents if changing interfaces
4. Add test vectors for schema changes
5. Run full test suite: `python noetica-kernels/CI/run_all_tests.py`

## Getting Help

- See `noetica-kernels/SPEC/interface_seam.md` for ABI details
- See `noetica-kernels/SPEC/kernel_contract.md` for contract details
- See individual kernel READMEs for kernel-specific documentation
