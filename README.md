# Noetica

This repository ships three minimal kernel packages with clean boundaries:

- **NSC** (Deterministic Governed Execution Substrate) - runtime execution, receipts, replay, contracts
- **Noetica** (Semantic Language Kernel) - glyphs → AST → types → action emission
- **Coherence** (Certified Debt Governance) - mathematical certification of debt bounds

The normative bridge between the three is documented in:
- [noetica-kernels/SPEC/kernel_contract.md](noetica-kernels/SPEC/kernel_contract.md)
- [noetica-kernels/SPEC/interface_seam.md](noetica-kernels/SPEC/interface_seam.md)

## Package map

- [nsc-kernel](nsc-kernel) (execution substrate, receipts, replay, contracts)
- [noetica-kernel](noetica-kernel) (semantic kernel, grammar, typing, runtime)
- [coherence-kernel](coherence-kernel) (certified debt governance, mathematical spec)
- [noetica-kernels](noetica-kernels) (combined contract spine and CI)

## Run tests

From the repo root:

```bash
python coherence-kernel/tests/test_ck0_reference_model.py
python noetica-kernel/tests/test_nk0_parse_type_run.py
python noetica-kernel/tests/test_nk0_replay.py
```

Or run the combined script:

```bash
python noetica-kernels/CI/run_all_tests.py
```

Single command:

```bash
make test
```

## Architecture

```
Noetica (Semantic Kernel)
    │
    │ Action stream
    ▼
NSC (Execution Substrate)
    │
    │ Certification requests
    ▼
Coherence (Certified Debt)
```

## Conformance

A system conforms to Noetica if it implements all three kernels:

- **Noetica** defines meaning (glyphs → typed actions)
- **NSC** defines execution (deterministic, audited, governed)
- **Coherence** defines certification (debt bounds, Lyapunov stability)
