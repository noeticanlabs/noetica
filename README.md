# Noetica

This repository ships two minimal kernel packages with clean boundaries:

- CK-0: a governance-grade coherence contract (spec + Lean core + receipts)
- NK-0: a deterministic execution kernel with receipts and replay

The normative bridge between the two is documented in
[noetica-kernels/SPEC/kernel_contract.md](noetica-kernels/SPEC/kernel_contract.md).

## Package map

- [ck0-coherence-kernel](ck0-coherence-kernel) (spec, schemas, Lean core, Python model)
- [nk0-noetica-kernel](nk0-noetica-kernel) (grammar, typing, runtime, receipts, replay)
- [noetica-kernels](noetica-kernels) (combined contract spine and CI)

## Run tests

From the repo root:

```bash
python ck0-coherence-kernel/tests/test_ck0_reference_model.py
python nk0-noetica-kernel/tests/test_nk0_parse_type_run.py
python nk0-noetica-kernel/tests/test_nk0_replay.py
```

Or run the combined script:

```bash
python noetica-kernels/CI/run_all_tests.py
```

Single command:

```bash
make test
```

## Conformance

CK-0 defines the recurrence laws, debt, and invalidation requirements.
NK-0 defines the deterministic execution substrate and receipt/replay obligations.
Implementations must satisfy both to claim conformance.