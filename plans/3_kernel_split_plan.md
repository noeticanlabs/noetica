# 3-Kernel Split Plan: NSC + Noetica + Coherence

## Overview

This plan outlines the architectural split of the current Noetica kernel codebase into three distinct kernels per your specification:

| Kernel | Name | Role | Source |
|--------|------|------|--------|
| **NSC** | Deterministic Governed Execution Substrate | Runtime execution, receipts, replay, contracts, rails, canonicalization enforcement | ** create new nsc0-NSC-kernel** | **Extract from `nk0-noetica-kernel` (runtime/receipts/replay)** + shared spec |
| **Noetica** | Semantic Language Kernel | Glyphs → AST/IR → types → reduction → action emission | **Extract from `nk0-noetica-kernel` (grammar/typing/semantics/glyphs)** |
| **Coherence** | Certified Debt Governance | Residual-energy geometry, curvature/budget law, debt certification, proof artifacts | **From `ck0-coherence-kernel`** (math + Lean + reference model) |

---

## Current State Analysis

### `nk0-noetica-kernel/` (execution + semantics)
Contains:
- Grammar (EBNF)
- Typing rules
- Operational semantics
- **Parser, AST, typechecker, runtime** ← NSC material
- **Receipt/replay implementation** ← NSC material
- **Canonicalization** ← NSC material

### `ck0-coherence-kernel/` (math + governance)
Contains:
- Coherence kernel mathematical specification (residuals, energy functional, curvature)
- Lean formalization (CK0.lean, CK0V11.lean, Receipts.lean, Theorems.lean)
- Python reference model (math parts)
- Receipt schemas ← Coherence material (normative definitions)

---

## Target Architecture

```
noetica/
├── nsc-kernel/           # NEW: Deterministic Governed Execution Substrate
│   ├── SPEC/
│   │   ├── nsc_spec.md              # Runtime kernel spec (per your Section A)
│   │   ├── nsc_receipts.md           # Receipt chain spec
│   │   ├── nsc_replay.md             # Replay verification spec
│   │   ├── nsc_contracts.md          # L0/L1/L2 contracts
│   │   └── nsc_rails.md              # Rail enforcement spec
│   ├── src/                          # Python runtime
│   ├── lean/                         # Lean formalization (subset of current)
│   ├── schemas/                      # NSC receipt/replay schemas
│   ├── test_vectors/
│   └── tests/
│
├── noetica-kernel/       # RENAMED: Semantic Language Kernel
│   ├── SPEC/
│   │   ├── noetica_spec.md           # Language kernel spec (per your Section B)
│   │   ├── noetica_grammar.ebnf      # Glyph/AST grammar
│   │   ├── noetica_typing.md         # Type system
│   │   ├── noetica_semantics.md      # Operational semantics + action algebra
│   │   └── noetica_glyphs.md         # Glyph semantics
│   ├── src/                          # Parser, AST, typecheck, runtime
│   ├── examples/
│   ├── schemas/
│   ├── test_vectors/
│   └── tests/
│
├── coherence-kernel/     # NEW: Certified Debt Governance
│   ├── SPEC/
│   │   ├── coherence_spec.md         # Mathematical spec (current ck0_spec.md)
│   │   ├── coherence_theorems.md     # Lyapunov, domination, drift
│   │   └── coherence_certification.md # Proof/checker interface
│   ├── src/                          # Python reference model
│   ├── lean/                         # Lean formalization (current CK0.lean)
│   ├── schemas/
│   ├── test_vectors/
│   └── tests/
│
└── noetica-kernels/     # Updated: Combined contract spine
    ├── SPEC/
    │   ├── kernel_contract.md        # Updated: NSC ↔ Noetica ↔ Coherence
    │   └── interface_seam.md         # NEW: Interface specification
    └── CI/
```

---

## Implementation Steps

### Phase 1: Create Directory Structure

1. Create `nsc-kernel/` directory structure mirroring existing patterns
2. Create `coherence-kernel/` directory structure from existing `ck0-coherence-kernel/`
3. Rename `nk0-noetica-kernel/` → `noetica-kernel/`

### Phase 2: NSC Kernel (Execution Substrate)

1. **Create `nsc-kernel/SPEC/nsc_spec.md`**
   - Runtime state model Σ = (S, E, K, Ω)
   - Deterministic step function
   - **Canonicalization** (normative responsibility - Noetica provides serializable state)
   - Receipt chain specification
   - Contract admissibility (L0/L1/L2)
   - Rail enforcement
   - Debt/budget interface (calls Coherence for certified debt)
   - Replay determinism guarantees

2. **Extract execution code from `nk0-noetica-kernel/`** ← CORRECTED SOURCE
   - Receipt chain logic
   - Replay verification
   - Contract enforcement
   - Rail enforcement
   - Canonicalization implementation
   - Runtime step loop

3. **Create NSC schemas**
   - `nsc_receipt.schema.json`
   - `nsc_replay_report.schema.json`

### Phase 3: Noetica Kernel (Semantic Language)

1. **Rename `nk0-noetica-kernel/` → `noetica-kernel/`**

2. **Extract semantic layer from existing nk0**
   - Grammar (EBNF)
   - Typing rules
   - Operational semantics
   - Glyph semantics and lowering
   - Action algebra definition (WRITE, CALL, ASSERT, REPAIR, SOLVE, MEASURE)

3. **Update SPEC files with new naming**
   - Document action algebra as the stable ABI to NSC
   - Define canonicalizable semantic-state serialization rules (but NOT canonicalization algorithm)
   - Document glyph→AST→IR→action lowering pipeline

### Phase 4: Coherence Kernel (Certified Debt)

1. **Create `coherence-kernel/` from `ck0-coherence-kernel/`**
   - Copy all SPEC, lean, schemas, tests, test_vectors
   - Rename from CK-0 to Coherence

2. **Update SPEC documentation**
   - Focus on mathematical specification
   - Add interface for certified debt callbacks to NSC
   - Document proof checker interface

### Phase 5: Interface Specification

1. **Update `noetica-kernels/SPEC/kernel_contract.md`**
   - Define 3-way contract: NSC ↔ Noetica ↔ Coherence
   - Document action stream interface
   - Document certified debt callback interface
   - Document receipt verification flow

2. **Create `noetica-kernels/SPEC/interface_seam.md`**
   - Noetica → NSC: action stream, semantic state serialization
   - NSC → Coherence: debt certification requests
   - Coherence → NSC: certified debt values
   - NSC → Noetica: execution results, governance failures

### Phase 6: Testing and CI

1. Update test file imports
2. Update CI scripts
3. Run all tests to verify split works

---

## Key Interface Contracts

### Noetica → NSC Interface (Action Algebra - Stable ABI)
```
Action: { type: "WRITE" | "CALL" | "ASSERT" | "REPAIR" | "SOLVE" | "MEASURE", ... }
SemanticState: serialized S (must be canonicalizable by NSC)
RegistryDigest: hash of operators/types for replay lock
```

**Noetica defines WHAT actions mean; NSC defines HOW they execute safely.**

### NSC → Coherence Interface (Certified Debt)
```
CertificationRequest: { V_k, B_k, residuals }
CertificationResponse: { D_k, proof_object, timestamp }
```

### Canonicalization (Shared, Normative: NSC)
- **Noetica** provides canonicalizable semantic-state serialization rules
- **NSC** implements canonicalization algorithm (deterministic, schema-stable)
- Spec stays in `noetica-kernels/SPEC/canonicalization.md` (shared)

### NSC Guarantees
- Deterministic execution of actions
- Tamper-evident receipts
- Replay equality
- Fail-closed governance
- Rail-constrained updates
- **Canonicalization** (schema-stable, key-sorted, numeric-canonical)

### Noetica Guarantees
- Well-formedness (grammar)
- Type correctness
- Meaning preservation across lowering
- Deterministic action emission **given the same inputs and registry**
- Provides **canonicalizable** semantic-state serialization (NSC implements canonicalization)

### Coherence Guarantees
- Lyapunov stability certification
- Debt bounds verification
- Perturbation tolerance
- Certified proof objects
- **Certified debt callback interface** for NSC integration

---

## Migration Notes

1. **Breaking changes**: Module names change from `nk0_*` → `noetica_*`
2. **Directory renames**: Explicit user action required for directory structure
3. **Schema changes**: New NSC schemas needed; current NK-0 and CK-0 schemas deprecated
4. **Interface evolution**: The seam between kernels must remain stable once defined

---

## Files to Modify/Create

### New Files (High Priority)
- `plans/3_kernel_split_plan.md` (this file)
- `nsc-kernel/SPEC/nsc_spec.md`
- `nsc-kernel/SPEC/nsc_receipts.md`
- `nsc-kernel/SPEC/nsc_replay.md`
- `nsc-kernel/SPEC/nsc_contracts.md`
- `nsc-kernel/SPEC/nsc_rails.md`
- `coherence-kernel/SPEC/coherence_spec.md`
- `coherence-kernel/SPEC/coherence_certification.md`
- `noetica-kernels/SPEC/interface_seam.md`

### Files to Rename/Repurpose
- `nk0-noetica-kernel/` → `noetica-kernel/`
- `ck0-coherence-kernel/` → `coherence-kernel/`
- `nk0_noetica_spec.md` → `noetica_spec.md`

### Files to Update
- Root `README.md`
- All `SPEC/NORMATIVE.md` files
- Test file imports
- CI scripts
