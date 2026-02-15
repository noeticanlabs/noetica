# NK-0 Receipts & Replay (Normative)

Receipt hash uses canonical JSON with:
- ../noetica-kernels/SPEC/canonicalization.md

Replay is valid iff:
1) Receipt hash chain verifies
2) Each step input hash matches reconstructed state
3) Deterministic step function reproduces output hash
4) CK-0 linked fields (V, dV, D, B) remain recurrence-consistent

Receipt fields MUST include:
- status: OK | FAILED_ASSERT | INVALID_DEBT | TYPE_ERROR | PARSE_ERROR
- error_code: stable enum identifier
- error_detail: optional string (non-normative)
- spec_version: semantic version of the NK-0 spec
- schema_version: semantic version of the receipt schema
