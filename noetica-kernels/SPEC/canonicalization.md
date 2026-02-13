# Canonicalization (Normative)

This document defines canonical encoding shared by CK-0 and NK-0.

## Canonical JSON
All receipt hashes and state hashes MUST use the following canonical JSON:

- UTF-8 encoding
- Sorted object keys
- No whitespace (separators are `,` and `:`)
- No NaN or Infinity values

## Numeric encoding
Real numbers MUST be encoded as decimal strings with a fixed precision policy.
The reference policy for kernel-grade replay is:

- 17 significant digits
- No trailing zeros beyond the decimal point
- A leading `-` for negative values only

Implementations MAY use rationals in place of decimal strings, but MUST declare
the format and preserve deterministic replay.
