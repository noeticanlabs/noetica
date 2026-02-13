# NK-0 Security Posture (Normative)

The NK-0 reference runtime is a minimal deterministic interpreter and is not a
secure sandbox.

Conforming implementations MUST reject any AST node that is not explicitly
whitelisted by the NK-0 grammar and typing rules. In particular, attribute
access, function calls outside declared kernels, subscripting, and comprehensions
MUST be rejected.
