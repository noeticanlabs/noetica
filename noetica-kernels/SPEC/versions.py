"""
Noetica Kernel Version Constants

These constants pin the golden vectors to specific versions.
Any change to these versions requires new golden vector folders.
"""

# Action Algebra Version
# Defines the format of actions (WRITE, CALL, ASSERT, etc.)
ACTION_ALGEBRA_VERSION = "1.0"

# Receipt Schema Version
# Defines the format of receipt chains
RECEIPT_SCHEMA_VERSION = "1.0"

# Canonical Profile Version
# Defines the JSON canonicalization rules
CANONICAL_PROFILE_VERSION = "1.0"

# NSC Governance Version
# Defines contract enforcement behavior
NSC_GOVERNANCE_VERSION = "1.0"

# Coherence Kernel Version
# Defines coherence certification interface
CK_VERSION = "1.0"

# All versions as a tuple for compatibility checks
VERSION_TUPLE = (
    ACTION_ALGEBRA_VERSION,
    RECEIPT_SCHEMA_VERSION,
    CANONICAL_PROFILE_VERSION,
    NSC_GOVERNANCE_VERSION,
    CK_VERSION,
)


def get_version_info():
    """Return version information as a dictionary."""
    return {
        "action_algebra_version": ACTION_ALGEBRA_VERSION,
        "receipt_schema_version": RECEIPT_SCHEMA_VERSION,
        "canonical_profile_version": CANONICAL_PROFILE_VERSION,
        "nsc_governance_version": NSC_GOVERNANCE_VERSION,
        "ck_version": CK_VERSION,
    }
