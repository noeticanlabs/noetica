"""
Coherence Callback Interface

This module defines the callback interface between NSC and Coherence.
NSC uses this interface to request debt certification from Coherence.

This is the NSC → Coherence boundary. NSC should only depend on this
interface, not on Coherence's internal math.
"""

from typing import Any, Dict, Optional
from dataclasses import dataclass


@dataclass
class CertificationRequest:
    """
    Request from NSC to Coherence for debt certification.
    
    Fields:
    - V_k: Current invariant violations measure
    - B_k: Current budget
    - residuals: List of residual identifiers
    - step_id: Current execution step
    """
    V_k: float
    B_k: float
    residuals: list[str]
    step_id: int
    timestamp: str


@dataclass
class CertificationResponse:
    """
    Response from Coherence to NSC with certified debt.
    
    Fields:
    - D_k: Certified debt value
    - debt_total: Running total debt
    - proof_object_digest: Optional proof artifact digest
    - curvature: Optional curvature metric
    - budget_recommendation: Optional budget recommendation
    - valid: Whether certification succeeded
    - error_message: Error message if valid=False
    """
    D_k: float
    debt_total: float
    proof_object_digest: Optional[str] = None
    curvature: Optional[float] = None
    budget_recommendation: Optional[float] = None
    valid: bool = True
    error_message: Optional[str] = None


class CoherenceCallback:
    """
    Callback interface for NSC to communicate with Coherence.
    
    This class provides a stable interface that NSC uses to request
    debt certification. The actual implementation can be swapped
    (e.g., stub for testing, real implementation for production).
    """
    
    def __init__(self, stub_mode: bool = False):
        """
        Initialize the callback.
        
        Args:
            stub_mode: If True, return deterministic stub responses
                       instead of calling the real Coherence math.
        """
        self._stub_mode = stub_mode
        self._debt_total = 0.0
    
    def request_certification(
        self, 
        V_k: float, 
        B_k: float, 
        residuals: list[str],
        step_id: int
    ) -> CertificationResponse:
        """
        Request debt certification from Coherence.
        
        Args:
            V_k: Current invariant violations measure
            B_k: Current budget
            residuals: List of residual identifiers
            step_id: Current execution step
            
        Returns:
            CertificationResponse with certified debt and optional proof
        """
        if self._stub_mode:
            return self._stub_certification(V_k, B_k, residuals, step_id)
        
        # TODO: Implement actual Coherence math call
        # For now, return stub
        return self._stub_certification(V_k, B_k, residuals, step_id)
    
    def _stub_certification(
        self, 
        V_k: float, 
        B_k: float, 
        residuals: list[str],
        step_id: int
    ) -> CertificationResponse:
        """
        Stub implementation for testing.
        
        Returns deterministic responses for testing purposes.
        """
        # Simple stub: debt increases with violations
        dV = max(0.0, V_k)  # Violation delta
        D_k = dV  # Debt increment
        self._debt_total = max(0.0, self._debt_total + D_k - B_k)
        
        return CertificationResponse(
            D_k=D_k,
            debt_total=self._debt_total,
            proof_object_digest=f"stub_proof_{step_id}",
            curvature=0.5,  # Stub value
            budget_recommendation=B_k,  # Stub: recommend current budget
            valid=True,
            error_message=None
        )
    
    def reset(self):
        """Reset the callback state (for testing)."""
        self._debt_total = 0.0


def create_coherence_callback(stub_mode: bool = False) -> CoherenceCallback:
    """
    Factory function to create a Coherence callback.
    
    Args:
        stub_mode: If True, create a stub callback for testing
        
    Returns:
        CoherenceCallback instance
    """
    return CoherenceCallback(stub_mode=stub_mode)
