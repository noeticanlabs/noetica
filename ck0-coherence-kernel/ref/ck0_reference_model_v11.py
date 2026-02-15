"""
CK-0 Coherence Kernel v1.1 Reference Implementation

This module implements the referee-hardened v1.1 specification:
- Hilbert space state model
- Coordinate-stable curvature via baseline metric G₀
- Certified perturbation bounds
- Step operator abstraction
- Debt dynamics with curvature weighting
- Budget law with curvature tax
- CTD time reparameterization
"""

import hashlib
import json
import math
from dataclasses import dataclass, asdict, field
from typing import Any, Dict, List, Tuple, Optional, Callable, Protocol
from abc import ABC, abstractmethod
import numpy as np
from numpy.typing import NDArray


# =============================================================================
# Section 1: State Model (Hilbert Space)
# =============================================================================

class HilbertSpace(Protocol):
    """Protocol for Hilbert space state representation."""
    
    @property
    def dimension(self) -> int:
        """Dimension of the Hilbert space (for finite-dimensional case)."""
        ...
    
    def inner_product(self, x: NDArray, y: NDArray) -> float:
        """Inner product ⟨x, y⟩."""
        ...
    
    def norm(self, x: NDArray) -> float:
        """Norm ‖x‖ = sqrt(⟨x, x⟩)."""
        ...


class FiniteDimensionalHilbertSpace:
    """Finite-dimensional Hilbert space (ℝ^n or ℂ^n)."""
    
    def __init__(self, dimension: int, inner_product: Optional[Callable[[NDArray, NDArray], float]] = None):
        self._dimension = dimension
        self._inner_product = inner_product or (lambda x, y: float(np.dot(x, y)))
    
    @property
    def dimension(self) -> int:
        return self._dimension
    
    def inner_product(self, x: NDArray, y: NDArray) -> float:
        return self._inner_product(x, y)
    
    def norm(self, x: NDArray) -> float:
        return math.sqrt(self.inner_product(x, x))
    
    def zero(self) -> NDArray:
        return np.zeros(self._dimension)


# =============================================================================
# Section 2: Residual Structure
# =============================================================================

@dataclass
class ResidualSpace:
    """Residual space Y with inner product."""
    dimension: int
    inner_product_matrix: NDArray  # Matrix M such that ⟨y1, y2⟩ = y1^T M y2
    
    def inner_product(self, y1: NDArray, y2: NDArray) -> float:
        return float(y1 @ self.inner_product_matrix @ y2)
    
    def norm(self, y: NDArray) -> float:
        return math.sqrt(self.inner_product(y, y))


# =============================================================================
# Section 3: Weight Operator
# =============================================================================

@dataclass
class WeightOperator:
    """
    Weight operator W: Y → Y satisfying:
    - Self-adjoint: W = W^*
    - Bounded: ‖W‖ < ∞
    - Coercive: ⟨y, Wy⟩ ≥ c_W ‖y‖²
    """
    matrix: NDArray
    coercivity_constant: float  # c_W
    
    def __post_init__(self):
        # Verify self-adjointness
        if not np.allclose(self.matrix, self.matrix.T):
            raise ValueError("Weight operator must be self-adjoint (symmetric)")
    
    def apply(self, y: NDArray) -> NDArray:
        return self.matrix @ y
    
    def inner_product(self, y1: NDArray, y2: NDArray) -> float:
        return float(y1 @ self.matrix @ y2)
    
    @staticmethod
    def constant(dimension: int, value: float = 1.0) -> 'WeightOperator':
        """Create constant weight operator W = value * I."""
        return WeightOperator(
            matrix=value * np.eye(dimension),
            coercivity_constant=value
        )


# =============================================================================
# Section 4: Coherence Energy
# =============================================================================

@dataclass
class ResidualMap:
    """
    Residual map F: X → Y
    Assumptions:
    - F is continuously differentiable
    - J(x) = DF(x) exists and is bounded
    """
    residual_fn: Callable[[NDArray], NDArray]
    jacobian_fn: Callable[[NDArray], NDArray]  # J(x) as matrix
    
    def __call__(self, x: NDArray) -> NDArray:
        return self.residual_fn(x)
    
    def jacobian(self, x: NDArray) -> NDArray:
        return self.jacobian_fn(x)


class CoherenceEnergy:
    """
    Coherence energy: Φ(x) = 1/2 ⟨F(x), W F(x)⟩
    
    Properties:
    - Φ(x) ≥ 0
    - Φ(x) = 0 ⟺ F(x) = 0
    """
    
    def __init__(
        self,
        residual_map: ResidualMap,
        weight: WeightOperator,
        residual_space: ResidualSpace
    ):
        self.residual_map = residual_map
        self.weight = weight
        self.residual_space = residual_space
    
    def __call__(self, x: NDArray) -> float:
        Fx = self.residual_map(x)
        return 0.5 * self.weight.inner_product(Fx, Fx)
    
    def certified(
        self,
        x: NDArray,
        residual_cert: NDArray,
        weight_cert: WeightOperator
    ) -> float:
        """
        Certified energy computation with declared bounds.
        Used when exact evaluation is too expensive.
        """
        return 0.5 * weight_cert.inner_product(residual_cert, residual_cert)


# =============================================================================
# Section 5: Induced Metric (Gauss-Newton)
# =============================================================================

class InducedMetric:
    """
    Induced metric: G(x) = J(x)^* W J(x)
    
    Properties:
    - Self-adjoint
    - Positive semidefinite
    - Positive definite if J has full rank
    """
    
    def __init__(
        self,
        coherence_energy: CoherenceEnergy,
        hilbert_space: HilbertSpace
    ):
        self.coherence_energy = coherence_energy
        self.hilbert_space = hilbert_space
    
    def compute(self, x: NDArray) -> NDArray:
        """Compute G(x) = J(x)^T W J(x) for finite-dimensional case."""
        J = self.coherence_energy.residual_map.jacobian(x)
        W = self.coherence_energy.weight.matrix
        # G = J^T W J
        return J.T @ W @ J
    
    def compute_pseudo_inverse(self, x: NDArray, reg: float = 1e-10) -> NDArray:
        """Compute G(x)^dagger for gradient computation."""
        G = self.compute(x)
        # Regularized pseudo-inverse
        return np.linalg.pinv(G, rcond=reg)


# =============================================================================
# Section 6: Coordinate-Stable Curvature
# =============================================================================

class CurvatureComputer:
    """
    Coordinate-stable curvature definition using baseline metric G₀.
    
    κ(x) = log(1 + λ_max(G̃(x)))
    where G̃(x) = G₀^{-1/2} G(x) G₀^{-1/2}
    
    Properties:
    - Invariant under linear coordinate reparameterization
    - κ(x) ≥ 0
    """
    
    def __init__(self, induced_metric: InducedMetric, G0: NDArray):
        self.induced_metric = induced_metric
        self.G0 = G0
        self._G0_inv_sqrt = self._matrix_sqrt_inv(G0)
    
    def _matrix_sqrt_inv(self, M: NDArray) -> NDArray:
        """Compute M^{-1/2} using eigendecomposition."""
        eigvals, eigvecs = np.linalg.eigh(M)
        # Ensure positive eigenvalues
        eigvals = np.maximum(eigvals, 1e-12)
        return eigvecs @ np.diag(1.0 / np.sqrt(eigvals)) @ eigvecs.T
    
    def compute(self, x: NDArray) -> float:
        """Compute curvature scalar κ(x)."""
        G = self.induced_metric.compute(x)
        
        # G̃ = G₀^{-1/2} G G₀^{-1/2}
        G_tilde = self._G0_inv_sqrt @ G @ self._G0_inv_sqrt
        
        # λ_max(G̃)
        eigvals = np.linalg.eigvalsh(G_tilde)
        lambda_max = np.max(eigvals)
        
        # κ = log(1 + λ_max)
        return math.log(1.0 + lambda_max)
    
    def compute_all(self, x: NDArray) -> Dict[str, float]:
        """Compute curvature and related quantities."""
        G = self.induced_metric.compute(x)
        G_tilde = self._G0_inv_sqrt @ G @ self._G0_inv_sqrt
        eigvals = np.linalg.eigvalsh(G_tilde)
        
        return {
            'kappa': math.log(1.0 + np.max(eigvals)),
            'lambda_max': float(np.max(eigvals)),
            'lambda_min': float(np.min(eigvals)),
            'condition_number': float(np.max(eigvals) / max(np.min(eigvals), 1e-12))
        }


# =============================================================================
# Section 7: Step Operator Abstraction
# =============================================================================

@dataclass
class StepOperatorConfig:
    """Configuration for step operator."""
    p: int = 1  # Truncation order (p ≥ 1)
    Ct: float = 1.0  # Truncation error constant
    
    def truncation_error_bound(self, dt: float) -> float:
        """Bound: |error| ≤ C_t * dt^{p+1}"""
        return self.Ct * (dt ** (self.p + 1))


class StepOperator:
    """
    Abstract step operator: x_{n+1} = Step(x_n, Δt_n, b_n)
    
    The actual step depends on:
    - Current state x_n
    - Time step Δt_n (from CTD)
    - Budget b_n (for perturbation control)
    """
    
    def __init__(
        self,
        config: StepOperatorConfig,
        ideal_step_fn: Callable[[NDArray, float], NDArray]
    ):
        self.config = config
        self.ideal_step_fn = ideal_step_fn
    
    def compute(
        self,
        x: NDArray,
        dt: float,
        budget: float,
        perturbation_fn: Optional[Callable[[float], NDArray]] = None
    ) -> Tuple[NDArray, float]:
        """
        Compute step with perturbation.
        
        Returns: (x_next, actual_error_estimate)
        """
        # Ideal step
        x_tilde = self.ideal_step_fn(x, dt)
        
        # Perturbation bound from budget
        truncation_bound = self.config.truncation_error_bound(dt)
        
        # Add perturbation if provided
        if perturbation_fn is not None:
            perturbation = perturbation_fn(budget)
            x_next = x_tilde + perturbation
        else:
            x_next = x_tilde
            perturbation = np.zeros_like(x)
        
        # Actual error estimate (truncation + perturbation)
        perturbation_norm = np.linalg.norm(perturbation)
        actual_error = truncation_bound + perturbation_norm
        
        return x_next, actual_error


# =============================================================================
# Section 8: Certified Perturbation Bounds
# =============================================================================

@dataclass
class CertifiedBounds:
    """
    Declared certified bounds for perturbation model.
    
    ε_x(b) ≤ C_x / b^γ
    ε_F(b) ≤ C_F / b^γ
    ε_Φ(b) ≤ C_Φ / b^γ
    """
    Cx: float  # C_x > 0
    gamma: float  # γ > 0
    Cf: float = 0.0  # For residual evaluation
    Cphi: float = 0.0  # For energy evaluation
    
    def perturbation_bound(self, budget: float) -> float:
        """ε_x(b) = C_x / b^γ"""
        if budget <= 0:
            return float('inf')
        return self.Cx / (budget ** self.gamma)
    
    def residual_bound(self, budget: float) -> float:
        """ε_F(b) = C_F / b^γ"""
        if budget <= 0:
            return float('inf')
        return self.Cf / (budget ** self.gamma)
    
    def energy_bound(self, budget: float) -> float:
        """ε_Φ(b) = C_Φ / b^γ"""
        if budget <= 0:
            return float('inf')
        return self.Cphi / (budget ** self.gamma)


def default_perturbation(budget: float, bounds: CertifiedBounds, dim: int) -> NDArray:
    """
    Default perturbation generator: uniform random within ε_x(b).
    In production, this would be replaced with actual numerical errors.
    """
    eps = bounds.perturbation_bound(budget)
    return np.random.uniform(-eps, eps, dim)


# =============================================================================
# Section 9: Debt Dynamics
# =============================================================================

@dataclass
class DebtState:
    """Debt state for tracking."""
    accumulated: float = 0.0
    instantaneous: float = 0.0
    
    def update(
        self,
        phi_curr: float,
        phi_next: float,
        curvature: float,
        curvature_weighted: bool = True
    ) -> 'DebtState':
        """
        Update debt dynamics.
        
        d_n = max(0, Φ_{n+1} - Φ_n) * (1 + κ(x_n))
        D_n = D_{n-1} + d_n
        """
        delta_phi = phi_next - phi_curr
        instantaneous = max(0.0, delta_phi)
        
        if curvature_weighted:
            instantaneous *= (1.0 + curvature)
        
        return DebtState(
            accumulated=self.accumulated + instantaneous,
            instantaneous=instantaneous
        )
    
    def is_admissible(self, d_max: float) -> bool:
        """Check admissibility condition: D_N ≤ D_max"""
        return self.accumulated <= d_max


# =============================================================================
# Section 10: Budget Law (Curvature Tax)
# =============================================================================

@dataclass
class BudgetLaw:
    """
    Budget law: b_n ≥ b_min + η * κ(x_n)
    
    Higher curvature requires larger computational expenditure.
    """
    b_min: float  # b_min > 0
    eta: float  # η > 0
    
    def compute_budget(self, curvature: float) -> float:
        """Compute minimum required budget."""
        return self.b_min + self.eta * curvature
    
    def verify(self, budget: float, curvature: float) -> bool:
        """Verify budget satisfies law."""
        return budget >= self.compute_budget(curvature)


# =============================================================================
# Section 11: CTD Time Reparameterization
# =============================================================================

@dataclass
class CTDConfig:
    """CTD (Curvature-Time Dilation) configuration."""
    delta_tau: float  # Fixed internal step
    mu: float  # μ > 0
    
    def compute_timestep(self, curvature: float) -> float:
        """
        Δt_n = Δτ / (1 + μ * κ(x_n))
        
        High curvature → smaller real-time step
        Low curvature → larger real-time step
        """
        return self.delta_tau / (1.0 + self.mu * curvature)


# =============================================================================
# Section 12: Stability Verification
# =============================================================================

@dataclass
class StabilityConfig:
    """Configuration for stability verification."""
    delta: float  # Step decay coefficient
    K1: float  # Truncation error coefficient
    K2: float  # Perturbation error coefficient
    lambda_min: float  # λ_min > 0 for G
    lambda_max: float  # λ_max bound for G


def verify_stability(
    phi_curr: float,
    phi_next: float,
    gradient_norm_sq: float,  # |∇Φ|^2_{G^{-1}}
    dt: float,
    perturbation: float,
    curvature: float,
    config: StabilityConfig
) -> Dict[str, Any]:
    """
    Verify stability condition from Section 12.
    
    Condition:
    K_1 * dt^{p+1} + K_2 * ε_x(b)^2 ≤ (δ/2) * |∇Φ|^2_{G^{-1}}
    
    If satisfied, energy is non-increasing.
    """
    # Compute error terms
    truncation_term = config.K1 * (dt ** 2)  # Assuming p=1
    perturbation_term = config.K2 * (perturbation ** 2)
    error_sum = truncation_term + perturbation_term
    
    # Right-hand side threshold
    rhs_threshold = (config.delta / 2.0) * gradient_norm_sq
    
    # Stability condition
    is_stable = error_sum <= rhs_threshold
    
    # Energy decrement
    energy_decrement = phi_curr - phi_next
    
    return {
        'is_stable': is_stable,
        'truncation_term': truncation_term,
        'perturbation_term': perturbation_term,
        'error_sum': error_sum,
        'rhs_threshold': rhs_threshold,
        'energy_decrement': energy_decrement,
        'phi_curr': phi_curr,
        'phi_next': phi_next
    }


# =============================================================================
# Full Kernel Interface
# =============================================================================

@dataclass
class CoherenceKernelV11:
    """
    Complete Coherence Kernel v1.1 implementation.
    
    Interface summary (Section 14):
    - Module supplies: X, Y, F, W, G₀, ε_x, ε_F, constants
    - Kernel supplies: Φ, G, κ, budget rule, debt rule, CTD rule
    """
    
    # Module-supplied (interface)
    hilbert_space: HilbertSpace
    residual_space: ResidualSpace
    residual_map: ResidualMap
    weight: WeightOperator
    G0: NDArray  # Baseline metric
    certified_bounds: CertifiedBounds
    
    # Kernel-supplied (computed)
    coherence_energy: CoherenceEnergy = field(init=False)
    induced_metric: InducedMetric = field(init=False)
    curvature_computer: CurvatureComputer = field(init=False)
    
    # Configuration
    b_min: float = 1.0
    eta: float = 1.0
    mu: float = 1.0
    delta_tau: float = 0.1
    d_max: float = 100.0
    
    def __post_init__(self):
        """Initialize kernel-supplied components."""
        self.coherence_energy = CoherenceEnergy(
            residual_map=self.residual_map,
            weight=self.weight,
            residual_space=self.residual_space
        )
        self.induced_metric = InducedMetric(
            coherence_energy=self.coherence_energy,
            hilbert_space=self.hilbert_space
        )
        self.curvature_computer = CurvatureComputer(
            induced_metric=self.induced_metric,
            G0=self.G0
        )
    
    def compute_all(self, x: NDArray) -> Dict[str, float]:
        """Compute all kernel quantities for state x."""
        phi = self.coherence_energy(x)
        G = self.induced_metric.compute(x)
        kappa = self.curvature_computer.compute(x)
        
        # Gradient (using pseudo-inverse)
        J = self.residual_map.jacobian(x)
        Fx = self.residual_map(x)
        G_pinv = self.induced_metric.compute_pseudo_inverse(x)
        gradient = J.T @ self.weight.apply(Fx)
        gradient_norm_sq = float(gradient @ G_pinv @ gradient)
        
        return {
            'phi': phi,
            'kappa': kappa,
            'gradient_norm_sq': gradient_norm_sq,
            'lambda_max_G': float(np.max(np.linalg.eigvalsh(G))),
            'lambda_min_G': float(np.min(np.linalg.eigvalsh(G)))
        }
    
    def budget_law(self, curvature: float) -> float:
        """Compute required budget: b_n = b_min + η * κ(x_n)"""
        return self.b_min + self.eta * curvature
    
    def ctd_timestep(self, curvature: float) -> float:
        """Compute CTD time step: Δt_n = Δτ / (1 + μ * κ(x_n))"""
        return self.delta_tau / (1.0 + self.mu * curvature)
    
    def step(
        self,
        x: NDArray,
        ideal_step_fn: Callable[[NDArray, float], NDArray],
        budget: Optional[float] = None,
        use_perturbation: bool = False
    ) -> Tuple[NDArray, Dict[str, Any]]:
        """
        Execute one kernel step.
        
        Returns: (x_next, step_info)
        """
        # Compute kernel quantities
        kernel_state = self.compute_all(x)
        kappa = kernel_state['kappa']
        
        # Compute budget (if not provided)
        if budget is None:
            budget = self.budget_law(kappa)
        
        # Compute CTD time step
        dt = self.ctd_timestep(kappa)
        
        # Execute step
        step_op = StepOperator(
            config=StepOperatorConfig(),
            ideal_step_fn=ideal_step_fn
        )
        
        # Perturbation function
        pert_fn = None
        if use_perturbation:
            dim = self.hilbert_space.dimension
            pert_fn = lambda b: default_perturbation(b, self.certified_bounds, dim)
        
        x_next, actual_error = step_op.compute(x, dt, budget, pert_fn)
        
        # Compute new kernel state
        kernel_state_next = self.compute_all(x_next)
        
        # Update debt
        debt_state = DebtState()
        new_debt = debt_state.update(
            phi_curr=kernel_state['phi'],
            phi_next=kernel_state_next['kappa'],
            curvature=kappa,
            curvature_weighted=True
        )
        
        return x_next, {
            'phi': kernel_state['phi'],
            'phi_next': kernel_state_next['phi'],
            'kappa': kappa,
            'budget': budget,
            'dt': dt,
            'perturbation_error': actual_error,
            'debt_accumulated': new_debt.accumulated,
            'is_admissible': new_debt.is_admissible(self.d_max)
        }


# =============================================================================
# Receipt Generation (v1.1 Extended)
# =============================================================================

@dataclass
class CK0ReceiptV11:
    """Extended receipt for v1.1 with curvature-aware fields."""
    step_id: int
    rule_id: str
    input_hash: str
    output_hash: str
    
    # v1.0 fields
    V_k: float
    V_k1: float
    dV_k: float
    B_k: float
    D_k: float
    D_k1: float
    
    # v1.1 fields
    kappa: float
    phi: float
    phi_next: float
    dt: float
    perturbation_bound: float
    
    # Chain
    prev_receipt_hash: str
    receipt_hash: str
    
    # Status
    status: str
    error_code: str
    error_detail: Optional[str]
    
    spec_version: str = "1.1"
    schema_version: str = "1.1"


# =============================================================================
# Utility Functions
# =============================================================================

def canonical_json(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def hash_obj(obj: Any) -> str:
    return sha256_hex(canonical_json(obj))


# =============================================================================
# Example Usage
# =============================================================================

def create_example_kernel():
    """Create an example kernel for testing."""
    dimension = 3
    
    # Hilbert space X = R^3
    hilbert_space = FiniteDimensionalHilbertSpace(dimension)
    
    # Residual space Y = R^2
    residual_space = ResidualSpace(
        dimension=2,
        inner_product_matrix=np.eye(2)
    )
    
    # Residual map F(x) = [x₁² + x₂ - 1, x₁x₂ + x₃ - 1]
    def residual_fn(x: NDArray) -> NDArray:
        return np.array([
            x[0]**2 + x[1] - 1.0,
            x[0] * x[1] + x[2] - 1.0
        ])
    
    # Jacobian J(x) = [[2x₁, 1, 0], [x₂, x₁, 1]]
    def jacobian_fn(x: NDArray) -> NDArray:
        return np.array([
            [2.0 * x[0], 1.0, 0.0],
            [x[1], x[0], 1.0]
        ])
    
    residual_map = ResidualMap(residual_fn, jacobian_fn)
    
    # Weight operator W = I
    weight = WeightOperator.constant(2, 1.0)
    
    # Baseline metric G₀ = I
    G0 = np.eye(dimension)
    
    # Certified bounds
    certified_bounds = CertifiedBounds(
        Cx=1.0,
        gamma=1.0,
        Cf=0.5,
        Cphi=0.25
    )
    
    # Create kernel
    kernel = CoherenceKernelV11(
        hilbert_space=hilbert_space,
        residual_space=residual_space,
        residual_map=residual_map,
        weight=weight,
        G0=G0,
        certified_bounds=certified_bounds,
        b_min=1.0,
        eta=1.0,
        mu=1.0,
        delta_tau=0.1,
        d_max=10.0
    )
    
    return kernel


if __name__ == "__main__":
    # Example usage
    kernel = create_example_kernel()
    
    # Initial state
    x = np.array([0.5, 0.5, 0.5])
    
    # Compute kernel quantities
    state = kernel.compute_all(x)
    print("Kernel state at x =", x)
    print(f"  Φ(x) = {state['phi']:.6f}")
    print(f"  κ(x) = {state['kappa']:.6f}")
    print(f"  |∇Φ|² = {state['gradient_norm_sq']:.6f}")
    
    # Budget and CTD
    budget = kernel.budget_law(state['kappa'])
    dt = kernel.ctd_timestep(state['kappa'])
    print(f"\nBudget law: b = {budget:.6f}")
    print(f"CTD timestep: Δt = {dt:.6f}")
    
    # Simple gradient descent step
    def ideal_step(x: NDArray, dt: float) -> NDArray:
        J = kernel.residual_map.jacobian(x)
        Fx = kernel.residual_map(x)
        grad = J.T @ kernel.weight.apply(Fx)
        return x - dt * grad
    
    # Execute step
    x_next, info = kernel.step(x, ideal_step, use_perturbation=False)
    print(f"\nStep result:")
    print(f"  x_next = {x_next}")
    print(f"  Φ(x_next) = {info['phi_next']:.6f}")
    print(f"  Debt accumulated = {info['debt_accumulated']:.6f}")
    print(f"  Admissible = {info['is_admissible']}")
