import RHFormalization.MinMaxBrick7

namespace RHFormalization
noncomputable section
open RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {n : ℕ} {B : E →ₗ[𝕜] E}

/-- The operator `B` shifted by a real scalar `c`: `B + c·I`. -/
def shiftOp (B : E →ₗ[𝕜] E) (c : ℝ) : E →ₗ[𝕜] E := B + (c:𝕜) • (LinearMap.id : E →ₗ[𝕜] E)

theorem shiftOp_apply (c : ℝ) (x : E) : shiftOp B c x = B x + (c:𝕜) • x := by
  rw [shiftOp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]

theorem shiftOp_symm (hB : B.IsSymmetric) (c : ℝ) : (shiftOp B c).IsSymmetric := by
  intro x y
  rw [shiftOp_apply, shiftOp_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, hB x y, RCLike.conj_ofReal]

theorem shiftOp_rayleigh (c : ℝ) (x : E) :
    RCLike.re (inner 𝕜 x (shiftOp B c x))
      = RCLike.re (inner 𝕜 x (B x)) + c * ‖x‖^2 := by
  rw [shiftOp_apply, inner_add_right, inner_smul_right, map_add, RCLike.re_ofReal_mul,
    inner_self_eq_norm_sq]

/-- `shiftOp B c` has eigenvector `e_i` with eigenvalue `λ_i + c`. -/
theorem shiftOp_apply_eigenvectorBasis (hB : B.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (c : ℝ) (i : Fin n) :
    shiftOp B c (hB.eigenvectorBasis hn i)
      = ((hB.eigenvalues hn i + c : ℝ) : 𝕜) • hB.eigenvectorBasis hn i := by
  rw [shiftOp_apply, hB.apply_eigenvectorBasis hn i, RCLike.ofReal_add, add_smul]

#print axioms shiftOp_apply
#print axioms shiftOp_symm
#print axioms shiftOp_rayleigh
#print axioms shiftOp_apply_eigenvectorBasis
end
end RHFormalization
