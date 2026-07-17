import RHFormalization.PrimePotentialBumpSplit
import RHFormalization.DirichletEigenfunOrthogonal

/-!
# Brick 2, stone 3a: product-to-sum form of the single-bump matrix element
`B_{mn}(q) = ½·C_{m−n}(q) − ½·C_{m+n}(q)`, reducing the two-sine bump integral
to cosine-weighted Gaussian integrals. The `(m−n)` frequency carries the
off-diagonal decay (D.DISP displacement structure).
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Real MeasureTheory intervalIntegral
open scoped Real

/-- Cosine-weighted single-bump integral `C_j(q) = ∫₀ᴸ cos(jπx/L)·W(x−log q) dx`. -/
noncomputable def cosBumpIntegral (δ : ℝ) (q : ℕ) (L : ℝ) (j : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L, Real.cos (j * Real.pi * x / L) * gaussBump δ (x - Real.log q)

theorem continuous_cosBumpIntegrand (δ : ℝ) (q : ℕ) (L : ℝ) (j : ℝ) :
    Continuous (fun x : ℝ => Real.cos (j * Real.pi * x / L) * gaussBump δ (x - Real.log q)) := by
  unfold gaussBump
  fun_prop

/-- **Stone 3a**: `B_{mn}(q) = ½·C_{m−n}(q) − ½·C_{m+n}(q)`. -/
theorem bumpMatrixElement_eq_cos
    (δ : ℝ) (q : ℕ) (L : ℝ) (m n : ℕ) :
    bumpMatrixElement δ q L m n
      = (1/2) * cosBumpIntegral δ q L ((m : ℝ) - n)
        - (1/2) * cosBumpIntegral δ q L ((m : ℝ) + n) := by
  unfold bumpMatrixElement cosBumpIntegral
  have hpt : ∀ x : ℝ,
      dirichletEigenfun m L x * gaussBump δ (x - Real.log q) * dirichletEigenfun n L x
        = (1/2) * (Real.cos (((m : ℝ) - n) * Real.pi * x / L) * gaussBump δ (x - Real.log q))
          - (1/2) * (Real.cos (((m : ℝ) + n) * Real.pi * x / L) * gaussBump δ (x - Real.log q)) := by
    intro x
    have he := eigenfun_mul_eq m n L x
    rw [show dirichletEigenfun m L x * gaussBump δ (x - Real.log q) * dirichletEigenfun n L x
          = (dirichletEigenfun m L x * dirichletEigenfun n L x) * gaussBump δ (x - Real.log q) by ring,
        he]
    ring
  rw [intervalIntegral.integral_congr (fun x _ => hpt x)]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  · exact ((continuous_cosBumpIntegrand δ q L ((m:ℝ)-n)).intervalIntegrable 0 L).const_mul _
  · exact ((continuous_cosBumpIntegrand δ q L ((m:ℝ)+n)).intervalIntegrable 0 L).const_mul _

#print axioms bumpMatrixElement_eq_cos
end
end RHFormalization
