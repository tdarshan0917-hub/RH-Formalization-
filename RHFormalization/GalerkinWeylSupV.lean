/-
GalerkinWeylSupV.lean

WEYL AT THE SUP-ANCHOR: the genuine galerkin spectrum stays within
SupVConst of the free Dirichlet spectrum, index by index -- via the banked
form-level Weyl inequality (MinMaxBrick10) fed by the banked uniform
complex form bound. Sharper than the growthDrop route: no operator norm.

This is the per-index spectral control for Front F (D.R->infty tails and
the N-limit both consume it).
-/
import RHFormalization.PerturbedEigenvalueWeyl
import RHFormalization.GalerkinUniformShift

namespace RHFormalization

noncomputable section

open Complex

variable {N : ℕ}

/-- Form distance between the genuine galerkin perturbed operator and the
free diagonal is at most SupVConst, pointwise. -/
theorem galerkinOp_formDist_supV (μ : Fin N → ℝ) (qs : Finset ℕ)
    (x : EuclideanSpace ℂ (Fin N)) :
    |RCLike.re (inner ℂ x
        (perturbedOp μ (galerkinVC (N := N) 1 qs ppWeightReal 1) x))
      - RCLike.re (inner ℂ x (freeDiagOp μ x))|
      ≤ SupVConst * ‖x‖ ^ 2 := by
  have happ : perturbedOp μ (galerkinVC (N := N) 1 qs ppWeightReal 1) x
      = freeDiagOp μ x + pertOp (galerkinVC (N := N) 1 qs ppWeightReal 1) x := by
    rw [perturbedOp_eq_add]
    first
      | rfl
      | exact LinearMap.add_apply _ _ _
  rw [happ, inner_add_right, _root_.map_add]
  have hcancel :
      RCLike.re (inner ℂ x (freeDiagOp μ x))
        + RCLike.re (inner ℂ x
            (pertOp (galerkinVC (N := N) 1 qs ppWeightReal 1) x))
        - RCLike.re (inner ℂ x (freeDiagOp μ x))
      = RCLike.re (inner ℂ x
          (pertOp (galerkinVC (N := N) 1 qs ppWeightReal 1) x)) := by
    ring
  rw [hcancel]
  exact galerkinVC_re_form_bound qs x

/-- **WEYL AT SupVConst.** Every genuine galerkin eigenvalue is within
SupVConst of the corresponding free Dirichlet eigenvalue. -/
theorem galerkinEigenvalues_dist_free_le (μ : Fin N → ℝ) (qs : Finset ℕ)
    (k : Fin N) :
    |perturbedEigenvalues μ
        (galerkinVC_isHermitian (N := N) 1 qs ppWeightReal 1) k
      - freeEigenvalues μ k| ≤ SupVConst :=
  eigenvalues_dist_le
    (perturbedOp_isSymmetric μ (galerkinVC_isHermitian (N := N) 1 qs ppWeightReal 1))
    (freeDiagOp_isSymmetric μ)
    perturbedOp_finrank
    SupVConst
    (galerkinOp_formDist_supV μ qs)
    k

/-- Lower half: each genuine eigenvalue dominates its free partner minus
SupVConst -- the per-index growth transfer for tail summability. -/
theorem galerkinEigenvalue_ge_free_sub (μ : Fin N → ℝ) (qs : Finset ℕ)
    (k : Fin N) :
    freeEigenvalues μ k - SupVConst
      ≤ perturbedEigenvalues μ
          (galerkinVC_isHermitian (N := N) 1 qs ppWeightReal 1) k := by
  have h := abs_le.mp (galerkinEigenvalues_dist_free_le μ qs k)
  linarith [h.1]

#print axioms galerkinOp_formDist_supV
#print axioms galerkinEigenvalues_dist_free_le
#print axioms galerkinEigenvalue_ge_free_sub

end

end RHFormalization
