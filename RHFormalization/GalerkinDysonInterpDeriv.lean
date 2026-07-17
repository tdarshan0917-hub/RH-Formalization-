import RHFormalization.GalerkinDysonInterp
import Mathlib

set_option autoImplicit false
namespace RHFormalization
noncomputable section
open Matrix
attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
variable {N : ℕ}

/-- Free factor's u-derivative: `d/du exp((t-u)•(-K)) = exp((t-u)•(-K)) * K`.
Chain rule: inner (t-u) has derivative -1, cancels the -K to +K. -/
theorem hasDerivAt_dysonInterp_freeFactor
    (L : ℝ) (t u : ℝ) :
    HasDerivAt (fun v : ℝ => NormedSpace.exp ((t - v) • (-(galerkinK (N := N) L))))
      (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L))) * (galerkinK (N := N) L)) u := by
  -- g(w) = exp(w • (-K)), inner f(v) = t - v.  (g ∘ f)'(u) = g'(f u) * f'(u).
  have hg := hasDerivAt_galerkinFreeHeat (N := N) L (t - u)
  have hf : HasDerivAt (fun v : ℝ => t - v) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub t
  -- comp: (hg.comp u hf) : HasDerivAt (g ∘ f) (g'(f u) • f') u  — but for ℝ→ℝ scalar it's mul
  have hcomp := HasDerivAt.scomp u hg hf
  -- hcomp value: (exp((t-u)•(-K)) * (-K)) • (-1) ; simplify smul by -1 and neg
  simpa [neg_one_smul, mul_neg, neg_neg] using hcomp

#print axioms hasDerivAt_dysonInterp_freeFactor

end
end RHFormalization
