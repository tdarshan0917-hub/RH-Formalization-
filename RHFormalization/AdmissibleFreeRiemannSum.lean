import RHFormalization.AdmissibleGalerkinStage
import RHFormalization.AdmissibleEigenvalueFloor
import RHFormalization.GalerkinFConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# RHFormalization.AdmissibleFreeRiemannSum

**Front F-adm, brick 1a (Route A′).** The free part of the admissible FH-limit,
DEFINED AS THE IMPROPER INTEGRAL itself:

  `FHadmFree s = (1/2π) ∫_{u>0} (s + SupVConst + u²)⁻¹ du`.

The closed form `1/(4√(s+SupVConst))` is a deferred manuscript-comparison
island; `DFHLimitData` is agnostic to the formula (needs only holomorphy +
compact ε–N convergence), and the overlap identity runs through the B side.

This file: the free stage sum, the integrand, denominator nonvanishing on Ω,
and integrability on `Ioi 0` — making `FHadmFree` well-defined pointwise on Ω.
No Riemann-sum estimate yet (bricks 1c/1d).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory

/-- **The admissible free stage**: density-normalized free Dirichlet resolvent
sum — the free-spectrum comparison object for the package F-slot at the
admissible stage (same shift `s + SupVConst`, reassociated). -/
def admissibleFreeStage (n : ℕ) (s : ℂ) : ℂ :=
  admDensityC n *
    ∑ i : Fin (admN n),
      (s + ((SupVConst + galerkinFreeMu (admN n) (admL n) i : ℝ) : ℂ))⁻¹

/-- The free continuum integrand `(s + SupVConst + u²)⁻¹`, fused real cast so
the banked compact-δ engine applies with `lam := SupVConst + u²`. -/
def freeResolventIntegrand (s : ℂ) (u : ℝ) : ℂ :=
  (s + ((SupVConst + u ^ 2 : ℝ) : ℂ))⁻¹

/-- Denominator nonvanishing on Ω: nonneg real shifts cannot reach the cut. -/
theorem freeResolvent_denom_ne_zero {s : ℂ} (hs : s ∈ Ω) (u : ℝ) :
    s + ((SupVConst + u ^ 2 : ℝ) : ℂ) ≠ 0 := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_uniform_lower_bound_on_compact {s}
    isCompact_singleton (Set.singleton_subset_iff.mpr hs)
  have hlam : (0:ℝ) ≤ SupVConst + u ^ 2 :=
    add_nonneg SupVConst_nonneg_adm (sq_nonneg u)
  intro h0
  have h := hδ s (Set.mem_singleton s) (SupVConst + u ^ 2) hlam
  rw [h0, norm_zero] at h
  linarith

/-- **Integrability of the free integrand on `Ioi 0`** for each `s ∈ Ω`, by
comparison with `C·(1+u²)⁻¹` via the banked uniform term bound. Makes
`FHadmFree` well-defined pointwise on Ω. -/
theorem freeResolventIntegrand_integrableOn {s : ℂ} (hs : s ∈ Ω) :
    IntegrableOn (freeResolventIntegrand s) (Set.Ioi (0:ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := inv_norm_le_on_compact {s}
    isCompact_singleton (Set.singleton_subset_iff.mpr hs)
  have hSupV : (0:ℝ) ≤ SupVConst := SupVConst_nonneg_adm
  have hden : Continuous (fun u : ℝ => s + ((SupVConst + u ^ 2 : ℝ) : ℂ)) := by
    have h1 : Continuous (fun u : ℝ => SupVConst + u ^ 2) :=
      continuous_const.add (continuous_pow 2)
    exact continuous_const.add (Complex.continuous_ofReal.comp h1)
  have hcont : ContinuousOn (freeResolventIntegrand s) (Set.Ioi (0:ℝ)) := by
    unfold freeResolventIntegrand
    exact hden.continuousOn.inv₀ (fun u _ => freeResolvent_denom_ne_zero hs u)
  refine Integrable.mono'
    ((integrable_inv_one_add_sq.integrableOn).const_mul C)
    (hcont.aestronglyMeasurable measurableSet_Ioi)
    (ae_of_all _ fun u => ?_)
  show ‖(s + ((SupVConst + u ^ 2 : ℝ) : ℂ))⁻¹‖ ≤ C * ((1:ℝ) + u ^ 2)⁻¹
  have hlam : (0:ℝ) ≤ SupVConst + u ^ 2 := add_nonneg hSupV (sq_nonneg u)
  have h1 := hC s (Set.mem_singleton s) (SupVConst + u ^ 2) hlam
  have hb : (0:ℝ) < 1 + u ^ 2 := by positivity
  have hle : (1:ℝ) + u ^ 2 ≤ 1 + (SupVConst + u ^ 2) := by linarith
  have h2 : ((1:ℝ) + (SupVConst + u ^ 2))⁻¹ ≤ ((1:ℝ) + u ^ 2)⁻¹ := by
    first
      | gcongr
      | exact inv_le_inv_of_le hb hle
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hCpos.le)

/-- **The free part of the admissible FH-limit** (Route A′): the improper
integral itself. Closed form deferred; consumed by nothing on the live route. -/
def FHadmFree (s : ℂ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ u in Set.Ioi (0:ℝ), freeResolventIntegrand s u

#print axioms freeResolvent_denom_ne_zero
#print axioms freeResolventIntegrand_integrableOn

end

end RHFormalization
