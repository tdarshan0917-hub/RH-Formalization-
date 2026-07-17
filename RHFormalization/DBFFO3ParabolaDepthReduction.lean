import RHFormalization.DBFFStarOffParabolaBound
import RHFormalization.DBFFO2ShortResidualAssembly

/-!
# DBFFO3ParabolaDepthReduction

ROUTE CARD
1. Target: isolate the only remaining O3 / hstar case.
2. Object: `starObject`, the discrete Stieltjes error from `DBFFStarObject`.
3. Raw B on Ω? NO.
4. R = F − raw B forced? NO.
5. True outright: off-parabola hstar is banked; remaining case is exactly
   parabola-depth.
6. Manuscript: D.OP-BOUND / D.TAIL-DENSITY / D.UNIFORM-CAN.
7. Consumer: corrected-bulk/D.OP-BOUND assembly.

This file does not prove the remaining parabola-depth estimate. It proves that
the global hstar obligation is reduced to that one case.

Off-parabola:
  Re sqrt(s+1/4) ≥ 1/2 + δ uniformly on K
is already banked by `starObject_bounded_off_parabola`.

Remaining:
  no such δ exists for K, i.e. K reaches parabola depth.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology BigOperators

/-- Full O3 hstar: compact-uniform boundedness of the discrete Stieltjes error. -/
def DBFFO3Hstar : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    ∃ Cstar : ℝ,
      ∀ n : ℕ, ∀ s ∈ K, ‖starObject n s‖ ≤ Cstar

/-- The remaining parabola-depth O3 obligation. -/
def DBFFO3ParabolaDepthHstar : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    (∀ δ : ℝ, 0 < δ →
      ¬ (∀ s ∈ K,
        (1 / 2 : ℝ) + δ ≤ (Complex.sqrt (s + (1/4 : ℂ))).re)) →
    ∃ Cstar : ℝ,
      ∀ n : ℕ, ∀ s ∈ K, ‖starObject n s‖ ≤ Cstar

/--
Off-parabola hstar is already banked.

This is just the exported form of `starObject_bounded_off_parabola`.
-/
theorem DBFFO3Hstar_off_parabola
    (K : Set ℂ) (hKO : K ⊆ Ω)
    {δ : ℝ} (hδ : 0 < δ)
    (hoff : ∀ s ∈ K,
      (1 / 2 : ℝ) + δ ≤ (Complex.sqrt (s + (1/4 : ℂ))).re) :
    ∃ Cstar : ℝ,
      ∀ n : ℕ, ∀ s ∈ K, ‖starObject n s‖ ≤ Cstar :=
  starObject_bounded_off_parabola K hKO (δ := δ) hδ hoff

/--
Global hstar follows from the remaining parabola-depth hstar.

This is the precise reduction: every compact is either off-parabola, already
solved, or it is a parabola-depth compact, the true remaining O3 case.
-/
theorem DBFFO3Hstar_from_parabola_depth
    (Hpar : DBFFO3ParabolaDepthHstar) :
    DBFFO3Hstar := by
  intro K hK hKO
  classical
  by_cases hOff :
      ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ K,
          (1 / 2 : ℝ) + δ ≤ (Complex.sqrt (s + (1/4 : ℂ))).re
  · obtain ⟨δ, hδ, hoff⟩ := hOff
    exact DBFFO3Hstar_off_parabola K hKO (δ := δ) hδ hoff
  · refine Hpar K hK hKO ?_
    intro δ hδ hoff
    exact hOff ⟨δ, hδ, hoff⟩

/--
O3 hstar gives the compensated B-side compact bound, provided the already-banked
kernel prefactor bound is supplied.
-/
theorem DBFFO3_compensated_B_bounded_of_hstar
    (H : DBFFO3Hstar)
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω)
    (c : ℝ) (hc : 0 < c)
    (hker : ∀ s ∈ K,
      ‖(1 : ℂ) / (2 * Complex.sqrt (s + (1/4 : ℂ)))‖ ≤ c⁻¹) :
    ∃ C : ℝ,
      ∀ n : ℕ, ∀ s ∈ K,
        ‖galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
            - compensatorM n s‖ ≤ C := by
  obtain ⟨Cstar, hstar⟩ := H K hK hKO
  refine ⟨c⁻¹ * Cstar, ?_⟩
  exact
    compensated_B_bounded_of_starObject_bounded
      K hKO c hc hker Cstar hstar

/--
Parabola-depth hstar gives the compensated B-side compact bound.
This is the form the remaining D.TAIL-DENSITY / D.UNIFORM-CAN proof will feed.
-/
theorem DBFFO3_compensated_B_bounded_from_parabola_depth
    (Hpar : DBFFO3ParabolaDepthHstar)
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω)
    (c : ℝ) (hc : 0 < c)
    (hker : ∀ s ∈ K,
      ‖(1 : ℂ) / (2 * Complex.sqrt (s + (1/4 : ℂ)))‖ ≤ c⁻¹) :
    ∃ C : ℝ,
      ∀ n : ℕ, ∀ s ∈ K,
        ‖galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
            - compensatorM n s‖ ≤ C := by
  exact
    DBFFO3_compensated_B_bounded_of_hstar
      (DBFFO3Hstar_from_parabola_depth Hpar)
      K hK hKO c hc hker

#print axioms DBFFO3Hstar
#print axioms DBFFO3ParabolaDepthHstar
#print axioms DBFFO3Hstar_off_parabola
#print axioms DBFFO3Hstar_from_parabola_depth
#print axioms DBFFO3_compensated_B_bounded_of_hstar
#print axioms DBFFO3_compensated_B_bounded_from_parabola_depth

end

end RHFormalization
