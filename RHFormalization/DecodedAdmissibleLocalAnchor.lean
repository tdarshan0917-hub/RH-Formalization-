import RHFormalization.PrimePotentialDecodedCenter
import RHFormalization.AppendixDActiveSpikeCodesFromCenterCutoff
import RHFormalization.AnchorFiniteGeneral
import Mathlib

/-!
# DecodedAdmissibleLocalAnchor — the exact D.ADM objects at the live stage

`decodedAdmissibleLocalMajorant δ R` = V_R^# : physical-center bump sum over
the active codes at cutoff R with the frozen arithmetic weights.
`decodedAdmissibleLocalAnchor δ R c` = M(R) at coupling c = C*·t0.

Main results (Lemma D.ADM-NET, stage half):
- anchor integrand integrable at EVERY coupling and EVERY finite R;
- anchor value nonnegative;
- window inequality M(R)/(2·max(L0, M(R))) ≤ 1 — the manuscript's
  "fix R, then choose L" step, schedule-preserving (L0 ≤ chosen L).

The elementary bump/weight facts enter as hypotheses here and are
discharged in the companion file from the literal `gaussBump`/`ppWeightReal`
definitions.
-/

set_option autoImplicit false

namespace RHFormalization

open Real MeasureTheory

/-- The exact decoded local majorant `V_R^#` at cutoff `R`. -/
noncomputable def decodedAdmissibleLocalMajorant (δ R : ℝ) (x : ℝ) : ℝ :=
  decodedPrimePotentialFn δ (activePrimePowerCodesCenterBelow R) ppWeightReal x

/-- Total active weight mass — the trivial sup bound for `V_R^#`. -/
noncomputable def decodedAdmissibleLocalMajorantBound (R : ℝ) : ℝ :=
  ∑ k ∈ activePrimePowerCodesCenterBelow R, ppWeightReal k

theorem decodedAdmissibleLocalMajorant_nonneg
    (δ R : ℝ)
    (hbump_nonneg : ∀ y, 0 ≤ gaussBump δ y)
    (hw : ∀ k, 0 ≤ ppWeightReal k) :
    ∀ x, 0 ≤ decodedAdmissibleLocalMajorant δ R x := by
  intro x
  unfold decodedAdmissibleLocalMajorant decodedPrimePotentialFn
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hw k) (hbump_nonneg _)

theorem decodedAdmissibleLocalMajorant_le_bound
    (δ R : ℝ)
    (hbump_le_one : ∀ y, gaussBump δ y ≤ 1)
    (hw : ∀ k, 0 ≤ ppWeightReal k) :
    ∀ x, decodedAdmissibleLocalMajorant δ R x
      ≤ decodedAdmissibleLocalMajorantBound R := by
  intro x
  unfold decodedAdmissibleLocalMajorant decodedPrimePotentialFn
    decodedAdmissibleLocalMajorantBound
  apply Finset.sum_le_sum
  intro k _
  exact (mul_le_mul_of_nonneg_left (hbump_le_one _) (hw k)).trans
    (le_of_eq (mul_one _))

theorem decodedAdmissibleLocalMajorant_measurable
    (δ R : ℝ)
    (hbump_meas : Measurable (gaussBump δ)) :
    Measurable (decodedAdmissibleLocalMajorant δ R) := by
  unfold decodedAdmissibleLocalMajorant decodedPrimePotentialFn
  apply Finset.measurable_sum
  intro k _
  exact (hbump_meas.comp (measurable_id.sub measurable_const)).const_mul _

theorem decodedAdmissibleLocalMajorant_integrable
    (δ R : ℝ)
    (hbump_int : Integrable (gaussBump δ) volume) :
    Integrable (decodedAdmissibleLocalMajorant δ R) volume := by
  unfold decodedAdmissibleLocalMajorant decodedPrimePotentialFn
  apply integrable_finset_sum
  intro k _
  exact (hbump_int.comp_sub_right _).const_mul _

/-- **M(R) integrand is integrable at every coupling and every finite R.**
This is step 1 of Lemma D.ADM-NET: `M(R) < ∞`, with NO smallness condition
on `c = C*·t0` — the fixed-coupling requirement the old `c*B ≤ 1` theorem
could not meet. -/
theorem decodedLocalAnchor_integrand_integrable
    (δ R c : ℝ) (hc : 0 ≤ c)
    (hbump_nonneg : ∀ y, 0 ≤ gaussBump δ y)
    (hbump_le_one : ∀ y, gaussBump δ y ≤ 1)
    (hbump_meas : Measurable (gaussBump δ))
    (hbump_int : Integrable (gaussBump δ) volume)
    (hw : ∀ k, 0 ≤ ppWeightReal k) :
    Integrable
      (fun u => Real.exp (c * decodedAdmissibleLocalMajorant δ R u)
        - 1 - c * decodedAdmissibleLocalMajorant δ R u) volume :=
  anchor_integrand_integrable_general
    (decodedAdmissibleLocalMajorant δ R) c
    (decodedAdmissibleLocalMajorantBound R) hc
    (decodedAdmissibleLocalMajorant_nonneg δ R hbump_nonneg hw)
    (decodedAdmissibleLocalMajorant_le_bound δ R hbump_le_one hw)
    (decodedAdmissibleLocalMajorant_measurable δ R hbump_meas)
    (decodedAdmissibleLocalMajorant_integrable δ R hbump_int)

/-- The exact stage anchor `M(R)` at coupling `c`. -/
noncomputable def decodedAdmissibleLocalAnchor (δ R c : ℝ) : ℝ :=
  ∫ u, (Real.exp (c * decodedAdmissibleLocalMajorant δ R u)
    - 1 - c * decodedAdmissibleLocalMajorant δ R u)

theorem decodedAdmissibleLocalAnchor_nonneg
    (δ R c : ℝ) (hc : 0 ≤ c)
    (hbump_nonneg : ∀ y, 0 ≤ gaussBump δ y)
    (hw : ∀ k, 0 ≤ ppWeightReal k) :
    0 ≤ decodedAdmissibleLocalAnchor δ R c := by
  unfold decodedAdmissibleLocalAnchor
  exact anchor_value_nonneg (decodedAdmissibleLocalMajorant δ R) c hc
    (decodedAdmissibleLocalMajorant_nonneg δ R hbump_nonneg hw)

/-- **Step 2 of Lemma D.ADM-NET (window choice), at the stage.**
Choosing `L := max L0 (M(R))` gives `M(R)/(2L) ≤ 1` while `L0 ≤ L`, so
every banked lower bound on the window survives the adaptive re-tuning. -/
theorem decodedAdmissibleLocalAnchor_window_bound
    (δ R c L0 : ℝ) (hc : 0 ≤ c) (hL0 : 1 ≤ L0)
    (hbump_nonneg : ∀ y, 0 ≤ gaussBump δ y)
    (hw : ∀ k, 0 ≤ ppWeightReal k) :
    decodedAdmissibleLocalAnchor δ R c
      / (2 * max L0 (decodedAdmissibleLocalAnchor δ R c)) ≤ 1 :=
  adaptive_window_bound _ _
    (decodedAdmissibleLocalAnchor_nonneg δ R c hc hbump_nonneg hw) hL0

#print axioms decodedLocalAnchor_integrand_integrable
#print axioms decodedAdmissibleLocalAnchor_nonneg
#print axioms decodedAdmissibleLocalAnchor_window_bound

end RHFormalization
