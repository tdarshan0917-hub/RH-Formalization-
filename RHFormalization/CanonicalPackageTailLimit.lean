import RHFormalization.CanonicalPackageTailConvergence
import RHFormalization.SummableSupportExhaustion
import RHFormalization.AdmissibleGalerkinStage
import RHFormalization.AdmissibleGalerkinEndpoint

/-!
# CanonicalPackageTailLimit — T1-final + T2: the tail row closes

ROUTE CARD
1. T1-final: the short packages over I_n = activePrimePowerPairsCenterBelow
   (admR n) converge on RHP(1) to the short tsum (exhaustion clone of the
   banked SlowCutoff proof, powered by shortPart_family_summable).
2. T2: canonicalPackageTail (I_n, t0) = B_stage − short (banked split), so
   the tail converges to Bcan-limit − short-tsum via Tendsto.sub against
   the banked admissible_hB.
3. Consumer: the core-Montel overlap identification.
4. Raw B on Ω? NO.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators Classical

/-- The short-part tsum limit. -/
def shortPackageLimit (t0 : ℝ) (s : ℂ) : ℂ :=
  ∑' q : PrimePowerPair, q.weightC * kernelShortPart q.center t0 s

/-- **T1-final: short packages converge along admR** on RHP(1). -/
theorem canonicalPackageShort_tendsto
    (t0 : ℝ) (ht0 : 0 < t0) (s : ℂ) (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        canonicalPackageShort (activePrimePowerPairsCenterBelow (admR n)) t0 s)
      Filter.atTop (𝓝 (shortPackageLimit t0 s)) := by
  have hsumm := shortPart_family_summable hs t0 ht0
  have hcover :
      ∀ q : PrimePowerPair,
        (q.weightC * kernelShortPart q.center t0 s) ≠ 0 →
        ∀ᶠ n : ℕ in atTop,
          q ∈ activePrimePowerPairsCenterBelow (admR n) := by
    intro q hqne
    have hvalid : IsPrimePowerPair q := by
      by_contra hbad
      apply hqne
      have hw0 : q.weightReal = 0 := by
        unfold PrimePowerPair.weightReal
        rw [if_neg hbad]
      have hwC0 : q.weightC = 0 := by
        unfold PrimePowerPair.weightC
        rw [hw0, Complex.ofReal_zero]
      rw [hwC0, zero_mul]
    have hev : ∀ᶠ n : ℕ in atTop, q.center ≤ admR n :=
      tendsto_admR_atTop.eventually_ge_atTop q.center
    filter_upwards [hev] with n hn
    exact (activePrimePowerPairsCenterBelow_mem (admR n) q).mpr ⟨hvalid, hn⟩
  have hconv := tendsto_sum_of_eventually_covers_support hsumm hcover
  unfold shortPackageLimit canonicalPackageShort
  first
    | exact hconv
    | simpa using hconv

/-- **T2: the tail limit on RHP(1)** — tail = B_stage − short, both converge. -/
theorem canonicalPackageTail_tendsto
    (t0 : ℝ) (ht0 : 0 < t0) (s : ℂ) (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        canonicalPackageTail (activePrimePowerPairsCenterBelow (admR n)) t0 s)
      Filter.atTop
      (𝓝 (galerkinBcanLimitData.Bcan s - shortPackageLimit t0 s)) := by
  have hsre : 0 < s.re := by
    have h1 : (1:ℝ) < s.re := hs
    linarith
  have hI : ∀ n : ℕ, ∀ q ∈ activePrimePowerPairsCenterBelow (admR n), 0 ≤ q.center :=
    fun n q _ => center_nonneg q
  have htail_eq : ∀ n : ℕ,
      canonicalPackageTail (activePrimePowerPairsCenterBelow (admR n)) t0 s
        = galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
          - canonicalPackageShort (activePrimePowerPairsCenterBelow (admR n)) t0 s := by
    intro n
    have hsplit := finiteCanonicalPrimePowerPackage_eq_short_add_tail
      (activePrimePowerPairsCenterBelow (admR n)) (hI n) t0 ht0 s hsre
    have hB : galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
        = finiteCanonicalPrimePowerPackage
            (activePrimePowerPairsCenterBelow (admR n))
            shiftedLaplaceHeatKernelC s := rfl
    rw [hB, hsplit]
    ring
  have hconv : Tendsto
      (fun n : ℕ =>
        galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
          - canonicalPackageShort (activePrimePowerPairsCenterBelow (admR n)) t0 s)
      Filter.atTop
      (𝓝 (galerkinBcanLimitData.Bcan s - shortPackageLimit t0 s)) :=
    (admissible_hB s hs).sub (canonicalPackageShort_tendsto t0 ht0 s hs)
  refine hconv.congr ?_
  intro n
  exact (htail_eq n).symm

#print axioms canonicalPackageShort_tendsto
#print axioms canonicalPackageTail_tendsto

end

end RHFormalization
