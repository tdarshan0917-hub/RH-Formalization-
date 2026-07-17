import RHFormalization.DBFFO3HstarFromCompensatedB
import RHFormalization.DBFFCompensatorHolo
import RHFormalization.AdmissibleFirstOrderVanish

/-!
# DBFFO3AssemblyInputs

ROUTE CARD
1. Target: reduce parabola-depth O3/hstar to the two real remaining inputs.
2. Objects:
   * square-root multiplier `2√(s+1/4)`;
   * O2 short residual `FirstOrderWindow + SecondResolventResidual`;
   * compensated B-side `DBFFO3CompensatedB`.
3. Raw B on Ω? NO.
4. R = F − raw B forced? NO.
5. True outright from compactness/continuity and banked O2 estimates.
6. Manuscript: D.OP-BOUND / D.TAIL-DENSITY / D.UNIFORM-CAN.
7. Consumer: final parabola-depth O3 assembly.

This file proves the easy assembly inputs:
  * the square-root multiplier is compact-bounded on Ω-compacts;
  * `DBFFO2ShortResidual` is compact-bounded;
  * therefore hstar reduces to:
      Hfree : admissibleFreeStage − compensatorM bounded,
      HR    : R_stage bounded.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology BigOperators

/-- The square-root multiplier is compact-bounded on Ω-compacts. -/
theorem DBFFO3_sqrtFactorBound :
    DBFFO3SqrtFactorBound := by
  intro K hK hKO
  have hcontF :
      ContinuousOn
        (fun s : ℂ => (2 : ℂ) * Complex.sqrt (s + (1/4 : ℂ))) K := by
    intro z hz
    have hsq : ContinuousAt
        (fun s : ℂ => Complex.sqrt (s + (1/4 : ℂ))) z :=
      (sqrtShiftFun_analyticAt (hKO hz)).continuousAt
    exact (continuousAt_const.mul hsq).continuousWithinAt
  have hcontNorm :
      ContinuousOn
        (fun s : ℂ => ‖(2 : ℂ) * Complex.sqrt (s + (1/4 : ℂ))‖) K :=
    hcontF.norm

  first
    | obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hcontNorm
      refine ⟨max C0 0, le_max_right C0 0, ?_⟩
      intro s hs
      have hbound := hC0 s hs
      have hval :
          ‖(2 : ℂ) * Complex.sqrt (s + (1/4 : ℂ))‖ ≤ C0 := by
        simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound
      exact le_trans hval (le_max_left C0 0)
    | obtain ⟨C0, hC0⟩ :=
        IsCompact.exists_bound_of_continuousOn hK hcontNorm
      refine ⟨max C0 0, le_max_right C0 0, ?_⟩
      intro s hs
      have hbound := hC0 s hs
      have hval :
          ‖(2 : ℂ) * Complex.sqrt (s + (1/4 : ℂ))‖ ≤ C0 := by
        simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound
      exact le_trans hval (le_max_left C0 0)

/-- The O2 short residual is uniformly compact-bounded. -/
theorem DBFFO3_shortResidual_bounded :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ Cshort : ℝ,
        ∀ n : ℕ, ∀ s ∈ K, ‖DBFFO2ShortResidual n s‖ ≤ Cshort := by
  intro K hK hKO
  obtain ⟨C1, hC1pos, hC1⟩ :=
    FirstOrderWindow_uniform_bound K hK hKO
  obtain ⟨C2, hC2pos, hC2⟩ :=
    DBFFO2_order2_anchor_uniform_bound K hK hKO
  refine ⟨C1 + C2, ?_⟩
  intro n s hs
  have hx : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hxpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity

  have h1' : ‖FirstOrderWindow n s‖ ≤ C1 := by
    refine le_trans (hC1 n s hs) ?_
    rw [div_le_iff₀ hxpos]
    nlinarith [hC1pos.le, hx]

  have h2' : ‖SecondResolventResidual n s‖ ≤ C2 := by
    refine le_trans (hC2 n s hs) ?_
    rw [div_le_iff₀ hxpos]
    nlinarith [hC2pos.le, hx]

  unfold DBFFO2ShortResidual
  calc
    ‖FirstOrderWindow n s + SecondResolventResidual n s‖
        ≤ ‖FirstOrderWindow n s‖ + ‖SecondResolventResidual n s‖ := norm_add_le _ _
    _ ≤ C1 + C2 := add_le_add h1' h2'

/--
Compensated-B boundedness now reduces to two real inputs:
free-minus-compensator boundedness and R-stage sector boundedness.
-/
theorem DBFFO3_compensatedB_bound_from_free_and_R
    (Hfree :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cfree : ℝ,
          ∀ n : ℕ, ∀ s ∈ K,
            ‖admissibleFreeStage n s - compensatorM n s‖ ≤ Cfree)
    (HR :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ CR : ℝ,
          ∀ n : ℕ, ∀ s ∈ K,
            ‖galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s‖ ≤ CR) :
    DBFFO3CompensatedBBound :=
  DBFFO3_compensatedB_bounded_from_FMR
    Hfree
    DBFFO3_shortResidual_bounded
    HR

/--
Global O3 hstar reduces to the same two real inputs.
-/
theorem DBFFO3Hstar_from_free_and_R
    (Hfree :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cfree : ℝ,
          ∀ n : ℕ, ∀ s ∈ K,
            ‖admissibleFreeStage n s - compensatorM n s‖ ≤ Cfree)
    (HR :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ CR : ℝ,
          ∀ n : ℕ, ∀ s ∈ K,
            ‖galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s‖ ≤ CR) :
    DBFFO3Hstar :=
  DBFFO3Hstar_from_compensatedB_bound
    DBFFO3_sqrtFactorBound
    (DBFFO3_compensatedB_bound_from_free_and_R Hfree HR)

/--
Parabola-depth O3 hstar also reduces to the same two real inputs.
-/
theorem DBFFO3ParabolaDepthHstar_from_free_and_R
    (Hfree :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cfree : ℝ,
          ∀ n : ℕ, ∀ s ∈ K,
            ‖admissibleFreeStage n s - compensatorM n s‖ ≤ Cfree)
    (HR :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ CR : ℝ,
          ∀ n : ℕ, ∀ s ∈ K,
            ‖galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s‖ ≤ CR) :
    DBFFO3ParabolaDepthHstar := by
  intro K hK hKO hdepth
  exact (DBFFO3Hstar_from_free_and_R Hfree HR) K hK hKO

#print axioms DBFFO3_sqrtFactorBound
#print axioms DBFFO3_shortResidual_bounded
#print axioms DBFFO3_compensatedB_bound_from_free_and_R
#print axioms DBFFO3Hstar_from_free_and_R
#print axioms DBFFO3ParabolaDepthHstar_from_free_and_R

end

end RHFormalization
