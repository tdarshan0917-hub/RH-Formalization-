import RHFormalization.DBFFO3ParabolaDepthReduction
import RHFormalization.AdmissibleFreeFH
import RHFormalization.AdmissiblePrimeFirstOrderSplit

/-!
# DBFFO3FMRBridge

ROUTE CARD
1. Target: parabola-depth O3 / hstar, F-M-R algebra bridge.
2. Object: compensated B-side `B_stage - compensatorM`.
3. Raw B on Ω? NO — this is a per-stage finite algebra identity.
4. R = F − raw B forced globally? NO — only stage-level definitional algebra.
5. True outright from:
   `R_stage = F_stage - B_stage`,
   `F_stage = admissibleFreeStage + FadmPrimeStage`,
   `FadmPrimeStage = FirstOrderWindow + SecondResolventResidual`.
6. Manuscript: D.OP-BOUND / D.TAIL-DENSITY / D.UNIFORM-CAN, bridge toward
   the parabola-depth hstar estimate.
7. Consumer: `DBFFO3ParabolaDepthHstar`.

This file proves the key identity:

  B_stage n - M_n
    =
  (admissibleFreeStage n - M_n)
    + DBFFO2ShortResidual n
    - R_stage n.

Thus the remaining parabola-depth compensated-B bound is reduced to:
  free-minus-compensator bound,
  O2 short-residual bound,
  R-stage sector bound.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology BigOperators

/-- The compensated B-side object. -/
def DBFFO3CompensatedB (n : ℕ) (s : ℂ) : ℂ :=
  galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
    - compensatorM n s

/--
F-M-R identity for the compensated B-side.

This is the exact algebraic bridge:
`B - M = (free - M) + short - R`.
-/
theorem DBFFO3_compensatedB_eq_FMR
    (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    DBFFO3CompensatedB n s =
      (admissibleFreeStage n s - compensatorM n s)
        + DBFFO2ShortResidual n s
        - galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s := by
  have hR :
      galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s =
        galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
          - galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s := by
    rfl
  have hF :=
    package_F_stage_eq_free_add_prime n s
  have hP :=
    FadmPrimeStage_eq_first_plus_second n hs
  unfold DBFFO3CompensatedB DBFFO2ShortResidual
  rw [hR, hF, hP]
  ring

/--
If the three F-M-R pieces are compact-uniformly bounded, then the compensated
B-side is compact-uniformly bounded.

The next files should discharge these hypotheses from:
  * free-minus-compensator geometry,
  * banked O2 short residual estimates,
  * sector/R-stage bounds.
-/
theorem DBFFO3_compensatedB_bounded_from_FMR
    (Hfree :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cfree : ℝ,
          ∀ n : ℕ, ∀ s ∈ K,
            ‖admissibleFreeStage n s - compensatorM n s‖ ≤ Cfree)
    (Hshort :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cshort : ℝ,
          ∀ n : ℕ, ∀ s ∈ K,
            ‖DBFFO2ShortResidual n s‖ ≤ Cshort)
    (HR :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ CR : ℝ,
          ∀ n : ℕ, ∀ s ∈ K,
            ‖galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s‖ ≤ CR) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ,
        ∀ n : ℕ, ∀ s ∈ K,
          ‖DBFFO3CompensatedB n s‖ ≤ C := by
  intro K hK hKO
  obtain ⟨Cfree, hfree⟩ := Hfree K hK hKO
  obtain ⟨Cshort, hshort⟩ := Hshort K hK hKO
  obtain ⟨CR, hR⟩ := HR K hK hKO
  refine ⟨Cfree + Cshort + CR, ?_⟩
  intro n s hs

  let A : ℂ := admissibleFreeStage n s - compensatorM n s
  let B : ℂ := DBFFO2ShortResidual n s
  let C : ℂ := galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s

  have hEq : DBFFO3CompensatedB n s = A + B - C := by
    simpa [A, B, C] using
      DBFFO3_compensatedB_eq_FMR n (s := s) (hKO hs)

  have hA : ‖A‖ ≤ Cfree := by
    simpa [A] using hfree n s hs
  have hB : ‖B‖ ≤ Cshort := by
    simpa [B] using hshort n s hs
  have hC : ‖C‖ ≤ CR := by
    simpa [C] using hR n s hs

  calc
    ‖DBFFO3CompensatedB n s‖
        = ‖A + B - C‖ := by rw [hEq]
    _ ≤ ‖A + B‖ + ‖C‖ := by
        simpa using norm_sub_le (A + B) C
    _ ≤ (‖A‖ + ‖B‖) + ‖C‖ := by
        exact add_le_add (norm_add_le A B) (le_rfl : ‖C‖ ≤ ‖C‖)
    _ ≤ (Cfree + Cshort) + CR := by
        exact add_le_add (add_le_add hA hB) hC
    _ = Cfree + Cshort + CR := by ring

#print axioms DBFFO3CompensatedB
#print axioms DBFFO3_compensatedB_eq_FMR
#print axioms DBFFO3_compensatedB_bounded_from_FMR

end

end RHFormalization
