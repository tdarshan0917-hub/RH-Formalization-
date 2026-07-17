import RHFormalization.DBFFO3FMRBridge

/-!
# DBFFO3HstarFromCompensatedB

ROUTE CARD
1. Target: parabola-depth O3 / hstar bridge.
2. Object: `starObject` and the compensated B-side
   `DBFFO3CompensatedB = B_stage − compensatorM`.
3. Raw B on Ω? NO — only the finite-stage factored identity from `DBFFStarObject`.
4. R = F − raw B forced? NO.
5. True outright from the factored identity and compact boundedness of the
   square-root multiplier.
6. Manuscript: D.OP-BOUND / D.TAIL-DENSITY / D.UNIFORM-CAN.
7. Consumer: `DBFFO3ParabolaDepthHstar`.

This file proves the reverse direction of the D.OP.2 factorization:

  B_stage − M = (2√(s+1/4))⁻¹ · starObject

so a compact bound on `B_stage − M` gives a compact bound on `starObject`,
provided the harmless multiplier `2√(s+1/4)` is bounded on the compact.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology BigOperators

/-- Compact boundedness of the square-root multiplier. -/
def DBFFO3SqrtFactorBound : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    ∃ Cs : ℝ, 0 ≤ Cs ∧
      ∀ s ∈ K, ‖(2 : ℂ) * Complex.sqrt (s + (1/4 : ℂ))‖ ≤ Cs

/-- Compact boundedness of the compensated B-side. -/
def DBFFO3CompensatedBBound : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    ∃ CB : ℝ,
      ∀ n : ℕ, ∀ s ∈ K, ‖DBFFO3CompensatedB n s‖ ≤ CB

/--
Reverse factored identity: on Ω,

  starObject = (2√(s+1/4)) · (B_stage − compensatorM).
-/
theorem starObject_eq_sqrtFactor_mul_compensatedB
    (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    starObject n s =
      ((2 : ℂ) * Complex.sqrt (s + (1/4 : ℂ))) *
        DBFFO3CompensatedB n s := by
  let a : ℂ := (2 : ℂ) * Complex.sqrt (s + (1/4 : ℂ))
  have ha : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero (by norm_num) (sqrt_ne_zero' hs)
  have h :=
    B_sub_compensator_eq n hs
  have hmul :
      a * DBFFO3CompensatedB n s = starObject n s := by
    unfold DBFFO3CompensatedB
    change a *
        (galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
          - compensatorM n s)
      = starObject n s
    rw [h]
    change a * ((1 / a) * starObject n s) = starObject n s
    field_simp [ha]
  exact hmul.symm

/--
A compensated-B bound plus the square-root multiplier bound gives full hstar.
-/
theorem DBFFO3Hstar_from_compensatedB_bound
    (Hsqrt : DBFFO3SqrtFactorBound)
    (HB : DBFFO3CompensatedBBound) :
    DBFFO3Hstar := by
  intro K hK hKO
  obtain ⟨Cs, hCs0, hCs⟩ := Hsqrt K hK hKO
  obtain ⟨CB, hB⟩ := HB K hK hKO
  refine ⟨Cs * max CB 0, ?_⟩
  intro n s hs
  rw [starObject_eq_sqrtFactor_mul_compensatedB n (hKO hs), norm_mul]
  have hB' : ‖DBFFO3CompensatedB n s‖ ≤ max CB 0 :=
    le_trans (hB n s hs) (le_max_left CB 0)
  exact mul_le_mul (hCs s hs) hB' (norm_nonneg _) hCs0

/--
Parabola-depth compensated-B bound gives the remaining parabola-depth hstar.
-/
theorem DBFFO3ParabolaDepthHstar_from_compensatedB_bound
    (Hsqrt : DBFFO3SqrtFactorBound)
    (HBpar :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        (∀ δ : ℝ, 0 < δ →
          ¬ (∀ s ∈ K,
            (1 / 2 : ℝ) + δ ≤ (Complex.sqrt (s + (1/4 : ℂ))).re)) →
        ∃ CB : ℝ,
          ∀ n : ℕ, ∀ s ∈ K, ‖DBFFO3CompensatedB n s‖ ≤ CB) :
    DBFFO3ParabolaDepthHstar := by
  intro K hK hKO hdepth
  obtain ⟨Cs, hCs0, hCs⟩ := Hsqrt K hK hKO
  obtain ⟨CB, hB⟩ := HBpar K hK hKO hdepth
  refine ⟨Cs * max CB 0, ?_⟩
  intro n s hs
  rw [starObject_eq_sqrtFactor_mul_compensatedB n (hKO hs), norm_mul]
  have hB' : ‖DBFFO3CompensatedB n s‖ ≤ max CB 0 :=
    le_trans (hB n s hs) (le_max_left CB 0)
  exact mul_le_mul (hCs s hs) hB' (norm_nonneg _) hCs0

#print axioms DBFFO3SqrtFactorBound
#print axioms DBFFO3CompensatedBBound
#print axioms starObject_eq_sqrtFactor_mul_compensatedB
#print axioms DBFFO3Hstar_from_compensatedB_bound
#print axioms DBFFO3ParabolaDepthHstar_from_compensatedB_bound

end

end RHFormalization
