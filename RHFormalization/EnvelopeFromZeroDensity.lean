/-
EnvelopeFromZeroDensity.lean — Campaign D, installment 1 (snapshot: ZD_D1).

The uniform quadratic denominator bound: on any compact away from the pole
set, ‖zeroPoleDenom ρ s‖ ≥ c·(1 + im(ρ)²) uniformly in the zero ρ.
Low zone (bounded im): compact_uniform_pole_distance. High zone: the reverse
triangle inequality against im_sq_le_norm_polePoint and the compact's norm
bound. This is the analytic heart of reducing the envelope to the single
zero-density summability Σ mult(ρ)/(1+im(ρ)²) < ∞.
-/
import RHFormalization.ZpoleFromSeries

namespace RHFormalization

noncomputable section
open Complex Filter Metric

/-- The summand denominator is the distance to the pole point. -/
theorem norm_zeroPoleDenom_eq_dist (ρ s : ℂ) :
    ‖zeroPoleDenom ρ s‖ = dist s (polePoint ρ) := by
  rw [dist_eq_norm]
  unfold zeroPoleDenom polePoint
  congr 1
  ring

/-- D1: uniform quadratic lower bound for denominators on a compact away
from the pole set. -/
theorem denom_lower_bound (K : CompactAwayFromZeroPoles) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ρ : ℂ, IsNontrivialZetaZero ρ →
        ∀ s ∈ K.K, c * (1 + ρ.im ^ 2) ≤ ‖zeroPoleDenom ρ s‖ := by
  obtain ⟨δ, hδ, hδbound⟩ := compact_uniform_pole_distance K
  obtain ⟨C0, hC0⟩ := K.h_compact.isBounded.exists_norm_le
  set C : ℝ := max C0 0 with hCdef
  have hC : ∀ s ∈ K.K, ‖s‖ ≤ C := fun s hs => (hC0 s hs).trans (le_max_left _ _)
  have hCnn : (0:ℝ) ≤ C := le_max_right _ _
  have h2C3 : (0:ℝ) < 2 * C + 3 := by linarith
  refine ⟨min (1/2) (δ / (2*C + 3)),
    lt_min (by norm_num) (div_pos hδ h2C3), ?_⟩
  intro ρ hρ s hs
  rw [norm_zeroPoleDenom_eq_dist]
  rcases le_total (2*C + 2) (ρ.im ^ 2) with hbig | hsmall
  · -- HIGH ZONE: reverse triangle + γ² ≤ ‖polePoint‖
    have h1 : ρ.im ^ 2 ≤ ‖polePoint ρ‖ :=
      im_sq_le_norm_polePoint ρ (le_of_lt hρ.2.1) (le_of_lt hρ.2.2)
    have h2 : ‖polePoint ρ‖ - ‖s‖ ≤ dist s (polePoint ρ) := by
      rw [dist_eq_norm, ← norm_sub_rev]
      exact norm_sub_norm_le _ _
    have h3 : ‖s‖ ≤ C := hC s hs
    have h4 : ρ.im ^ 2 - C ≤ dist s (polePoint ρ) := by linarith
    have h5 : (1 + ρ.im ^ 2) / 2 ≤ dist s (polePoint ρ) := by linarith
    have hnn : (0:ℝ) ≤ 1 + ρ.im ^ 2 := by positivity
    calc min (1/2) (δ/(2*C+3)) * (1 + ρ.im ^ 2)
        ≤ (1/2) * (1 + ρ.im ^ 2) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hnn
      _ = (1 + ρ.im ^ 2) / 2 := by ring
      _ ≤ dist s (polePoint ρ) := h5
  · -- LOW ZONE: uniform pole distance
    have h1 : δ ≤ dist s (polePoint ρ) := hδbound ρ hρ s hs
    have h2 : 1 + ρ.im ^ 2 ≤ 2*C + 3 := by nlinarith
    have hnn : (0:ℝ) ≤ 1 + ρ.im ^ 2 := by positivity
    have hq : (0:ℝ) ≤ δ / (2*C+3) := le_of_lt (div_pos hδ h2C3)
    calc min (1/2) (δ/(2*C+3)) * (1 + ρ.im ^ 2)
        ≤ (δ/(2*C+3)) * (1 + ρ.im ^ 2) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hnn
      _ ≤ (δ/(2*C+3)) * (2*C+3) := mul_le_mul_of_nonneg_left h2 hq
      _ = δ := by field_simp
      _ ≤ dist s (polePoint ρ) := h1

#print axioms norm_zeroPoleDenom_eq_dist
#print axioms denom_lower_bound

/-- The chosen uniform constant for a compact. -/
noncomputable def denomConst (K : CompactAwayFromZeroPoles) : ℝ :=
  (denom_lower_bound K).choose

theorem denomConst_pos (K : CompactAwayFromZeroPoles) : 0 < denomConst K :=
  (denom_lower_bound K).choose_spec.1

theorem denomConst_le (K : CompactAwayFromZeroPoles) :
    ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ∀ s ∈ K.K,
      denomConst K * (1 + ρ.im ^ 2) ≤ ‖zeroPoleDenom ρ s‖ :=
  (denom_lower_bound K).choose_spec.2

/-- D2 — THE CONSTRUCTOR: the full per-compact envelope from the SINGLE
zero-density summability Σ mult(ρ)/(1 + im(ρ)²) < ∞ (classically:
Riemann–von Mangoldt). -/
noncomputable def buildEnvelopeFromZeroDensity
    (M : ZeroMultiplicityData)
    (hsum : Summable (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
      (M.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2))) :
    ZeroPoleEnvelopeData M where
  u := fun K ρ =>
    (1 / denomConst K) * ((M.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2))
  h_summable := fun K => hsum.mul_left _
  h_bound := fun K ρ x hx => by
    have hc := denomConst_pos K
    have hle := denomConst_le K ρ.1 ρ.2 x hx
    have h1 : (0:ℝ) < 1 + ρ.1.im ^ 2 := by positivity
    have hnorm : ‖zeroPoleSummand M ρ.1 x‖ =
        (M.mult ρ.1 : ℝ) / ‖zeroPoleDenom ρ.1 x‖ := by
      unfold zeroPoleSummand
      rw [norm_div, Complex.norm_natCast]
    rw [hnorm]
    have hb : (M.mult ρ.1 : ℝ) / ‖zeroPoleDenom ρ.1 x‖ ≤
        (M.mult ρ.1 : ℝ) / (denomConst K * (1 + ρ.1.im ^ 2)) := by
      gcongr
    refine hb.trans (le_of_eq ?_)
    field_simp

#print axioms buildEnvelopeFromZeroDensity

end
end RHFormalization
