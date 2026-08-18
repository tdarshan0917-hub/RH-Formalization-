import RHFormalization.DBFFCompensator
import RHFormalization.DBFFDeficitCompactBound
import RHFormalization.ShiftedLaplaceOmegaGeometry
import Mathlib

/-!
B(i)-5: the E⁰ compact-gap lemmas (STATED, per GPT standing instruction).

With w(s) = Complex.sqrt (s + 1/4) on the slit plane Ω:
1. `denseE0 s = 1/(2·w·(1/2 − w))` — the disk-identity main term
   (B7 consumes: ∫₀^R e^{u/2}K(u,s)du = compensatorM − E⁰; live bridge
   E_n = F^ctr − E⁰ per the signed B7 correction).
2. Gap (ii) is BANKED: `kernelDenom_min` (DBFFDeficitCompactBound) gives
   ∃ c > 0 with c ≤ ‖2w‖ on K — consumed, not reproved.
3. Gap (iii) NEW: `halfSubSqrt_min` — ∃ c > 0 with c ≤ ‖1/2 − w‖ on K,
   same exists_isMinOn mechanism, nonvanishing at minimizer from banked
   `sqrt_ne_half`.
4. `denseE0_bounded_on_compact` — ‖E⁰‖ ≤ (c₁·c₂)⁻¹ on K.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology

/-- **The disk-identity main term** `E⁰(s) = 1/(2·w·(½−w))`, w = √(s+¼). -/
def denseE0 (s : ℂ) : ℂ :=
  1 / (2 * Complex.sqrt (s + (1/4:ℂ))
        * ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))))

/-- **Gap (iii)**: positive lower bound for `‖½ − √(s+¼)‖` on an Ω-compact. -/
theorem halfSubSqrt_min (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ K, c ≤ ‖(1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))‖ := by
  rcases K.eq_empty_or_nonempty with hemp | hne
  · exact ⟨1, one_pos, by simp [hemp]⟩
  · have hcont : ContinuousOn
        (fun s : ℂ => ‖(1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))‖) K := by
      apply ContinuousOn.norm
      apply ContinuousOn.sub continuousOn_const
      intro s hs
      have hslit : (s + (1/4:ℂ)) ∈ Complex.slitPlane :=
        shiftedLaplaceShift_mem_slitPlane_of_mem_Omega s (hKO hs)
      have h1 : ContinuousAt (fun z : ℂ => Complex.sqrt (z + (1/4:ℂ))) s := by
        first
          | exact ((Complex.continuousAt_sqrt hslit).comp
              (by fun_prop : ContinuousAt (fun z : ℂ => z + (1/4:ℂ)) s))
          | exact ContinuousAt.comp (Complex.continuousAt_sqrt hslit)
              (by fun_prop)
          | (have hd : DifferentiableAt ℂ
                (fun z : ℂ => Complex.sqrt (z + (1/4:ℂ))) s := by
               have hsh : DifferentiableAt ℂ (fun z : ℂ => z + (1/4:ℂ)) s := by
                 fun_prop
               simpa using (Complex.differentiableAt_sqrt hslit).comp s hsh
             exact hd.continuousAt)
      exact h1.continuousWithinAt
    obtain ⟨s₀, hs₀K, hs₀min⟩ := hK.exists_isMinOn hne hcont
    refine ⟨‖(1/2:ℂ) - Complex.sqrt (s₀ + (1/4:ℂ))‖, ?_, fun s hs => hs₀min hs⟩
    have hne_half : Complex.sqrt (s₀ + (1/4:ℂ)) ≠ (1/2:ℂ) :=
      sqrt_ne_half (hKO hs₀K)
    have hdiff : (1/2:ℂ) - Complex.sqrt (s₀ + (1/4:ℂ)) ≠ 0 := by
      intro h0
      apply hne_half
      linear_combination -h0
    exact norm_pos_iff.mpr hdiff

/-- **B(i)-5 export**: `E⁰` is uniformly bounded on every Ω-compact. -/
theorem denseE0_bounded_on_compact
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ K, ‖denseE0 s‖ ≤ C := by
  obtain ⟨c₁, hc₁, hc₁K⟩ := kernelDenom_min K hK hKO
  obtain ⟨c₂, hc₂, hc₂K⟩ := halfSubSqrt_min K hK hKO
  refine ⟨(c₁ * c₂)⁻¹, inv_pos.mpr (mul_pos hc₁ hc₂), ?_⟩
  intro s hs
  unfold denseE0
  rw [norm_div, norm_one, norm_mul]
  have h1 := hc₁K s hs
  have h2 := hc₂K s hs
  have hden : c₁ * c₂
      ≤ ‖2 * Complex.sqrt (s + (1/4:ℂ))‖
        * ‖(1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))‖ :=
    mul_le_mul h1 h2 hc₂.le (norm_nonneg _)
  have hden0 : (0:ℝ) < ‖2 * Complex.sqrt (s + (1/4:ℂ))‖
        * ‖(1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))‖ :=
    lt_of_lt_of_le (mul_pos hc₁ hc₂) hden
  rw [div_le_iff₀ hden0]
  rw [inv_mul_eq_div, le_div_iff₀ (mul_pos hc₁ hc₂)]
  nlinarith [hden, (mul_pos hc₁ hc₂).le]

#print axioms denseE0
#print axioms halfSubSqrt_min
#print axioms denseE0_bounded_on_compact

end

end RHFormalization
