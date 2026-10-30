import RHFormalization.PolylogShiftTheorem
import RHFormalization.PolylogStageClosedForm
import RHFormalization.CompensatedBSubseqEndpoint
import RHFormalization.DBFFStarObject
import Mathlib

/-!
# PolylogSquareStageBridge — PL-5b-i: the operator family at the square stages is the
# von Mangoldt discrepancy

At stage `n = M² − 2`, with `ρ_s := √(s+¼) + ½`,
`compensatedBFamily (M²−2) s = (2√(s+¼))⁻¹ · (vmDiscrepancy M ρ_s − 1/(½ − √(s+¼)))`.
Consequence (via PL-6a): RH follows from boundedness of the pure prime-sum discrepancy
`vmDiscrepancy M ρ_s` on Ω-compacts, uniformly in `M ≥ 2`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- Square-stage star object = discrepancy minus the fixed term. -/
theorem starObject_square_stage_eq_vmDiscrepancy (M : ℕ) (hM : 2 ≤ M) {s : ℂ}
    (hs : s ∈ Ω) :
    starObject (M ^ 2 - 2) s
      = vmDiscrepancy M (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))
        - 1 / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) := by
  rw [starObject_square_stage_closed M hM hs]
  unfold vmDiscrepancy
  generalize Complex.sqrt (s + (1/4:ℂ)) = w
  rw [show (1:ℂ) - (w + (1/2:ℂ)) = (1/2:ℂ) - w by ring]
  ring

/-- **Bridge**: the compensated operator family at the square stages. -/
theorem compensatedBFamily_square_stage (M : ℕ) (hM : 2 ≤ M) {s : ℂ} (hs : s ∈ Ω) :
    compensatedBFamily (M ^ 2 - 2) s
      = (1 / (2 * Complex.sqrt (s + (1/4:ℂ))))
        * (vmDiscrepancy M (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))
            - 1 / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ)))) := by
  unfold compensatedBFamily
  rw [B_sub_compensator_eq _ hs, starObject_square_stage_eq_vmDiscrepancy M hM hs]

/-- Positive lower bound for `‖½ − √(s+¼)‖` on an Ω-compact. -/
theorem halfDenom_min (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ e : ℝ, 0 < e ∧ ∀ s ∈ K, e ≤ ‖(1/2:ℂ) - Complex.sqrt (s + (1/4 : ℂ))‖ := by
  rcases K.eq_empty_or_nonempty with hemp | hne
  · exact ⟨1, one_pos, by simp [hemp]⟩
  · have hcont : ContinuousOn
        (fun s : ℂ => ‖(1/2:ℂ) - Complex.sqrt (s + (1/4 : ℂ))‖) K := by
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
          | (have hd : DifferentiableAt ℂ (fun z : ℂ => Complex.sqrt (z + (1/4:ℂ))) s := by
               have hsh : DifferentiableAt ℂ (fun z : ℂ => z + (1/4:ℂ)) s := by fun_prop
               simpa using (Complex.differentiableAt_sqrt hslit).comp s hsh
             exact hd.continuousAt)
      exact h1.continuousWithinAt
    obtain ⟨s₀, hs₀K, hs₀min⟩ := hK.exists_isMinOn hne hcont
    refine ⟨‖(1/2:ℂ) - Complex.sqrt (s₀ + (1/4:ℂ))‖, ?_, fun s hs => hs₀min hs⟩
    have hne0 : (1/2:ℂ) - Complex.sqrt (s₀ + (1/4:ℂ)) ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (sqrt_ne_half (hKO hs₀K)))
    exact norm_pos_iff.mpr hne0

/-- Square stages `M ↦ (M+2)² − 2` are strictly increasing. -/
theorem squareStage_strictMono : StrictMono (fun M : ℕ => (M + 2) ^ 2 - 2) := by
  intro a b hab
  have h4 : 2 ≤ (a + 2) ^ 2 := by nlinarith
  have hlt : (a + 2) ^ 2 < (b + 2) ^ 2 := by
    first
      | exact Nat.pow_lt_pow_left (by omega : a + 2 < b + 2) (by norm_num)
      | nlinarith
  show (a + 2) ^ 2 - 2 < (b + 2) ^ 2 - 2
  first
    | exact Nat.sub_lt_sub_right h4 hlt
    | exact tsub_lt_tsub_right_of_le h4 hlt

/-- **PL-5b-i endpoint**: RH from boundedness of the von Mangoldt discrepancy at
`ρ_s = √(s+¼) + ½` on Ω-compacts, uniformly over cutoffs `M ≥ 2`. -/
theorem RH_from_vmDiscrepancy_bdd
    (h : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ B : ℝ, ∀ M : ℕ, 2 ≤ M → ∀ s ∈ K,
        ‖vmDiscrepancy M (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))‖ ≤ B) :
    RiemannHypothesis := by
  refine RH_from_compensatedB_locbdd_subseq (fun M : ℕ => (M + 2) ^ 2 - 2)
    squareStage_strictMono ?_
  intro K hK hKO
  obtain ⟨B, hB⟩ := h K hK hKO
  obtain ⟨c, hc, hcK⟩ := kernelDenom_min K hK hKO
  obtain ⟨e, he, heK⟩ := halfDenom_min K hK hKO
  refine ⟨1 / c * (B + 1 / e), fun M s hs => ?_⟩
  show ‖compensatedBFamily ((M + 2) ^ 2 - 2) s‖ ≤ 1 / c * (B + 1 / e)
  rw [compensatedBFamily_square_stage (M + 2) (by omega) (hKO hs), norm_mul]
  have hker : ‖(1:ℂ) / (2 * Complex.sqrt (s + (1/4:ℂ)))‖ ≤ 1 / c := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hc (hcK s hs)
  have hfix : ‖(1:ℂ) / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ)))‖ ≤ 1 / e := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le he (heK s hs)
  have hsum : ‖vmDiscrepancy (M + 2) (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ))
        - 1 / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ)))‖ ≤ B + 1 / e :=
    le_trans (norm_sub_le _ _) (add_le_add (hB (M + 2) (by omega) s hs) hfix)
  exact mul_le_mul hker hsum (norm_nonneg _) (one_div_pos.mpr hc).le

#print axioms starObject_square_stage_eq_vmDiscrepancy
#print axioms compensatedBFamily_square_stage
#print axioms RH_from_vmDiscrepancy_bdd

end

end RHFormalization
