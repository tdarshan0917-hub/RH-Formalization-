import RHFormalization.QuadTPairedTransform
import RHFormalization.AdaptiveGalerkinStage

/-!
# RHFormalization.StageRemainderTransformBound
**Ledger item 3d: the q-summed stage remainder transform bound.**
Triangle inequality over the stage code set + the a-uniform 3c bound +
`adaptiveStageMass_le_two_mul` + `adaptiveL = exp(adaptiveR)`:
the weighted, normalized q-sum of per-prime remainder transforms is
`≤ e^{−R/2}·δ^{−5/2}·Γ(5/2)·SupV²·√2/√π` — n-uniformly bounded AND
vanishing along the net. Closes ledger item 3.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RHFormalization

noncomputable section

open Matrix Real MeasureTheory Set

variable {N : ℕ}

/-- **Item 3d: the normalized q-summed remainder transform bound.** -/
theorem stage_remainder_transform_sum_le (c : ℝ) (n : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (s : ℂ) (hRe : δ ≤ s.re) :
    ‖((1 / (2 * adaptiveL c n) : ℝ) : ℂ)
        * ∑ q ∈ activePrimePowerPairsCenterBelow (adaptiveR c n),
            ((q.weightReal : ℝ) : ℂ)
              * ∫ t in Ioi (0:ℝ), Complex.exp (-(s * t))
                  * ((quadTPairedMassFn (N := N)
                      (activePrimePowerCodesCenterBelow (adaptiveR c n))
                      q.center t : ℝ) : ℂ)‖
      ≤ Real.exp (-(adaptiveR c n) / 2)
          * (δ ^ (-(5:ℝ)/2) * Real.Gamma ((5:ℝ)/2)
              * (SupVConst ^ 2 * Real.sqrt 2 / Real.sqrt Real.pi)) := by
  set B : ℝ := δ ^ (-(5:ℝ)/2) * Real.Gamma ((5:ℝ)/2)
      * (SupVConst ^ 2 * Real.sqrt 2 / Real.sqrt Real.pi) with hB
  have hg : 0 < Real.Gamma ((5:ℝ)/2) := by
    first
      | exact Real.Gamma_pos_of_pos (by norm_num)
      | exact Real.Gamma_pos (by norm_num)
      | (rw [Real.Gamma_eq_integral (by norm_num : (0:ℝ) < 5/2)]
         positivity)
  have hBnn : 0 ≤ B := by
    rw [hB]
    positivity
  have hLpos : 0 < adaptiveL c n := by
    unfold adaptiveL
    positivity
  -- triangle + per-term 3c bound
  have htri : ‖∑ q ∈ activePrimePowerPairsCenterBelow (adaptiveR c n),
        ((q.weightReal : ℝ) : ℂ)
          * ∫ t in Ioi (0:ℝ), Complex.exp (-(s * t))
              * ((quadTPairedMassFn (N := N)
                  (activePrimePowerCodesCenterBelow (adaptiveR c n))
                  q.center t : ℝ) : ℂ)‖
      ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (adaptiveR c n),
          |q.weightReal| * B := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun q _ => ?_)
    rw [norm_mul, Complex.norm_real]
    have hterm := quadTPaired_transform_global_le
      (N := N) (activePrimePowerCodesCenterBelow (adaptiveR c n)) hN
      q.center δ hδ s hRe
    rw [Real.norm_eq_abs]
    calc |q.weightReal| * ‖∫ t in Ioi (0:ℝ), Complex.exp (-(s * t))
            * ((quadTPairedMassFn (N := N)
                (activePrimePowerCodesCenterBelow (adaptiveR c n))
                q.center t : ℝ) : ℂ)‖
        ≤ |q.weightReal| * B := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [hB]
          exact hterm
  -- mass bound + normalization crush
  have hmass := adaptiveStageMass_le_two_mul c n
  have hsum : ∑ q ∈ activePrimePowerPairsCenterBelow (adaptiveR c n),
      |q.weightReal| * B ≤ 2 * Real.exp ((adaptiveR c n) / 2) * B := by
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ hBnn
    calc ∑ q ∈ activePrimePowerPairsCenterBelow (adaptiveR c n), |q.weightReal|
        = adaptiveStageMass c n := rfl
      _ ≤ 2 * Real.exp ((adaptiveR c n) / 2) := hmass
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * adaptiveL c n))]
  calc (1 / (2 * adaptiveL c n))
        * ‖∑ q ∈ activePrimePowerPairsCenterBelow (adaptiveR c n),
            ((q.weightReal : ℝ) : ℂ)
              * ∫ t in Ioi (0:ℝ), Complex.exp (-(s * t))
                  * ((quadTPairedMassFn (N := N)
                      (activePrimePowerCodesCenterBelow (adaptiveR c n))
                      q.center t : ℝ) : ℂ)‖
      ≤ (1 / (2 * adaptiveL c n)) * (2 * Real.exp ((adaptiveR c n) / 2) * B) := by
        apply mul_le_mul_of_nonneg_left (le_trans htri hsum) (by positivity)
    _ = Real.exp (-(adaptiveR c n) / 2) * B := by
        have hL1 : adaptiveL c n = Real.exp (adaptiveR c n) := by
          unfold adaptiveL galerkinL
          ring
        rw [hL1]
        rw [show Real.exp (-(adaptiveR c n) / 2)
          = Real.exp (adaptiveR c n / 2) / Real.exp (adaptiveR c n) from by
          rw [← Real.exp_sub]
          congr 1
          ring]
        have hexpP : (0:ℝ) < Real.exp (adaptiveR c n) := Real.exp_pos _
        field_simp
        ring

#print axioms stage_remainder_transform_sum_le

end

end RHFormalization
