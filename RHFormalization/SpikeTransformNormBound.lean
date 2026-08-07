import RHFormalization.ResolventFirstPowerDomination
import RHFormalization.ResolventSumBound
import RHFormalization.GalerkinOneLetterNormalizationLock
import RHFormalization.GalerkinPairingBounds

/-!
# RHFormalization.SpikeTransformNormBound
**The hT main-term assembly: the per-q spike transform norm bound.**
`‖galerkinSpikeTransform (galerkinLam L) L a s‖
  ≤ 2·Γ(1/2)·(L/(2√π))·(s.re+1/4)^{−1/2}` for `−1/4 < s.re` — triangle
over the modes, entry bound ≤ 2, twin-1 modulus domination per mode,
twin-2 resolvent sum with the monotone floor `τ+λ ≥ τ`... precisely:
per-mode `(s.re+1/4+λ_m)⁻¹` summed via twin 2 at `τ = s.re+1/4`.
N-uniform, a-uniform. L-linear — killed downstream by `1/(2L)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RHFormalization

noncomputable section

open Complex Real

variable {N : ℕ}

/-- **The per-q spike transform bound.** -/
theorem galerkinSpikeTransform_norm_le (L a : ℝ) (hL : 0 < L)
    (s : ℂ) (hs : -(1/4 : ℝ) < s.re) :
    ‖galerkinSpikeTransform (N := N)
        (fun m => galerkinLam L (m : ℕ)) L a s‖
      ≤ 2 * (Real.Gamma ((1/2):ℝ) * (L / (2 * Real.sqrt Real.pi))
          * (s.re + 1/4) ^ (-(1/2):ℝ)) := by
  have hτ : (0:ℝ) < s.re + 1/4 := by linarith
  unfold galerkinSpikeTransform
  calc ‖∑ m : Fin N, ((galerkinT (N := N) L a m m : ℝ) : ℂ) *
        (1 / (s + (1 / 4 : ℂ) + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)))‖
      ≤ ∑ m : Fin N, ‖((galerkinT (N := N) L a m m : ℝ) : ℂ) *
          (1 / (s + (1 / 4 : ℂ) + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m : Fin N, 2 * (s.re + 1/4 + galerkinLam L (m : ℕ))⁻¹ := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hT2 : |galerkinT (N := N) L a m m| ≤ 2 :=
          galerkinT_entry_abs_le L a hL m m
        have hlamnn : 0 ≤ galerkinLam L (m : ℕ) := by
          unfold galerkinLam
          positivity
        have hdom : ‖(1 / (s + (1 / 4 : ℂ)
            + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)) : ℂ)‖
            ≤ (s.re + 1/4 + galerkinLam L (m : ℕ))⁻¹ := by
          rw [one_div]
          exact resolvent_shift_inv_norm_le s (galerkinLam L (m : ℕ)) hs hlamnn
        calc |galerkinT (N := N) L a m m|
              * ‖(1 / (s + (1 / 4 : ℂ)
                  + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)) : ℂ)‖
            ≤ 2 * (s.re + 1/4 + galerkinLam L (m : ℕ))⁻¹ := by
              apply mul_le_mul hT2 hdom (norm_nonneg _) (by norm_num)
    _ = 2 * ∑ m : Fin N, (s.re + 1/4 + galerkinLam L (m : ℕ))⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ 2 * (Real.Gamma ((1/2):ℝ) * (L / (2 * Real.sqrt Real.pi))
          * (s.re + 1/4) ^ (-(1/2):ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have h := resolvent_sum_le (N := N) L hL (s.re + 1/4) hτ
        refine le_trans (le_of_eq ?_) h
        refine Finset.sum_congr rfl (fun m _ => ?_)
        congr 1
        ring

#print axioms galerkinSpikeTransform_norm_le

end

end RHFormalization
