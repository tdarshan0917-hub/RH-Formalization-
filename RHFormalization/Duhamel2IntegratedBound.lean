import RHFormalization.Duhamel2Term
import RHFormalization.BetaConvBound

/-!
# Brick 2, Stone 6C-ii: the INTEGRATED order-2 Duhamel bound
`|duhamel2Term δ qs w L t| ≤ B²·L²/π` for `t > 0`, finite and `t`-INDEPENDENT —
order-2 case of the convergent Dyson/Duhamel series (manuscript Lemma B.TC).
Chains: triangle bound (6C-i) → integrand sqrt-bound (6B') factored via the heat
constant → Beta convolution ≤ 4 (6C-iii) → arithmetic. B = ∑ |w q|·bumpMass.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix Real MeasureTheory
open scoped BigOperators

variable {N : ℕ}

/-- `√(π/(s·(π/L)²))/2 = (L/(2√π))·s^{-1/2}`. -/
theorem sqrt_heat_factor (L s : ℝ) (hL : 0 < L) (hs : 0 < s) :
    Real.sqrt (Real.pi / (s * (Real.pi / L) ^ 2)) / 2
      = (L / (2 * Real.sqrt Real.pi)) * s ^ (-(1:ℝ)/2) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hsimp : Real.pi / (s * (Real.pi / L) ^ 2) = L ^ 2 / Real.pi * s⁻¹ := by
    field_simp
  rw [hsimp, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      Real.mul_rpow (by positivity) (by positivity),
      Real.div_rpow (by positivity) (by positivity)]
  rw [show ((L:ℝ) ^ 2) ^ ((1:ℝ)/2) = L by
        rw [← Real.rpow_natCast L 2, ← Real.rpow_mul hL.le]; norm_num]
  rw [Real.inv_rpow hs.le, ← Real.rpow_neg hs.le, show (-(1:ℝ)/2) = -(1/2) by ring]
  ring

/-- The order-2 integrand is continuous in `u`. -/
theorem duhamel2Integrand_continuous
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    Continuous (fun u : ℝ => duhamel2Integrand (N := N) δ qs w L t u) := by
  simp only [duhamel2Integrand_eq_sum]
  apply continuous_finset_sum; intro m _
  apply continuous_finset_sum; intro n _
  unfold heatWeight; fun_prop

/-- **Stone 6C-ii**: the integrated order-2 Duhamel bound, `t`-independent. -/
theorem abs_duhamel2Term_le_const
    (δ : ℝ) (hδ : 0 < δ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (t : ℝ) (ht : 0 < t) :
    |duhamel2Term (N := N) δ qs w L t|
      ≤ ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L) ^ 2 * (L ^ 2 / Real.pi) := by
  set B := ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L) with hB
  set C := (L / (2 * Real.sqrt Real.pi)) ^ 2 with hC
  refine le_trans (abs_duhamel2Term_le_integral_abs δ qs w L t ht.le) ?_
  have hpt : ∀ u ∈ Set.Ioo (0:ℝ) t,
      |duhamel2Integrand (N := N) δ qs w L t u|
        ≤ B ^ 2 * C * ((t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2)) := by
    intro u hu
    obtain ⟨hu0, hut⟩ := hu
    have htu : 0 < t - u := by linarith
    refine le_trans (abs_duhamel2Integrand_le_sqrt δ hδ qs w L hL t u hu0 htu) ?_
    rw [sqrt_heat_factor L (t - u) hL htu, sqrt_heat_factor L u hL hu0, hC]
    apply le_of_eq; ring
  have hint_lhs : IntervalIntegrable
      (fun u : ℝ => |duhamel2Integrand (N := N) δ qs w L t u|) MeasureTheory.volume 0 t :=
    ((duhamel2Integrand_continuous δ qs w L t).abs).intervalIntegrable 0 t
  have hint_rhs : IntervalIntegrable
      (fun u : ℝ => B ^ 2 * C * ((t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2)))
      MeasureTheory.volume 0 t :=
    (intervalIntegrable_beta_integrand t ht).const_mul (B ^ 2 * C)
  calc ∫ u in (0:ℝ)..t, |duhamel2Integrand (N := N) δ qs w L t u|
      ≤ ∫ u in (0:ℝ)..t, B ^ 2 * C * ((t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2)) :=
        intervalIntegral.integral_mono_on_of_le_Ioo ht.le hint_lhs hint_rhs hpt
    _ = B ^ 2 * C * ∫ u in (0:ℝ)..t, (t - u) ^ (-(1:ℝ)/2) * u ^ (-(1:ℝ)/2) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ B ^ 2 * C * 4 := by
        apply mul_le_mul_of_nonneg_left (beta_conv_bound t ht)
        rw [hC]; positivity
    _ = B ^ 2 * (L ^ 2 / Real.pi) := by
        rw [hC, show (L / (2 * Real.sqrt Real.pi)) ^ 2 = L ^ 2 / (4 * Real.pi) by
          rw [div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring]
        ring

#print axioms abs_duhamel2Term_le_const
end
end RHFormalization
