import RHFormalization.GreenSqRemainderExpForm
import Mathlib

/-!
# GreenSqRemainderBound — P2-C2b: the box remainder is schedule-crushed

ROUTE CARD
1. Target: for `0 < κ`, `0 ≤ a ≤ L`, `1 ≤ κ*L`:
   `|greenSqRemainder κ L a| ≤ 2·(2L + 1/(2κ))·e^{−2κ(L−a)}/κ²`.
   Via banked exp/sinh form: `|M| ≤ 2L + 1/(2κ)` (triangle, y,z ∈ (0,1));
   `sinh(κL) ≥ e^{κL}/4` for `κL ≥ 1` ⇒ `e^{2κa}/sinh² ≤ 16e^{−2κ(L−a)}`.
   Along the net (`L−a ≥ admL−admR → ∞`) this is superexponential eps.
2. Raw B on Ω? NO. B−M bare Prop? NO — elementary real bounds.
3. Consumer: the box-error eps sector of h_expansion (with P2-B3 Parseval).
-/

set_option autoImplicit false

namespace RHFormalization

open Real

/-- `|M| ≤ 2L + 1/(2κ)`. -/
theorem greenSqRemainderM_abs_le (κ L a : ℝ)
    (hκ : 0 < κ) (ha0 : 0 ≤ a) (haL : a ≤ L) :
    |greenSqRemainderM κ L a| ≤ 2 * L + 1 / (2 * κ) := by
  unfold greenSqRemainderM
  set y := Real.exp (-(2*κ*a)) with hy
  set z := Real.exp (-(2*κ*(L-a))) with hz
  have hy0 : 0 < y := Real.exp_pos _
  have hy1 : y ≤ 1 := by
    rw [hy]
    calc Real.exp (-(2*κ*a)) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero
  have hz0 : 0 < z := Real.exp_pos _
  have hz1 : z ≤ 1 := by
    rw [hz]
    calc Real.exp (-(2*κ*(L-a))) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero
  -- T1: 0 ≤ T1 ≤ 2a
  have h1y : (0:ℝ) ≤ 1 - y := by linarith
  have hzy : z * y ≤ z := by nlinarith [mul_le_mul_of_nonneg_left hy1 hz0.le]
  have h2z : (0:ℝ) ≤ 2 - z * (1 + y) := by nlinarith [hzy, hz1]
  have h2z' : 2 - z * (1 + y) ≤ 2 := by
    nlinarith [mul_nonneg hz0.le (by linarith : (0:ℝ) ≤ 1 + y)]
  have hcore1 : y * (1 - y) ≤ 1 := by nlinarith [sq_nonneg y]
  have hprod2 : y * (1 - y) * (2 - z * (1 + y)) ≤ 2 := by
    have h := mul_le_mul_of_nonneg_right hcore1 h2z
    linarith [h2z']
  have hT1nn : 0 ≤ a * y * (1 - y) * (2 - z * (1 + y)) :=
    mul_nonneg (mul_nonneg (mul_nonneg ha0 hy0.le) h1y) h2z
  have hT1val : a * y * (1 - y) * (2 - z * (1 + y)) ≤ 2 * a := by
    nlinarith [mul_le_mul_of_nonneg_left hprod2 ha0]
  -- T2: 0 ≤ T2 ≤ L - a
  have hLa : (0:ℝ) ≤ L - a := by linarith
  have hy2 : (1 - y) ^ 2 ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hy1 hy0.le]
  have hT2nn : (0:ℝ) ≤ (L - a) * (1 - y) ^ 2 := mul_nonneg hLa (sq_nonneg _)
  have hT2val : (L - a) * (1 - y) ^ 2 ≤ L - a := by
    nlinarith [mul_le_mul_of_nonneg_left hy2 hLa]
  -- T3: 0 ≤ T3 ≤ 1/(2k)
  have h2k : (0:ℝ) < 2 * κ := by linarith
  have hyz1 : y * z ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hz1 hy0.le]
  have h1yz : (0:ℝ) ≤ 1 - y * z := by linarith
  have hyznn : (0:ℝ) ≤ y * z := mul_nonneg hy0.le hz0.le
  have hnum_nn : (0:ℝ) ≤ (1 - y) ^ 2 * (1 - y * z) :=
    mul_nonneg (sq_nonneg _) h1yz
  have hnum_le : (1 - y) ^ 2 * (1 - y * z) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hy2 h1yz]
  have hT3nn : (0:ℝ) ≤ (1 - y) ^ 2 * (1 - y * z) / (2 * κ) :=
    div_nonneg hnum_nn h2k.le
  have hT3val : (1 - y) ^ 2 * (1 - y * z) / (2 * κ) ≤ 1 / (2 * κ) := by
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum_le (inv_pos.mpr h2k).le
  have hbnd : (0:ℝ) ≤ 1 / (2 * κ) := by positivity
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · linarith [hT1nn, hT2val, hT3val]
  · linarith [hT1val, hT2nn, hT3nn, hbnd]

/-- `sinh(κL) ≥ e^{κL}/4` for `κL ≥ 1`. -/
theorem sinh_ge_exp_div_four (u : ℝ) (hu : 1 ≤ u) :
    Real.exp u / 4 ≤ Real.sinh u := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-u) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-1) ≤ 1/2 := by
    rw [Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)] <;>
      first
        | nlinarith [Real.add_one_le_exp (1:ℝ)]
        | (have := Real.add_one_le_exp (1:ℝ); linarith)
  have h3 : Real.exp u ≥ Real.exp 1 := Real.exp_le_exp.mpr hu
  have h4 : (2:ℝ) ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1:ℝ)]
  have h5 : Real.exp (-u) ≤ Real.exp u / 2 := by
    calc Real.exp (-u) ≤ 1/2 := le_trans h1 h2
      _ ≤ Real.exp u / 2 := by nlinarith
  linarith

/-- **P2-C2b: the box remainder bound.** -/
theorem greenSqRemainder_abs_le (κ L a : ℝ)
    (hκ : 0 < κ) (ha0 : 0 ≤ a) (haL : a ≤ L) (hkL : 1 ≤ κ * L) :
    |greenSqRemainder κ L a|
      ≤ 2 * (2 * L + 1 / (2 * κ)) * Real.exp (-(2*κ*(L-a))) / κ^2 := by
  have hL : 0 < L := by
    by_contra h
    push_neg at h
    nlinarith
  rw [greenSqRemainder_exp_form κ L a hκ hL]
  have hS : Real.exp (κ * L) / 4 ≤ Real.sinh (κ * L) :=
    sinh_ge_exp_div_four (κ * L) hkL
  have hSpos : 0 < Real.sinh (κ * L) := by
    have := Real.exp_pos (κ * L)
    linarith
  have hM := greenSqRemainderM_abs_le κ L a hκ ha0 haL
  have hMnn : (0:ℝ) ≤ 2 * L + 1 / (2 * κ) := by positivity
  rw [abs_div, abs_mul]
  have hden_eq : |8 * κ^2 * Real.sinh (κ*L)^2|
      = 8 * κ^2 * Real.sinh (κ*L)^2 := by
    rw [abs_of_nonneg]
    positivity
  rw [hden_eq]
  have hexp_abs : |Real.exp (2*κ*a)| = Real.exp (2*κ*a) := abs_of_pos (Real.exp_pos _)
  rw [hexp_abs]
  -- numerator ≤ e^{2κa}·(2L+1/(2κ)); denominator ≥ 8κ²e^{2κL}/16
  have hSsq : Real.exp (κ*L)^2 / 16 ≤ Real.sinh (κ*L)^2 := by
    have h4 : (0:ℝ) < 4 := by norm_num
    nlinarith [hS, Real.exp_pos (κ * L), hSpos]
  have hden_le : 8 * κ^2 * (Real.exp (κ*L)^2 / 16)
      ≤ 8 * κ^2 * Real.sinh (κ*L)^2 := by
    have h8 : (0:ℝ) ≤ 8 * κ^2 := by positivity
    exact mul_le_mul_of_nonneg_left hSsq h8
  have hden2_pos : (0:ℝ) < 8 * κ^2 * (Real.exp (κ*L)^2 / 16) := by
    positivity
  have hnum_le : Real.exp (2*κ*a) * |greenSqRemainderM κ L a|
      ≤ Real.exp (2*κ*a) * (2 * L + 1 / (2 * κ)) :=
    mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
  have hnum_nn : (0:ℝ) ≤ Real.exp (2*κ*a) * |greenSqRemainderM κ L a| := by
    positivity
  have hkey : Real.exp (2*κ*a) * |greenSqRemainderM κ L a|
        / (8 * κ^2 * Real.sinh (κ*L)^2)
      ≤ Real.exp (2*κ*a) * (2 * L + 1 / (2 * κ))
        / (8 * κ^2 * (Real.exp (κ*L)^2 / 16)) := by
    calc Real.exp (2*κ*a) * |greenSqRemainderM κ L a|
          / (8 * κ^2 * Real.sinh (κ*L)^2)
        ≤ Real.exp (2*κ*a) * |greenSqRemainderM κ L a|
          / (8 * κ^2 * (Real.exp (κ*L)^2 / 16)) :=
          div_le_div_of_nonneg_left hnum_nn hden2_pos hden_le
      _ ≤ Real.exp (2*κ*a) * (2 * L + 1 / (2 * κ))
          / (8 * κ^2 * (Real.exp (κ*L)^2 / 16)) := by
          first
            | exact div_le_div_of_le_left hnum_le hden2_pos (by positivity)
            | exact (div_le_div_iff_right hden2_pos).mpr hnum_le
            | exact (div_le_div_right hden2_pos).mpr hnum_le
            | (apply div_le_div_of_nonneg_right hnum_le hden2_pos)
            | (gcongr)
  refine hkey.trans ?_
  have hexp2L : Real.exp (κ*L)^2 = Real.exp (2*κ*L) := by
    rw [show (2*κ*L) = κ*L + κ*L by ring, Real.exp_add]
    ring
  have hfinal : Real.exp (2*κ*a) * (2 * L + 1 / (2 * κ))
        / (8 * κ^2 * (Real.exp (κ*L)^2 / 16))
      = 2 * (2 * L + 1 / (2 * κ)) * Real.exp (-(2*κ*(L-a))) / κ^2 := by
    rw [hexp2L]
    have hcollapse : Real.exp (2*κ*a)
        = Real.exp (-(2*κ*(L-a))) * Real.exp (2*κ*L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hcollapse]
    have hE : Real.exp (2*κ*L) ≠ 0 := ne_of_gt (Real.exp_pos _)
    field_simp
    ring
  rw [hfinal]

#print axioms greenSqRemainderM_abs_le
#print axioms sinh_ge_exp_div_four
#print axioms greenSqRemainder_abs_le

end RHFormalization
