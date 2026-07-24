-- SENTINEL: CXHYP-v3
import RHFormalization.CoshSinhRatioBound
import Mathlib

/-!
# ComplexHyperbolicBounds — lifting the real ratio bound to complex κ

GAP CLOSED: `cosh_div_sinh_le` (banked) is for REAL κ, but the application
needs κ = √(s+1/4) ∈ ℂ. The standard route:

  ‖cosh z‖ ≤ cosh (Re z)      (triangle inequality on (e^z + e^{-z})/2)
  ‖sinh z‖ ≥ sinh (Re z)      (reverse triangle)

so the complex ratio is dominated by the REAL ratio at Re κ, and the banked
`cosh_div_sinh_le` applies. Uses only `Complex.cosh_eq`, `Complex.sinh_eq`,
and `Complex.norm_exp` (all probe-confirmed in this pin).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace RHFormalization

/-- `‖cosh z‖ ≤ cosh (Re z)`. -/
theorem norm_cosh_le_cosh_re (z : ℂ) :
    ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  have hdef : Complex.cosh z = (Complex.exp z + Complex.exp (-z)) / 2 := by
    first
      | rfl
      | (unfold Complex.cosh; rfl)
      | simp [Complex.cosh]
  rw [hdef]
  have hnum : ‖Complex.exp z + Complex.exp (-z)‖
      ≤ ‖Complex.exp z‖ + ‖Complex.exp (-z)‖ := norm_add_le _ _
  have h1 : ‖Complex.exp z‖ = Real.exp z.re := Complex.norm_exp z
  have h2 : ‖Complex.exp (-z)‖ = Real.exp (-z.re) := by
    rw [Complex.norm_exp]
    try congr 1
    try simp
  rw [h1, h2] at hnum
  rw [norm_div]
  have hd : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [hd, Real.cosh_eq]
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  linarith

/-- `sinh (Re z) ≤ ‖sinh z‖`. -/
theorem sinh_re_le_norm_sinh (z : ℂ) :
    Real.sinh z.re ≤ ‖Complex.sinh z‖ := by
  have hdef : Complex.sinh z = (Complex.exp z - Complex.exp (-z)) / 2 := by
    first
      | rfl
      | (unfold Complex.sinh; rfl)
      | simp [Complex.sinh]
  rw [hdef]
  have h1 : ‖Complex.exp z‖ = Real.exp z.re := Complex.norm_exp z
  have h2 : ‖Complex.exp (-z)‖ = Real.exp (-z.re) := by
    rw [Complex.norm_exp]
    try congr 1
    try simp
  have hrev : ‖Complex.exp z‖ - ‖Complex.exp (-z)‖
      ≤ ‖Complex.exp z - Complex.exp (-z)‖ := by
    have := norm_sub_norm_le (Complex.exp z) (Complex.exp (-z))
    linarith
  rw [norm_div]
  have hd : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [hd, Real.sinh_eq]
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  rw [h1, h2] at hrev
  linarith

/-- **THE COMPLEX RATIO BOUND** — the banked real bound, at `Re κ`. -/
theorem complex_cosh_div_sinh_le (κ : ℂ) (L a : ℝ)
    (hκ : 0 < κ.re) (hL : 0 < L) (hκL : 1 ≤ κ.re * L)
    (ha0 : 0 ≤ a) (haL : a ≤ L) :
    ‖Complex.cosh (κ * ((L - a : ℝ) : ℂ))‖ / ‖Complex.sinh (κ * (L : ℂ))‖
      ≤ 4 * Real.exp (-(κ.re * a)) := by
  have hre1 : (κ * ((L - a : ℝ) : ℂ)).re = κ.re * (L - a) := by
    simp [Complex.mul_re]
  have hre2 : (κ * (L : ℂ)).re = κ.re * L := by
    simp [Complex.mul_re]
  have hnum : ‖Complex.cosh (κ * ((L - a : ℝ) : ℂ))‖
      ≤ Real.cosh (κ.re * (L - a)) := by
    have := norm_cosh_le_cosh_re (κ * ((L - a : ℝ) : ℂ))
    rwa [hre1] at this
  have hden : Real.sinh (κ.re * L) ≤ ‖Complex.sinh (κ * (L : ℂ))‖ := by
    have := sinh_re_le_norm_sinh (κ * (L : ℂ))
    rwa [hre2] at this
  have hspos : 0 < Real.sinh (κ.re * L) := by
    have hp : (0:ℝ) < κ.re * L := by positivity
    rw [Real.sinh_eq]
    have h1 : Real.exp (-(κ.re * L)) < Real.exp (κ.re * L) := by
      apply Real.exp_lt_exp.mpr; linarith
    linarith
  have hdenpos : 0 < ‖Complex.sinh (κ * (L : ℂ))‖ := lt_of_lt_of_le hspos hden
  have hreal := cosh_div_sinh_le κ.re L a hκ hL hκL ha0 haL
  rw [div_le_iff₀ hdenpos]
  have hstep : Real.cosh (κ.re * (L - a))
      ≤ 4 * Real.exp (-(κ.re * a)) * Real.sinh (κ.re * L) := by
    rw [div_le_iff₀ hspos] at hreal
    exact hreal
  have hEp : (0:ℝ) < Real.exp (-(κ.re * a)) := Real.exp_pos _
  calc ‖Complex.cosh (κ * ((L - a : ℝ) : ℂ))‖
      ≤ Real.cosh (κ.re * (L - a)) := hnum
    _ ≤ 4 * Real.exp (-(κ.re * a)) * Real.sinh (κ.re * L) := hstep
    _ ≤ 4 * Real.exp (-(κ.re * a)) * ‖Complex.sinh (κ * (L : ℂ))‖ := by
        have hc : (0:ℝ) ≤ 4 * Real.exp (-(κ.re * a)) := by positivity
        exact mul_le_mul_of_nonneg_left hden hc

#print axioms norm_cosh_le_cosh_re
#print axioms sinh_re_le_norm_sinh
#print axioms complex_cosh_div_sinh_le

end RHFormalization
