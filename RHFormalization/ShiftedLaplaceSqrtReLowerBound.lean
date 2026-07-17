import RHFormalization.ShiftedLaplaceBranchRange
import RHFormalization.ShiftedLaplaceBridge
import Mathlib

/-!
# Square-root real-part lower bound

`Re(√w) ≥ √(Re w)` for the principal branch, proved without the arg/half-angle
formula: from `(√w)² = w` and `Re(v²) = Re(v)² - Im(v)² ≤ Re(v)²` with
`Re(√w) ≥ 0`.

Consequence: `RightHalfPlane σ ⊆ {Re(√(s+¼)) > 1}` for `σ > 3/4`.
-/

namespace RHFormalization

open Complex Real

/-- `(√w)² = w`. -/
theorem sq_sqrt_eq (w : ℂ) : (Complex.sqrt w) ^ 2 = w := by
  unfold Complex.sqrt
  exact Complex.cpow_nat_inv_pow _ (by norm_num)

/-- Real-part lower bound: `Re(√w) ≥ √(Re w)`. -/
theorem sqrt_re_ge_sqrt_re (w : ℂ) :
    Real.sqrt w.re ≤ (Complex.sqrt w).re := by
  set v : ℂ := Complex.sqrt w with hv
  have hv_nonneg : 0 ≤ v.re := sqrt_re_nonneg w
  have hsq : v ^ 2 = w := sq_sqrt_eq w
  -- Re w = Re(v^2) = v.re^2 - v.im^2 ≤ v.re^2
  have hre_w : w.re = v.re ^ 2 - v.im ^ 2 := by
    have : w.re = (v ^ 2).re := by rw [hsq]
    rw [this]
    simp [pow_two, Complex.mul_re]
  have hle : w.re ≤ v.re ^ 2 := by
    rw [hre_w]; nlinarith [sq_nonneg v.im]
  -- √(Re w) ≤ √(v.re^2) = |v.re| = v.re
  calc Real.sqrt w.re
      ≤ Real.sqrt (v.re ^ 2) := Real.sqrt_le_sqrt hle
    _ = |v.re| := by rw [Real.sqrt_sq_eq_abs]
    _ = v.re := abs_of_nonneg hv_nonneg

/-- For real cutoff `σ`, if `Re(s) > σ` then `Re(√(s+¼)) ≥ √(σ + ¼)`. -/
theorem sqrt_shift_re_ge {s : ℂ} {σ : ℝ} (hs : σ < s.re) :
    Real.sqrt (σ + 1/4) ≤ (Complex.sqrt (s + (1/4:ℂ))).re := by
  have hstep := sqrt_re_ge_sqrt_re (s + (1/4:ℂ))
  have hre : (s + (1/4:ℂ)).re = s.re + 1/4 := by
    rw [Complex.add_re]; norm_num
  rw [hre] at hstep
  have hmono : Real.sqrt (σ + 1/4) ≤ Real.sqrt (s.re + 1/4) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

/-- **Containment.** For `σ > 3/4`, `RightHalfPlane σ ⊆ shiftedLaplaceAbsConvRegion`. -/
theorem rightHalfPlane_subset_absConvRegion {σ : ℝ} (hσ : 3/4 < σ) :
    RightHalfPlane σ ⊆ shiftedLaplaceAbsConvRegion := by
  intro s hs
  have hsre : σ < s.re := hs
  have hbound := sqrt_shift_re_ge hsre
  -- need: 1 < (√(s+¼) + ½).re, i.e. Re(√(s+¼)) > 1/2... actually piece2: (√+½).re > 1
  rw [absConvRegion_eq_piece2]
  rw [Complex.add_re]
  have h12 : ((1/2:ℂ)).re = (1/2:ℝ) := by norm_num
  rw [h12]
  -- need √(σ+¼) > 1/2 (then + 1/2 > 1). Since σ > 3/4, σ+¼ > 1, so √(σ+¼) > √1 = 1 > 1/2.
  have hone_lt : (1:ℝ) < Real.sqrt (σ + 1/4) := by
    have h1 : (1:ℝ) < σ + 1/4 := by linarith
    have : Real.sqrt 1 < Real.sqrt (σ + 1/4) := Real.sqrt_lt_sqrt (by norm_num) h1
    rwa [Real.sqrt_one] at this
  linarith [hbound, hone_lt]

/-- **Specialization to σ = 1** (GPT-requested name): the raw right half-plane
`Re(s) > 1` sits inside the shifted-Laplace absolute-convergence region. -/
theorem rightHalfPlane_one_subset_shiftedLaplaceAbsConvRegion :
    RightHalfPlane 1 ⊆ shiftedLaplaceAbsConvRegion :=
  rightHalfPlane_subset_absConvRegion (by norm_num)

#print axioms rightHalfPlane_subset_absConvRegion
#print axioms rightHalfPlane_one_subset_shiftedLaplaceAbsConvRegion
