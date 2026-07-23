-- SENTINEL: GREEN-v11
import Mathlib

/-!
# DirichletGreenKernel — D.LOC-1 stone 1: the position-space resolvent kernel

`G_L(x,y;κ) = sinh(κ·min(x,y))·sinh(κ·(L−max(x,y))) / (κ·sinh(κL))`
is the Dirichlet resolvent kernel for `−d²/dx² + κ²` on `[0,L]`.

THE POINT: `|G_L(x,y;κ)| ≤ e^{−κ|x−y|}/(2κ)` UNIFORMLY IN L. That
L-freeness is what the spectral/entrywise route lacked — PREM's bound grew
like L (measured ratio 202→980→3967→15166) while the true remainder decays
(0.794→0.031). The decay below is the mechanism that sees the cancellation.

Real κ > 0 here (the case needed on Ω-compacts after the shift).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace RHFormalization

open Real

/-- The Dirichlet Green's function on `[0,L]` for `−d²/dx² + κ²`. -/
noncomputable def dirichletGreen (L κ x y : ℝ) : ℝ :=
  Real.sinh (κ * min x y) * Real.sinh (κ * (L - max x y))
    / (κ * Real.sinh (κ * L))

/-- Symmetry in the two position arguments. -/
theorem dirichletGreen_symm (L κ x y : ℝ) :
    dirichletGreen L κ x y = dirichletGreen L κ y x := by
  unfold dirichletGreen
  rw [min_comm, max_comm]

/-- Nonnegativity on the box, for `κ > 0`. -/
theorem dirichletGreen_nonneg (L κ x y : ℝ) (hκ : 0 < κ) (hL : 0 < L)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxL : x ≤ L) (hyL : y ≤ L) :
    0 ≤ dirichletGreen L κ x y := by
  unfold dirichletGreen
  have hmin : 0 ≤ min x y := le_min hx hy
  have hmax : max x y ≤ L := max_le hxL hyL
  have hmin0 : 0 ≤ κ * min x y := by positivity
  have hmax0 : 0 ≤ κ * (L - max x y) := by
    have : 0 ≤ L - max x y := by linarith
    positivity
  have hL0 : 0 < κ * L := by positivity
  have h1 : 0 ≤ Real.sinh (κ * min x y) := by
    first
      | exact Real.sinh_nonneg_iff.mpr hmin0
      | exact (Real.sinh_nonneg _).mpr hmin0
      | (rw [Real.sinh_eq]
         have := Real.exp_le_exp.mpr (neg_nonpos.mpr hmin0)
         linarith [Real.exp_pos (κ * min x y), Real.exp_pos (-(κ * min x y))])
  have h2 : 0 ≤ Real.sinh (κ * (L - max x y)) := by
    first
      | exact Real.sinh_nonneg_iff.mpr hmax0
      | exact (Real.sinh_nonneg _).mpr hmax0
      | (rw [Real.sinh_eq]
         have := Real.exp_le_exp.mpr (neg_nonpos.mpr hmax0)
         linarith [Real.exp_pos (κ * (L - max x y)), Real.exp_pos (-(κ * (L - max x y)))])
  have h3 : 0 < Real.sinh (κ * L) := by
    first
      | exact Real.sinh_pos_iff.mpr hL0
      | exact (Real.sinh_pos _).mpr hL0
      | (rw [Real.sinh_eq]
         have hlt := Real.exp_lt_exp.mpr (neg_lt_self hL0)
         linarith)
  have h4 : 0 < κ * Real.sinh (κ * L) := mul_pos hκ h3
  exact div_nonneg (mul_nonneg h1 h2) h4.le

/-- Upper bound: `sinh a ≤ e^a / 2` for all real `a`. -/
theorem sinh_le_half_exp (a : ℝ) : Real.sinh a ≤ Real.exp a / 2 := by
  rw [Real.sinh_eq]
  have h : 0 < Real.exp (-a) := Real.exp_pos _
  linarith

/-- Lower bound: `e^a / 2 - 1 / 2 ≤ sinh a` (since `e^{-a} ≤ 1` for `a ≥ 0`). -/
theorem half_exp_sub_le_sinh {a : ℝ} (ha : 0 ≤ a) :
    Real.exp a / 2 - 1 / 2 ≤ Real.sinh a := by
  rw [Real.sinh_eq]
  have h : Real.exp (-a) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  linarith

/-- Nonnegativity of `sinh` on nonnegatives. -/
theorem sinh_nonneg_of_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ Real.sinh a := by
  rw [Real.sinh_eq]
  have h : Real.exp (-a) ≤ Real.exp a := by
    apply Real.exp_le_exp.mpr
    linarith
  linarith

/-- **DECAY, product form.** The numerator of `G` is bounded by
`e^{κ(u+v)}/4` where `u = min`, `v = L − max`; since
`κL = κu + κ|x−y| + κv`, this is `e^{κL}·e^{−κ|x−y|}/4`. -/
theorem dirichletGreen_numerator_le (L κ x y : ℝ) (hκ : 0 < κ) (hL : 0 < L)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxL : x ≤ L) (hyL : y ≤ L) :
    Real.sinh (κ * min x y) * Real.sinh (κ * (L - max x y))
      ≤ Real.exp (κ * L) * Real.exp (-(κ * |x - y|)) / 4 := by
  have hu0 : 0 ≤ κ * min x y := by
    have : 0 ≤ min x y := le_min hx hy
    positivity
  have hv0 : 0 ≤ κ * (L - max x y) := by
    have : 0 ≤ L - max x y := by
      have := max_le hxL hyL; linarith
    positivity
  have hd : |x - y| = max x y - min x y := by
    rcases le_total x y with h | h
    · rw [abs_of_nonpos (by linarith), min_eq_left h, max_eq_right h]
      try ring
    · rw [abs_of_nonneg (by linarith), min_eq_right h, max_eq_left h]
      try ring
  have hexp : Real.exp (κ * min x y) * Real.exp (κ * (L - max x y))
      = Real.exp (κ * L) * Real.exp (-(κ * |x - y|)) := by
    rw [← Real.exp_add, ← Real.exp_add, hd]
    congr 1
    ring
  calc Real.sinh (κ * min x y) * Real.sinh (κ * (L - max x y))
      ≤ (Real.exp (κ * min x y) / 2) * (Real.exp (κ * (L - max x y)) / 2) := by
        have hA : Real.sinh (κ * min x y) ≤ Real.exp (κ * min x y) / 2 :=
          sinh_le_half_exp _
        have hB : Real.sinh (κ * (L - max x y))
            ≤ Real.exp (κ * (L - max x y)) / 2 := sinh_le_half_exp _
        have hBnn : 0 ≤ Real.sinh (κ * (L - max x y)) :=
          sinh_nonneg_of_nonneg hv0
        have hEnn : (0:ℝ) ≤ Real.exp (κ * min x y) / 2 := by positivity
        exact mul_le_mul hA hB hBnn hEnn
    _ = (Real.exp (κ * min x y) * Real.exp (κ * (L - max x y))) / 4 := by ring
    _ = Real.exp (κ * L) * Real.exp (-(κ * |x - y|)) / 4 := by rw [hexp]

/-- Lower bound on the denominator: `sinh(κL) ≥ (e^{κL} − 1)/2`. -/
theorem half_exp_sub_one_le_sinh {a : ℝ} (ha : 0 ≤ a) :
    (Real.exp a - 1) / 2 ≤ Real.sinh a := by
  rw [Real.sinh_eq]
  have h : Real.exp (-a) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  linarith

/-- **THE DECAY BOUND.** For `κL ≥ 1`, the Green kernel decays like
`e^{−κ|x−y|}` with a constant free of `L` — the property the spectral
route could not see. -/
theorem dirichletGreen_decay (L κ x y : ℝ) (hκ : 0 < κ) (hL : 0 < L)
    (hκL : 1 ≤ κ * L)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxL : x ≤ L) (hyL : y ≤ L) :
    dirichletGreen L κ x y
      ≤ Real.exp (-(κ * |x - y|)) / (2 * κ * (1 - Real.exp (-1))) := by
  have hL0 : (0:ℝ) ≤ κ * L := by positivity
  -- constant 1 - e^{-1} > 0
  have hE : Real.exp (-1) < 1 := by
    have h0 : Real.exp (-(1:ℝ)) * Real.exp (1:ℝ) = 1 := by
      rw [← Real.exp_add]
      simp
    have h1 : (2:ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1:ℝ)
      linarith
    have hp : (0:ℝ) < Real.exp (-(1:ℝ)) := Real.exp_pos _
    nlinarith [h0, h1, hp]
  have hEnn : (0:ℝ) < 1 - Real.exp (-1) := by linarith
  -- denominator lower bound: sinh(κL) ≥ e^{κL}(1 - e^{-1})/2
  have hden : Real.exp (κ * L) * (1 - Real.exp (-1)) / 2 ≤ Real.sinh (κ * L) := by
    have hs : (Real.exp (κ * L) - 1) / 2 ≤ Real.sinh (κ * L) :=
      half_exp_sub_one_le_sinh hL0
    have hkey : Real.exp (κ * L) * (1 - Real.exp (-1)) ≤ Real.exp (κ * L) - 1 := by
      have h1 : Real.exp (κ * L) * Real.exp (-1) = Real.exp (κ * L - 1) := by
        rw [← Real.exp_add]
        try congr 1
        try ring
      have h2 : (1:ℝ) ≤ Real.exp (κ * L - 1) := by
        have := Real.add_one_le_exp (κ * L - 1); linarith
      rw [mul_sub, mul_one, h1]
      linarith
    linarith
  have hdenpos : 0 < Real.sinh (κ * L) := by
    have hpos : (0:ℝ) < Real.exp (κ * L) * (1 - Real.exp (-1)) / 2 := by
      have := Real.exp_pos (κ * L); positivity
    linarith
  have hnum := dirichletGreen_numerator_le L κ x y hκ hL hx hy hxL hyL
  have hnumnn : 0 ≤ Real.sinh (κ * min x y) * Real.sinh (κ * (L - max x y)) := by
    have hu0 : 0 ≤ κ * min x y := by
      have : 0 ≤ min x y := le_min hx hy
      positivity
    have hv0 : 0 ≤ κ * (L - max x y) := by
      have : 0 ≤ L - max x y := by
        have := max_le hxL hyL; linarith
      positivity
    exact mul_nonneg (sinh_nonneg_of_nonneg hu0) (sinh_nonneg_of_nonneg hv0)
  unfold dirichletGreen
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- goal: sinh·sinh * (2κ(1-e^{-1})) ≤ e^{-κ|x-y|} * (κ sinh(κL))
  have hEpos : (0:ℝ) < Real.exp (-(κ * |x - y|)) := Real.exp_pos _
  have hcnn : (0:ℝ) ≤ 2 * κ * (1 - Real.exp (-1)) := by positivity
  have hknn : (0:ℝ) ≤ Real.exp (-(κ * |x - y|)) * κ := by positivity
  calc Real.sinh (κ * min x y) * Real.sinh (κ * (L - max x y))
        * (2 * κ * (1 - Real.exp (-1)))
      ≤ (Real.exp (κ * L) * Real.exp (-(κ * |x - y|)) / 4)
          * (2 * κ * (1 - Real.exp (-1))) :=
        mul_le_mul_of_nonneg_right hnum hcnn
    _ = (Real.exp (-(κ * |x - y|)) * κ)
          * (Real.exp (κ * L) * (1 - Real.exp (-1)) / 2) := by ring
    _ ≤ (Real.exp (-(κ * |x - y|)) * κ) * Real.sinh (κ * L) :=
        mul_le_mul_of_nonneg_left hden hknn
    _ = Real.exp (-(κ * |x - y|)) * (κ * Real.sinh (κ * L)) := by ring

#print axioms sinh_le_half_exp
#print axioms sinh_nonneg_of_nonneg
#print axioms dirichletGreen_numerator_le
#print axioms half_exp_sub_one_le_sinh
#print axioms dirichletGreen_decay
#print axioms dirichletGreen_symm
#print axioms dirichletGreen_nonneg

end RHFormalization
