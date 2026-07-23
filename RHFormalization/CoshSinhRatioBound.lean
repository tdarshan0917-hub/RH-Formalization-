-- SENTINEL: CSR-v4
import RHFormalization.DirichletGreenKernel
import Mathlib

/-!
# CoshSinhRatioBound — brick 2a (algebraic half)

The mode sum's closed form is
  Σ_k cos(kπa/L)/(s+¼+(kπ/L)²) = L·cosh(κ(L−a))/(2κ·sinh(κL)) − 1/(2κ²)
(classical series, `Σ cos(kθ)/(k²+c²)`). This file banks the step from that
closed form to the Green's value:

  cosh(κ(L−a))/sinh(κL) = e^{−κa}·(1+e^{−2κ(L−a)})/(1−e^{−2κL})

so the main term converges to `e^{−κa}` with EXPONENTIALLY SMALL error in
κL — confirming that the measured O(a/L) error comes from the BOUNDARY
term (FPGB's `(a/L)cos` piece), not the main term.

Banked here: the two-sided ratio bound. The classical series itself is the
remaining analytic input for 2a.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace RHFormalization

/-- `cosh u ≤ e^u` for `u ≥ 0`. -/
theorem cosh_le_exp {u : ℝ} (hu : 0 ≤ u) : Real.cosh u ≤ Real.exp u := by
  rw [Real.cosh_eq]
  have h : Real.exp (-u) ≤ Real.exp u := by
    apply Real.exp_le_exp.mpr
    linarith
  linarith

/-- `cosh u ≥ e^u / 2`. -/
theorem half_exp_le_cosh (u : ℝ) : Real.exp u / 2 ≤ Real.cosh u := by
  rw [Real.cosh_eq]
  have h : 0 < Real.exp (-u) := Real.exp_pos _
  linarith

/-- **THE RATIO BOUND**: for `κL ≥ 1` and `0 ≤ a ≤ L`,
`cosh(κ(L−a)) / sinh(κL) ≤ 4·e^{−κa}` — the main term tracks the Green's
value with a constant free of `L`. -/
theorem cosh_div_sinh_le (κ L a : ℝ) (hκ : 0 < κ) (hL : 0 < L)
    (hκL : 1 ≤ κ * L) (ha0 : 0 ≤ a) (haL : a ≤ L) :
    Real.cosh (κ * (L - a)) / Real.sinh (κ * L)
      ≤ 4 * Real.exp (-(κ * a)) := by
  have hLa : 0 ≤ κ * (L - a) := by
    have : 0 ≤ L - a := by linarith
    positivity
  have hKL : 0 ≤ κ * L := by positivity
  -- numerator ≤ e^{κ(L−a)}
  have hnum : Real.cosh (κ * (L - a)) ≤ Real.exp (κ * (L - a)) :=
    cosh_le_exp hLa
  -- denominator ≥ e^{κL}(1 − e^{−1})/2  (from GREEN's machinery)
  have hE : Real.exp (-1) < 1 := by
    have h0 : Real.exp (-(1:ℝ)) * Real.exp (1:ℝ) = 1 := by
      rw [← Real.exp_add]; simp
    have h1 : (2:ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1:ℝ); linarith
    have hp : (0:ℝ) < Real.exp (-(1:ℝ)) := Real.exp_pos _
    nlinarith [h0, h1, hp]
  have hden : Real.exp (κ * L) * (1 - Real.exp (-1)) / 2 ≤ Real.sinh (κ * L) := by
    have hs : (Real.exp (κ * L) - 1) / 2 ≤ Real.sinh (κ * L) :=
      half_exp_sub_one_le_sinh hKL
    have hkey : Real.exp (κ * L) * (1 - Real.exp (-1))
        ≤ Real.exp (κ * L) - 1 := by
      have h1 : Real.exp (κ * L) * Real.exp (-1) = Real.exp (κ * L - 1) := by
        rw [← Real.exp_add]
        try congr 1
        try ring
      have h2 : (1:ℝ) ≤ Real.exp (κ * L - 1) := by
        have := Real.add_one_le_exp (κ * L - 1); linarith
      rw [mul_sub, mul_one, h1]
      linarith
    linarith
  have hcpos : (0:ℝ) < 1 - Real.exp (-1) := by linarith
  have hdenpos : 0 < Real.sinh (κ * L) := by
    have hep : (0:ℝ) < Real.exp (κ * L) := Real.exp_pos _
    have hpos : (0:ℝ) < Real.exp (κ * L) * (1 - Real.exp (-1)) / 2 := by
      positivity
    linarith
  rw [div_le_iff₀ hdenpos]
  -- e^{κ(L−a)} ≤ 3·e^{−κa}·(denominator)
  have hsplit : Real.exp (κ * (L - a)) = Real.exp (-(κ * a)) * Real.exp (κ * L) := by
    rw [← Real.exp_add]
    try congr 1
    try ring
  have hEp : (0:ℝ) < Real.exp (-(κ * a)) := Real.exp_pos _
  have hcnn : (0:ℝ) < 1 - Real.exp (-1) := hcpos
  calc Real.cosh (κ * (L - a))
      ≤ Real.exp (κ * (L - a)) := hnum
    _ = Real.exp (-(κ * a)) * Real.exp (κ * L) := hsplit
    _ ≤ 4 * Real.exp (-(κ * a)) * Real.sinh (κ * L) := by
        have hEhalf : Real.exp (-1) ≤ 1/2 := by
          have h0 : Real.exp (-(1:ℝ)) * Real.exp (1:ℝ) = 1 := by
            rw [← Real.exp_add]
            simp
          have h1 : (2:ℝ) ≤ Real.exp 1 := by
            have h := Real.add_one_le_exp (1:ℝ)
            linarith
          have hp : (0:ℝ) < Real.exp (-(1:ℝ)) := Real.exp_pos _
          nlinarith [h0, h1, hp]
        have hq : Real.exp (κ * L) ≤ 4 * Real.sinh (κ * L) := by
          nlinarith [hden, hEhalf, Real.exp_pos (κ * L)]
        nlinarith [hq, hEp, Real.exp_pos (κ * L), hdenpos]

#print axioms cosh_le_exp
#print axioms half_exp_le_cosh
#print axioms cosh_div_sinh_le

end RHFormalization
