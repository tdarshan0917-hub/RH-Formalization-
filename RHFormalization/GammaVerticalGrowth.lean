import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Brick 1 (foundation of Pillar 2): vertical growth of the Gamma function

GOAL of this file (the full brick, not yet complete): a bound of the form
`‖Complex.Gamma (σ + I*t)‖ ≤ C(σ) * |t|^(σ - 1/2) * Real.exp (-π/2 * |t|)`
for `|t|` large — the complex Stirling / Binet asymptotic up vertical lines.
This is the bottom stone of the zero-counting bound and is NOT in Mathlib.

This file begins it with the recurrence-shift fragment, which is exact and
axiom-clean, and is the algebraic backbone of the eventual asymptotic.
-/

namespace RHFormalization
open Complex

/-- **Brick 1, fragment 1 — the recurrence-shift identity for the norm.**
From Euler's `Γ(s+1) = s·Γ(s)`, the norm satisfies `‖Γ(s+1)‖ = ‖s‖·‖Γ(s)‖`.
This is the exact step that lets a vertical-line bound be propagated between
adjacent strips `Re s ∈ [σ, σ+1]`, the engine of the eventual Stirling estimate. -/
theorem norm_Gamma_add_one (s : ℂ) (hs : s ≠ 0) :
    ‖Complex.Gamma (s + 1)‖ = ‖s‖ * ‖Complex.Gamma s‖ := by
  rw [Complex.Gamma_add_one s hs, norm_mul]

#print axioms norm_Gamma_add_one

/-- **Brick 1, fragment 2 — the reflection identity on the half-line.**
On the critical line `z = 1/2 + I*t`, Euler reflection collapses to a closed form:
`Γ(1/2+it) · Γ(1/2-it) = π / sin(π(1/2+it))`.
Since `1/2 - it = 1 - (1/2 + it)`, this is the exact handle for `|Γ(1/2+it)|`,
the seed of the vertical-growth estimate (no Stirling required for this line). -/
theorem Gamma_reflect_half_line (t : ℝ) :
    Complex.Gamma (1/2 + Complex.I * t) * Complex.Gamma (1/2 - Complex.I * t)
      = (Real.pi : ℂ) / Complex.sin (Real.pi * (1/2 + Complex.I * t)) := by
  have h := Complex.Gamma_mul_Gamma_one_sub (1/2 + Complex.I * t)
  have he : (1 : ℂ) - (1/2 + Complex.I * t) = 1/2 - Complex.I * t := by ring
  rw [he] at h
  exact h

#print axioms Gamma_reflect_half_line

/-- **Brick 1, fragment 3 — closed form for the Gamma norm on the critical line.**
`‖Γ(1/2+it)‖² = π / cosh(π t)`, exact (no Stirling). From reflection + `Γ(1/2-it)=conj Γ(1/2+it)`
and `sin(π(1/2+it)) = cosh(π t)`. This is the seed vertical bound: the RHS decays like
`e^(-π|t|)`, giving `‖Γ(1/2+it)‖` exponential decay up the critical line. -/
theorem norm_Gamma_half_line_sq (t : ℝ) :
    ‖Complex.Gamma (1/2 + Complex.I * t)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  have hconj : (1/2 : ℂ) - Complex.I * t = (starRingEnd ℂ) (1/2 + Complex.I * t) := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have hG2 : Complex.Gamma (1/2 - Complex.I * t)
      = (starRingEnd ℂ) (Complex.Gamma (1/2 + Complex.I * t)) := by
    rw [hconj, Complex.Gamma_conj]
  -- sin(π(1/2+it)) = cosh(π t) as a complex number
  have hsin : Complex.sin (Real.pi * (1/2 + Complex.I * t)) = (Real.cosh (Real.pi * t) : ℂ) := by
    have hrw : (Real.pi : ℂ) * (1/2 + Complex.I * t)
        = (Real.pi * t : ℝ) * Complex.I + Real.pi / 2 := by
      push_cast; ring
    rw [hrw, Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
  -- start from reflection, take norms
  have href := Gamma_reflect_half_line t
  rw [hG2, hsin] at href
  have hcosh_pos : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  -- ‖Γ · conj Γ‖ = ‖Γ‖²
  have hL : ‖Complex.Gamma (1/2 + Complex.I * t)
        * (starRingEnd ℂ) (Complex.Gamma (1/2 + Complex.I * t))‖
      = ‖Complex.Gamma (1/2 + Complex.I * t)‖ ^ 2 := by
    rw [norm_mul, RCLike.norm_conj]; ring
  have hR : ‖(Real.pi : ℂ) / (Real.cosh (Real.pi * t) : ℂ)‖
      = Real.pi / Real.cosh (Real.pi * t) := by
    rw [norm_div, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg hcosh_pos.le]
  have := congrArg norm href
  rw [hL, hR] at this
  exact this

#print axioms norm_Gamma_half_line_sq

/-- `cosh x ≥ (1/2) exp|x|`: half of one exponential term lower-bounds cosh. -/
theorem cosh_ge_half_exp_abs (x : ℝ) :
    (1/2 : ℝ) * Real.exp |x| ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  rcases abs_cases x with ⟨hx, _⟩ | ⟨hx, _⟩
  · rw [hx]
    have h2 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
    have : (1/2 : ℝ) * Real.exp x ≤ (Real.exp x + Real.exp (-x)) / 2 := by linarith
    linarith [this]
  · rw [hx]
    have h2 : 0 ≤ Real.exp x := (Real.exp_pos _).le
    have : (1/2 : ℝ) * Real.exp (-x) ≤ (Real.exp x + Real.exp (-x)) / 2 := by linarith
    linarith [this]

/-- **Brick 1, fragment 4 — squared exponential decay of Gamma on the critical line.**
`‖Γ(1/2+it)‖² ≤ 2π · exp(-π|t|)`. The genuine vertical decay bound (no Stirling), the
direct input to the zeta strip-growth estimate. -/
theorem norm_Gamma_half_line_sq_le (t : ℝ) :
    ‖Complex.Gamma (1/2 + Complex.I * t)‖ ^ 2
      ≤ 2 * Real.pi * Real.exp (-(Real.pi * |t|)) := by
  rw [norm_Gamma_half_line_sq]
  have hcosh : (1/2 : ℝ) * Real.exp |Real.pi * t| ≤ Real.cosh (Real.pi * t) :=
    cosh_ge_half_exp_abs _
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have habs : |Real.pi * t| = Real.pi * |t| := by
    rw [abs_mul, abs_of_nonneg hpi.le]
  rw [habs] at hcosh
  have hcosh_pos : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hexp_pos : 0 < Real.exp (Real.pi * |t|) := Real.exp_pos _
  -- π / cosh ≤ π / ((1/2) exp(π|t|)) = 2π exp(-π|t|)
  have hstep : Real.pi / Real.cosh (Real.pi * t)
      ≤ Real.pi / ((1/2) * Real.exp (Real.pi * |t|)) := by
    apply div_le_div_of_nonneg_left hpi.le _ hcosh
    positivity
  refine hstep.trans (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp

#print axioms cosh_ge_half_exp_abs
#print axioms norm_Gamma_half_line_sq_le


end RHFormalization
