-- SENTINEL: R4-v2
import RHFormalization.GalerkinSpikeDefectSplit
import Mathlib

/-!
# Harmonic (t-free) bound on the sin-correction sum (defect-gate R4)

The banked `abs_spikeSinSum_le` gives an N-free bound with a
`(1 − e^{−t(π/L)²})⁻¹` factor that blows up like `1/t` at `t → 0`.
This brick gives the complementary small-`t` bound: modewise
`e^{−tλ_m} ≤ 1` and `|sin| ≤ 1` yield

  `|spikeSinSum N L t a| ≤ (1/π)·(1 + log N)`

— t-free and only logarithmic in `N`, so in the gate's weighted stage sum
the E_sin contribution is `mass·(1 + log N_n)/(2L_n) → 0` with room to
spare (`L_n ≥ (n+2)³`). Transfer from Mathlib's ℚ-valued `harmonic` via
`harmonic_le_one_add_log`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- Real-valued harmonic-sum bound, transferred from `harmonic_le_one_add_log`. -/
theorem sum_inv_succ_le_one_add_log (N : ℕ) :
    ∑ i ∈ Finset.range N, (((i : ℝ)) + 1)⁻¹ ≤ 1 + Real.log N := by
  have hcast : ((harmonic N : ℚ) : ℝ)
      = ∑ i ∈ Finset.range N, (((i : ℝ)) + 1)⁻¹ := by
    unfold harmonic
    push_cast
    rfl
  have h := harmonic_le_one_add_log N
  rw [hcast] at h
  exact h

/-- Per-mode t-free sin bound: `|exp·sin/((m+1)π)| ≤ 1/((m+1)·π)`. -/
theorem abs_sinMode_le_inv (L t a : ℝ) (ht : 0 ≤ t) (m : Fin N) :
    |Real.exp (-(t * galerkinLam L (m : ℕ))) *
        (Real.sin (((m : ℝ) + 1) * Real.pi * a / L)
          / ((((m : ℝ)) + 1) * Real.pi))|
      ≤ ((((m : ℝ)) + 1) * Real.pi)⁻¹ := by
  have hlam : (0 : ℝ) ≤ galerkinLam L (m : ℕ) := by
    unfold galerkinLam
    positivity
  have hexp : Real.exp (-(t * galerkinLam L (m : ℕ))) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg ht hlam))
  have hm1pos : (0 : ℝ) < ((m : ℝ) + 1) * Real.pi := by positivity
  have hsin : |Real.sin (((m : ℝ) + 1) * Real.pi * a / L)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_div, abs_of_pos hm1pos]
  calc Real.exp (-(t * galerkinLam L (m : ℕ)))
        * (|Real.sin (((m : ℝ) + 1) * Real.pi * a / L)|
            / (((m : ℝ) + 1) * Real.pi))
      ≤ 1 * (1 / (((m : ℝ) + 1) * Real.pi)) := by
        gcongr
    _ = ((((m : ℝ)) + 1) * Real.pi)⁻¹ := by
        rw [one_mul, one_div]

/-- **E_sin, t-free form**: `|spikeSinSum| ≤ (1/π)·(1 + log N)`. -/
theorem abs_spikeSinSum_le_log (L t a : ℝ) (ht : 0 ≤ t) :
    |spikeSinSum N L t a| ≤ (1 / Real.pi) * (1 + Real.log N) := by
  unfold spikeSinSum
  have hstep1 : |∑ m : Fin N, Real.exp (-(t * galerkinLam L (m : ℕ))) *
        (Real.sin (((m : ℝ) + 1) * Real.pi * a / L)
          / ((((m : ℝ)) + 1) * Real.pi))|
      ≤ ∑ m : Fin N, ((((m : ℝ)) + 1) * Real.pi)⁻¹ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum fun m _ => abs_sinMode_le_inv L t a ht m
  have hstep2 : ∑ m : Fin N, ((((m : ℝ)) + 1) * Real.pi)⁻¹
      = (1 / Real.pi) * ∑ i ∈ Finset.range N, (((i : ℝ)) + 1)⁻¹ := by
    rw [Finset.mul_sum,
      ← Fin.sum_univ_eq_sum_range
        (fun i => (1 / Real.pi) * (((i : ℝ)) + 1)⁻¹) N]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_inv, one_div]
    ring
  have hstep3 : (1 / Real.pi) * ∑ i ∈ Finset.range N, (((i : ℝ)) + 1)⁻¹
      ≤ (1 / Real.pi) * (1 + Real.log N) := by
    refine mul_le_mul_of_nonneg_left (sum_inv_succ_le_one_add_log N) ?_
    positivity
  calc |∑ m : Fin N, Real.exp (-(t * galerkinLam L (m : ℕ))) *
        (Real.sin (((m : ℝ) + 1) * Real.pi * a / L)
          / ((((m : ℝ)) + 1) * Real.pi))|
      ≤ ∑ m : Fin N, ((((m : ℝ)) + 1) * Real.pi)⁻¹ := hstep1
    _ = (1 / Real.pi) * ∑ i ∈ Finset.range N, (((i : ℝ)) + 1)⁻¹ := hstep2
    _ ≤ (1 / Real.pi) * (1 + Real.log N) := hstep3

#print axioms sum_inv_succ_le_one_add_log
#print axioms abs_sinMode_le_inv
#print axioms abs_spikeSinSum_le_log

end

end RHFormalization
