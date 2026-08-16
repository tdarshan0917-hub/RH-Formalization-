/-
STAGE B(i) — Brick 3: B4 spectral-weight export (GPT amendment).
Standalone: Σ_{k<N} (1 + λ_k)⁻¹ ≤ L/2, λ_k = galerkinLam L k = ((k+1)π/L)².
The donor's comparison is specialized to the squared-resolvent summand, so
the sum-vs-integral step is built fresh here (complete): antitone comparison
per block, adjacent-interval summation, arctan FTC, arctan < π/2.
Explicit constant L/2. No sorry.
-/

import RHFormalization.AdmissibleResolventWeightSum
import RHFormalization.DenseGalerkinSchedule

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 800000

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- The continuum comparator `g(x) = (1 + (πx/L)²)⁻¹`. -/
private def swInt (L : ℝ) (x : ℝ) : ℝ := ((1 : ℝ) + (Real.pi * x / L) ^ 2)⁻¹

theorem sum_inv_one_add_galerkinLam_le (N : ℕ) (L : ℝ) (hL : 0 < L) :
    (∑ m : Fin N, ((1 : ℝ) + galerkinLam L (m : ℕ))⁻¹) ≤ L / 2 := by
  have hLne : L ≠ 0 := hL.ne'
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  -- continuity + integrability of the comparator
  have hg_cont : Continuous (swInt L) := by
    unfold swInt
    have hne : ∀ x : ℝ, ((1 : ℝ) + (Real.pi * x / L) ^ 2) ≠ 0 := by
      intro x; positivity
    first
      | exact ((continuous_const.add
          (((continuous_const.mul continuous_id).div_const L).pow 2)).inv₀ hne)
      | fun_prop
  have hg_intble : ∀ a b : ℝ, IntervalIntegrable (swInt L) MeasureTheory.volume a b :=
    fun a b => hg_cont.intervalIntegrable a b
  -- summand = g(m+1)
  have hlam : ∀ m : Fin N, ((1 : ℝ) + galerkinLam L (m : ℕ))⁻¹
      = swInt L ((m : ℝ) + 1) := by
    intro m
    unfold galerkinLam swInt
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun m _ => hlam m), Fin.sum_univ_eq_sum_range]
  -- per-block: g(i+1) ≤ ∫_{i}^{i+1} g  (g antitone on [0,∞))
  have hstep : ∀ i ∈ Finset.range N,
      swInt L ((i : ℝ) + 1) ≤ ∫ x in (i : ℝ)..((i : ℝ) + 1), swInt L x := by
    intro i _
    have hi0 : (0:ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hconst : swInt L ((i : ℝ) + 1)
        = ∫ _x in (i : ℝ)..((i : ℝ) + 1), swInt L ((i : ℝ) + 1) := by
      rw [intervalIntegral.integral_const]
      simp
    rw [hconst]
    apply intervalIntegral.integral_mono_on (by linarith)
      (intervalIntegrable_const) (hg_intble _ _)
    intro x hx
    unfold swInt
    have hx1 : x ≤ (i : ℝ) + 1 := hx.2
    have hx0 : (0:ℝ) ≤ x := le_trans hi0 hx.1
    have hfrac : Real.pi * x / L ≤ Real.pi * ((i : ℝ) + 1) / L := by
      apply div_le_div_of_nonneg_right ?_ hL
      exact mul_le_mul_of_nonneg_left hx1 hπ.le
    have h0 : (0:ℝ) ≤ Real.pi * x / L := by positivity
    have hsq : (Real.pi * x / L) ^ 2 ≤ (Real.pi * ((i : ℝ) + 1) / L) ^ 2 := by
      nlinarith
    first
      | (apply inv_le_inv_of_le (by positivity); linarith)
      | (gcongr; linarith)
      | (apply one_div_le_one_div_of_le (by positivity) |>.mp; linarith)
  calc (∑ i ∈ Finset.range N, swInt L ((i : ℝ) + 1))
      ≤ ∑ i ∈ Finset.range N, ∫ x in (i : ℝ)..((i : ℝ) + 1), swInt L x :=
        Finset.sum_le_sum hstep
    _ = ∫ x in (0 : ℝ)..(N : ℝ), swInt L x := by
        have := intervalIntegral.sum_integral_adjacent_intervals
          (a := fun k : ℕ => (k : ℝ)) (f := swInt L) (n := N)
          (fun k _ => hg_intble _ _)
        first
          | (simpa using this)
          | (push_cast at this ⊢; simpa using this)
          | (convert this using 2 <;> push_cast <;> ring)
    _ ≤ L / 2 := by
        -- FTC with arctan antiderivative, then arctan < π/2
        have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (N : ℝ), HasDerivAt
            (fun t : ℝ => (L / Real.pi) * Real.arctan (Real.pi * t / L))
            (swInt L x) x := by
          intro x _
          have hd1 : HasDerivAt (fun t : ℝ => Real.pi * t / L)
              (Real.pi / L) x := by
            first
              | exact ((hasDerivAt_id x).const_mul Real.pi).div_const L
              | simpa using ((hasDerivAt_id x).const_mul Real.pi).div_const L
          have hd2 := hd1.arctan
          have hd3 := hd2.const_mul (L / Real.pi)
          convert hd3 using 1
          unfold swInt
          field_simp
        have hFTC : (∫ x in (0 : ℝ)..(N : ℝ), swInt L x)
            = (L / Real.pi) * Real.arctan (Real.pi * (N : ℝ) / L)
              - (L / Real.pi) * Real.arctan (Real.pi * 0 / L) :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hg_intble _ _)
        rw [hFTC]
        have hz : Real.arctan (Real.pi * 0 / L) = 0 := by
          norm_num
        rw [hz, mul_zero, sub_zero]
        have harc : Real.arctan (Real.pi * (N : ℝ) / L) ≤ Real.pi / 2 :=
          (Real.arctan_lt_pi_div_two _).le
        calc (L / Real.pi) * Real.arctan (Real.pi * (N : ℝ) / L)
            ≤ (L / Real.pi) * (Real.pi / 2) :=
              mul_le_mul_of_nonneg_left harc (by positivity)
          _ = L / 2 := by field_simp

/-- Dense-schedule instantiation: `Σ_{k<denseN} (1+λ_k)⁻¹ ≤ denseL/2`
with `λ_k = galerkinFreeMu` via the B(i)-1 pin. -/
theorem sum_inv_one_add_freeMu_dense_le (n : ℕ) :
    (∑ m : Fin (denseN n),
        ((1 : ℝ) + galerkinFreeMu (denseN n) (denseL n) m)⁻¹) ≤ denseL n / 2 := by
  have h := sum_inv_one_add_galerkinLam_le (denseN n) (denseL n) (denseL_pos n)
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rfl

#print axioms sum_inv_one_add_galerkinLam_le
#print axioms sum_inv_one_add_freeMu_dense_le

end

end RHFormalization
