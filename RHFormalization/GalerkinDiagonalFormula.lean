import RHFormalization.GalerkinSpikeTailBound
import Mathlib

/-!
# Exact diagonal formula — G3-i of the defect gate
SENTINEL: diag-formula-v4

ROUTE CARD
1. `galerkinT_diag_formula`: for `0 ≤ a ≤ L`, the diagonal is EXACTLY
   `(1−a/L)·cos(kπa/L) + sin(kπa/L)/(kπ)`, `k = m+1`.
2. v4: file deleted before write (v3 was a corrupted merge — duplicate
   declarations); `split_ifs` for the Icc-membership if; derivative via
   `HasDerivAt.sin`; pin lemma `Real.sin_nat_mul_two_pi_sub`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- Product-to-sum. -/
theorem sinProdToSum_diag (A B : ℝ) :
    Real.sin A * Real.sin B = (Real.cos (A - B) - Real.cos (A + B)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- FTC for a linear-argument cosine. -/
theorem integral_cos_linear (c d A B : ℝ) (hc : c ≠ 0) :
    (∫ x in A..B, Real.cos (c * x + d))
      = (Real.sin (c * B + d) - Real.sin (c * A + d)) / c := by
  have hderiv : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun y : ℝ => Real.sin (c * y + d) / c)
        (Real.cos (c * x + d)) x := by
    intro x _
    have hlin : HasDerivAt (fun y : ℝ => c * y + d) c x := by
      simpa using ((hasDerivAt_id x).const_mul c).add_const d
    have hsin : HasDerivAt (fun y : ℝ => Real.sin (c * y + d))
        (Real.cos (c * x + d) * c) x := hlin.sin
    have h2 := hsin.div_const c
    have h3 : Real.cos (c * x + d) * c / c = Real.cos (c * x + d) := by
      field_simp
    rwa [h3] at h2
  have hint : IntervalIntegrable (fun x : ℝ => Real.cos (c * x + d))
      MeasureTheory.volume A B := by
    apply Continuous.intervalIntegrable
    continuity
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  ring

/-- **G3-i — exact diagonal at the bare level**: for `0 ≤ a ≤ L`, `k ≠ 0`,
`∫₀ᴸ φ_k(x)·φ_k^w(x−a) dx = (L−a)/2·cos(kπa/L) + L/(2kπ)·sin(kπa/L)`. -/
theorem TmatrixElement_diag_eval (L a : ℝ) (hL : 0 < L)
    (ha0 : 0 ≤ a) (haL : a ≤ L) (k : ℕ) (hk : k ≠ 0) :
    TmatrixElement L a k k
      = (L - a) / 2 * Real.cos ((k : ℝ) * Real.pi * a / L)
        + L / (2 * (k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * a / L) := by
  have hkR : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hpi := Real.pi_ne_zero
  unfold TmatrixElement
  set f : ℝ → ℝ :=
    fun x => dirichletEigenfun k L x * dirichletEigenfunWindowed k L (x - a)
    with hf
  have hEq1 : Set.EqOn f (fun _ => (0 : ℝ)) (Set.uIcc 0 a) := by
    intro x hx
    rw [Set.uIcc_of_le ha0] at hx
    rw [hf]
    simp only
    unfold dirichletEigenfunWindowed
    split_ifs with h
    · have hxa : x - a = 0 := by
        have h1 : 0 ≤ x - a := by
          first
            | exact h.1
            | simpa using (Set.mem_Icc.mp h).1
        have h2 : x - a ≤ 0 := by linarith [hx.2]
        linarith
      rw [hxa]
      unfold dirichletEigenfun
      simp
    · rw [mul_zero]
  have hEq2 : Set.EqOn f
      (fun x => dirichletEigenfun k L x * dirichletEigenfun k L (x - a))
      (Set.uIcc a L) := by
    intro x hx
    rw [Set.uIcc_of_le haL] at hx
    rw [hf]
    simp only
    unfold dirichletEigenfunWindowed
    split_ifs with h
    · rfl
    · exfalso
      apply h
      first
        | exact ⟨by linarith [hx.1], by linarith [hx.2, ha0]⟩
        | (rw [Set.mem_Icc]
           exact ⟨by linarith [hx.1], by linarith [hx.2, ha0]⟩)
  have hcont : Continuous
      (fun x => dirichletEigenfun k L x * dirichletEigenfun k L (x - a)) := by
    unfold dirichletEigenfun
    continuity
  have hi1 : IntervalIntegrable f MeasureTheory.volume 0 a := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.congr hEq1
  have hi2 : IntervalIntegrable f MeasureTheory.volume a L := by
    apply ContinuousOn.intervalIntegrable
    exact hcont.continuousOn.congr hEq2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  rw [← hsplit]
  have hv1 : (∫ x in (0:ℝ)..a, f x) = 0 := by
    rw [intervalIntegral.integral_congr hEq1]
    simp
  have hv2 : (∫ x in a..L, f x)
      = (L - a) / 2 * Real.cos ((k : ℝ) * Real.pi * a / L)
        + L / (2 * (k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * a / L) := by
    rw [intervalIntegral.integral_congr hEq2]
    unfold dirichletEigenfun
    have hrw : ∀ x : ℝ,
        Real.sin ((k : ℝ) * Real.pi * x / L)
          * Real.sin ((k : ℝ) * Real.pi * (x - a) / L)
        = (Real.cos ((k : ℝ) * Real.pi * a / L)
            - Real.cos ((2 * (k : ℝ) * Real.pi / L) * x
                + (-((k : ℝ) * Real.pi * a / L)))) / 2 := by
      intro x
      rw [sinProdToSum_diag]
      congr 2
      · field_simp
        ring
      · field_simp
        ring
    simp only [hrw]
    rw [intervalIntegral.integral_div]
    have hcne : (2 * (k : ℝ) * Real.pi / L) ≠ 0 := by
      apply div_ne_zero
      · positivity
      · exact hL.ne'
    rw [intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; continuity)
      (by apply Continuous.intervalIntegrable; continuity)]
    rw [intervalIntegral.integral_const,
      integral_cos_linear _ _ _ _ hcne]
    have hend1 : (2 * (k : ℝ) * Real.pi / L) * L + (-((k : ℝ) * Real.pi * a / L))
        = (k : ℕ) * (2 * Real.pi) - (k : ℝ) * Real.pi * a / L := by
      push_cast
      field_simp
      ring
    have hend2 : (2 * (k : ℝ) * Real.pi / L) * a + (-((k : ℝ) * Real.pi * a / L))
        = (k : ℝ) * Real.pi * a / L := by
      field_simp
      ring
    rw [hend1, hend2,
      Real.sin_nat_mul_two_pi_sub ((k : ℝ) * Real.pi * a / L) k]
    field_simp
    ring
  rw [hv1, hv2]
  ring

/-- **The diagonal formula, orthonormal-normalized**:
`(T_a)_{mm} = (1−a/L)·cos((m+1)πa/L) + sin((m+1)πa/L)/((m+1)π)`. -/
theorem galerkinT_diag_formula (L a : ℝ) (hL : 0 < L)
    (ha0 : 0 ≤ a) (haL : a ≤ L) (m : Fin N) :
    galerkinT (N := N) L a m m
      = (1 - a / L) * Real.cos (((m : ℝ) + 1) * Real.pi * a / L)
        + Real.sin (((m : ℝ) + 1) * Real.pi * a / L) / ((((m : ℝ)) + 1) * Real.pi) := by
  unfold galerkinT
  have hk : (m : ℕ) + 1 ≠ 0 := Nat.succ_ne_zero _
  rw [TmatrixElement_diag_eval L a hL ha0 haL ((m : ℕ) + 1) hk]
  have hcast : (((m : ℕ) + 1 : ℕ) : ℝ) = ((m : ℝ) + 1) := by push_cast; ring
  rw [hcast]
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp

#print axioms sinProdToSum_diag
#print axioms integral_cos_linear
#print axioms TmatrixElement_diag_eval
#print axioms galerkinT_diag_formula

end

end RHFormalization
