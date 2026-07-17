-- SENTINEL: L1a-complex-riemann-error-v2
import Mathlib

/-!
# L1a — Complex-valued endpoint Riemann-sum error
Norm analogues of the banked real lemmas (RiemannSliceError,
PartitionRiemannError), for ℂ-valued integrands:
  slice:     ‖(d−c)·f(d) − ∫_c^d f‖ ≤ (d−c)·∫_c^d ‖f′‖
  partition: ‖Σ_{k<N} h·f((k+1)h) − ∫_0^{Nh} f‖ ≤ h·∫_0^{Nh} ‖f′‖
Consumed by L1 with f(ξ) = cos(ξa)/(s+1/4+ξ²) and the L0a floor.
v2: hendpoint rewritten in the GOAL (backward), not in hs — forward rewrite
in hs also hit the integral bounds (ambiguous-rewrite trap).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory

/-- **Slice estimate, ℂ-valued**: right-endpoint term vs the integral. -/
theorem slice_riemann_error_C (f f' : ℝ → ℂ) (c d : ℝ) (hcd : c ≤ d)
    (hderiv : ∀ x ∈ Set.uIcc c d, HasDerivAt f (f' x) x)
    (hf'c : ContinuousOn f' (Set.uIcc c d)) :
    ‖((d - c : ℝ) : ℂ) * f d - ∫ x in c..d, f x‖
      ≤ (d - c) * ∫ x in c..d, ‖f' x‖ := by
  have hfc : ContinuousOn f (Set.uIcc c d) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hfint : IntervalIntegrable f volume c d := hfc.intervalIntegrable
  set M : ℝ := ∫ x in c..d, ‖f' x‖ with hMdef
  have hM0 : (0:ℝ) ≤ M := by
    rw [hMdef]
    exact intervalIntegral.integral_nonneg hcd (fun x _ => norm_nonneg _)
  have hconst : (∫ _ in c..d, f d) = ((d - c : ℝ) : ℂ) * f d := by
    rw [intervalIntegral.integral_const, Complex.real_smul]
  have hkey : ((d - c : ℝ) : ℂ) * f d - ∫ x in c..d, f x
      = ∫ x in c..d, (f d - f x) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hfint, hconst]
  rw [hkey]
  have hpt : ∀ x ∈ Set.uIoc c d, ‖f d - f x‖ ≤ M := by
    intro x hx
    rw [Set.uIoc_of_le hcd] at hx
    obtain ⟨hcx, hxd⟩ := hx
    have hsubxd : Set.uIcc x d ⊆ Set.uIcc c d := by
      rw [Set.uIcc_of_le hxd, Set.uIcc_of_le hcd]
      exact Set.Icc_subset_Icc hcx.le le_rfl
    have hsubcx : Set.uIcc c x ⊆ Set.uIcc c d := by
      rw [Set.uIcc_of_le hcx.le, Set.uIcc_of_le hcd]
      exact Set.Icc_subset_Icc le_rfl hxd
    have hFTC : (∫ u in x..d, f' u) = f d - f x := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro u hu
        exact hderiv u (hsubxd hu)
      · exact (hf'c.mono hsubxd).intervalIntegrable
    rw [← hFTC]
    have h1 : ‖∫ u in x..d, f' u‖ ≤ ∫ u in x..d, ‖f' u‖ :=
      intervalIntegral.norm_integral_le_integral_norm hxd
    have hint_cx : IntervalIntegrable (fun u => ‖f' u‖) volume c x :=
      ((hf'c.mono hsubcx).intervalIntegrable).norm
    have hint_xd : IntervalIntegrable (fun u => ‖f' u‖) volume x d :=
      ((hf'c.mono hsubxd).intervalIntegrable).norm
    have hsplit : (∫ u in c..x, ‖f' u‖) + ∫ u in x..d, ‖f' u‖ = M := by
      rw [hMdef]
      exact intervalIntegral.integral_add_adjacent_intervals hint_cx hint_xd
    have hnn : (0:ℝ) ≤ ∫ u in c..x, ‖f' u‖ :=
      intervalIntegral.integral_nonneg hcx.le (fun u _ => norm_nonneg _)
    linarith
  have hfinal := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ d - c)] at hfinal
  linarith [hfinal, mul_comm M (d - c)]

/-- **Partition estimate, ℂ-valued**: right-endpoint Riemann sum on the
uniform mesh `h` over `[0, N·h]` vs the integral. -/
theorem partition_riemann_error_C (f f' : ℝ → ℂ) (h : ℝ) (hh : 0 < h)
    (N : ℕ)
    (hderiv : ∀ x ∈ Set.Icc (0:ℝ) ((N:ℝ)*h), HasDerivAt f (f' x) x)
    (hf'c : ContinuousOn f' (Set.Icc (0:ℝ) ((N:ℝ)*h))) :
    ‖(∑ k ∈ Finset.range N, ((h : ℝ) : ℂ) * f (((k:ℝ)+1)*h))
        - ∫ x in (0:ℝ)..((N:ℝ)*h), f x‖
      ≤ h * ∫ x in (0:ℝ)..((N:ℝ)*h), ‖f' x‖ := by
  set a : ℕ → ℝ := fun k => (k:ℝ)*h with hadef
  have ha0 : a 0 = 0 := by simp [hadef]
  have haN : a N = (N:ℝ)*h := rfl
  have hamono : ∀ k : ℕ, a k ≤ a (k+1) := by
    intro k
    simp only [hadef]
    have : (k:ℝ) ≤ (k:ℝ) + 1 := by linarith
    push_cast
    nlinarith [hh]
  have hasub : ∀ k : ℕ, k < N → Set.uIcc (a k) (a (k+1)) ⊆ Set.Icc (0:ℝ) ((N:ℝ)*h) := by
    intro k hk
    rw [Set.uIcc_of_le (hamono k)]
    apply Set.Icc_subset_Icc
    · simp only [hadef]
      positivity
    · simp only [hadef]
      push_cast
      have hk1 : ((k:ℝ)+1) ≤ (N:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
      nlinarith [hh]
  have hfc : ContinuousOn f (Set.Icc (0:ℝ) ((N:ℝ)*h)) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hadj_f : ∀ k < N, IntervalIntegrable f volume (a k) (a (k+1)) :=
    fun k hk => (hfc.mono (hasub k hk)).intervalIntegrable
  have hadj_norm : ∀ k < N, IntervalIntegrable (fun x => ‖f' x‖) volume (a k) (a (k+1)) :=
    fun k hk => ((hf'c.mono (hasub k hk)).intervalIntegrable).norm
  have hsum_f : (∑ k ∈ Finset.range N, ∫ x in a k..a (k+1), f x)
      = ∫ x in (0:ℝ)..((N:ℝ)*h), f x := by
    rw [← ha0, ← haN]
    exact intervalIntegral.sum_integral_adjacent_intervals hadj_f
  have hsum_norm : (∑ k ∈ Finset.range N, ∫ x in a k..a (k+1), ‖f' x‖)
      = ∫ x in (0:ℝ)..((N:ℝ)*h), ‖f' x‖ := by
    rw [← ha0, ← haN]
    exact intervalIntegral.sum_integral_adjacent_intervals hadj_norm
  have hstep : (∑ k ∈ Finset.range N, ((h : ℝ) : ℂ) * f (((k:ℝ)+1)*h))
        - ∫ x in (0:ℝ)..((N:ℝ)*h), f x
      = ∑ k ∈ Finset.range N,
          (((h : ℝ) : ℂ) * f (((k:ℝ)+1)*h) - ∫ x in a k..a (k+1), f x) := by
    rw [Finset.sum_sub_distrib, hsum_f]
  rw [hstep]
  have hslice : ∀ k ∈ Finset.range N,
      ‖((h : ℝ) : ℂ) * f (((k:ℝ)+1)*h) - ∫ x in a k..a (k+1), f x‖
        ≤ h * ∫ x in a k..a (k+1), ‖f' x‖ := by
    intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    have hdc : a (k+1) - a k = h := by
      simp only [hadef]
      push_cast
      ring
    have hendpoint : a (k+1) = ((k:ℝ)+1)*h := by
      simp only [hadef]
      push_cast
      ring
    have hs := slice_riemann_error_C f f' (a k) (a (k+1)) (hamono k)
      (fun x hx => hderiv x (hasub k hkN hx))
      (hf'c.mono (hasub k hkN))
    rw [hdc] at hs
    rw [← hendpoint]
    exact hs
  calc ‖∑ k ∈ Finset.range N,
        (((h : ℝ) : ℂ) * f (((k:ℝ)+1)*h) - ∫ x in a k..a (k+1), f x)‖
      ≤ ∑ k ∈ Finset.range N,
          ‖((h : ℝ) : ℂ) * f (((k:ℝ)+1)*h) - ∫ x in a k..a (k+1), f x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, h * ∫ x in a k..a (k+1), ‖f' x‖ :=
        Finset.sum_le_sum hslice
    _ = h * ∑ k ∈ Finset.range N, ∫ x in a k..a (k+1), ‖f' x‖ := by
        rw [Finset.mul_sum]
    _ = h * ∫ x in (0:ℝ)..((N:ℝ)*h), ‖f' x‖ := by rw [hsum_norm]

#print axioms slice_riemann_error_C
#print axioms partition_riemann_error_C

end

end RHFormalization
