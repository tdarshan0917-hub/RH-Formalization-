import RHFormalization.CosGaussianDerivBound
import Mathlib

/-!
# Summed partition error — G3-ii-b sub-brick 3
SENTINEL: partition-error-v2

ROUTE CARD
1. `partition_endpoint_riemann_error`: for C¹ f on [0, Nh],
   `|Σ_{k<N} h·f((k+1)h) − ∫₀^{Nh} f| ≤ h·∫₀^{Nh} |f'|`.
   Telescopes the banked slice engine over the uniform partition.
2. Generic; instantiated at cosGauss in sub-brick 4 where the right side
   evaluates in closed form to h·(1 + |a|·√(π/4t)).
-/

set_option autoImplicit false

namespace RHFormalization

open MeasureTheory

theorem partition_endpoint_riemann_error (f f' : ℝ → ℝ) (h : ℝ) (hh : 0 < h)
    (N : ℕ)
    (hderiv : ∀ x ∈ Set.Icc (0 : ℝ) ((N : ℝ) * h), HasDerivAt f (f' x) x)
    (hf'c : ContinuousOn f' (Set.Icc (0 : ℝ) ((N : ℝ) * h))) :
    |(∑ k ∈ Finset.range N, h * f (((k : ℝ) + 1) * h))
        - ∫ x in (0 : ℝ)..((N : ℝ) * h), f x|
      ≤ h * ∫ x in (0 : ℝ)..((N : ℝ) * h), |f' x| := by
  set a : ℕ → ℝ := fun k => (k : ℝ) * h with ha
  -- basic facts about the partition
  have ha0 : a 0 = 0 := by simp [ha]
  have haN : a N = (N : ℝ) * h := rfl
  have hstep : ∀ k : ℕ, a (k + 1) - a k = h := by
    intro k
    simp only [ha]
    push_cast
    ring
  have hmono : ∀ k : ℕ, a k ≤ a (k + 1) := by
    intro k
    have := hstep k
    linarith
  have hnonneg : ∀ k : ℕ, 0 ≤ a k := by
    intro k
    simp only [ha]
    positivity
  have hupper : ∀ k : ℕ, k ≤ N → a k ≤ (N : ℝ) * h := by
    intro k hk
    simp only [ha]
    apply mul_le_mul_of_nonneg_right _ hh.le
    exact_mod_cast hk
  have hsub : ∀ k : ℕ, k < N →
      Set.uIcc (a k) (a (k + 1)) ⊆ Set.Icc (0 : ℝ) ((N : ℝ) * h) := by
    intro k hk
    rw [Set.uIcc_of_le (hmono k)]
    apply Set.Icc_subset_Icc (hnonneg k) (hupper (k + 1) hk)
  -- continuity of f on the big interval
  have hfc : ContinuousOn f (Set.Icc (0 : ℝ) ((N : ℝ) * h)) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  -- integrability on each slice
  have hfint : ∀ k : ℕ, k < N →
      IntervalIntegrable f volume (a k) (a (k + 1)) := by
    intro k hk
    exact (hfc.mono (hsub k hk)).intervalIntegrable
  have habsint : ∀ k : ℕ, k < N →
      IntervalIntegrable (fun x => |f' x|) volume (a k) (a (k + 1)) := by
    intro k hk
    exact ((hf'c.mono (hsub k hk)).abs).intervalIntegrable
  -- adjacent-intervals telescoping for f and |f'|
  have hsumf : (∑ k ∈ Finset.range N, ∫ x in (a k)..(a (k + 1)), f x)
      = ∫ x in (a 0)..(a N), f x :=
    intervalIntegral.sum_integral_adjacent_intervals hfint
  have hsumabs : (∑ k ∈ Finset.range N, ∫ x in (a k)..(a (k + 1)), |f' x|)
      = ∫ x in (a 0)..(a N), |f' x| :=
    intervalIntegral.sum_integral_adjacent_intervals habsint
  -- per-slice application of the banked engine
  have hslice : ∀ k ∈ Finset.range N,
      |h * f (a (k + 1)) - ∫ x in (a k)..(a (k + 1)), f x|
        ≤ h * ∫ x in (a k)..(a (k + 1)), |f' x| := by
    intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    have hcd := hmono k
    have he := slice_endpoint_riemann_error f f' (a k) (a (k + 1)) hcd
      (fun x hx => hderiv x (hsub k hkN hx))
      (hf'c.mono (by
        rw [Set.uIcc_of_le hcd]
        intro x hx
        exact hsub k hkN (by rw [Set.uIcc_of_le hcd]; exact hx)))
    rwa [hstep k] at he
  -- assemble
  have hrw : (∑ k ∈ Finset.range N, h * f (((k : ℝ) + 1) * h))
      = ∑ k ∈ Finset.range N, h * f (a (k + 1)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ha]
    push_cast
    ring_nf
  rw [ha0, haN] at hsumf hsumabs
  rw [hrw, ← hsumf, ← Finset.sum_sub_distrib]
  calc |∑ k ∈ Finset.range N,
        (h * f (a (k + 1)) - ∫ x in (a k)..(a (k + 1)), f x)|
      ≤ ∑ k ∈ Finset.range N,
          |h * f (a (k + 1)) - ∫ x in (a k)..(a (k + 1)), f x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, h * ∫ x in (a k)..(a (k + 1)), |f' x| :=
        Finset.sum_le_sum hslice
    _ = h * ∑ k ∈ Finset.range N, ∫ x in (a k)..(a (k + 1)), |f' x| := by
        rw [Finset.mul_sum]
    _ = h * ∫ x in (0 : ℝ)..((N : ℝ) * h), |f' x| := by rw [hsumabs]

#print axioms partition_endpoint_riemann_error

end RHFormalization
