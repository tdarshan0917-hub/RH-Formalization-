import RHFormalization.PrimePotentialPosition
import RHFormalization.DecodedAnchorDischarge
import Mathlib

/-!
# RawGaussianFrameObstruction — K1′ and K2

K1′: Gram-matrix form of the Bessel lower bound (entries ≥ α on S×S ⇒ any
Bessel constant ≥ α·|S|). K2: on the finite window `[0, L]`, two live
unit-width bumps `gaussBump 1 (· − a)`, `gaussBump 1 (· − b)` with centers
in the interior margin `[3/2, L − 3/2]` and `|a − b| ≤ 1` overlap by at least
`e^{−9/4}/π`. Elementary (pointwise bound on a unit sub-window); no Gaussian
integral needed. Kills only the raw-channel generic-Bessel route.
-/

set_option autoImplicit false

namespace RHFormalization

open Finset

/-- **K1′a** — Gram-matrix lower bound. -/
theorem gram_sum_ge_of_entries_ge {ι : Type*} (S : Finset ι) (G : ι → ι → ℝ)
    (α : ℝ) (h : ∀ i ∈ S, ∀ j ∈ S, α ≤ G i j) :
    α * (S.card : ℝ) ^ 2 ≤ ∑ i ∈ S, ∑ j ∈ S, G i j := by
  calc α * (S.card : ℝ) ^ 2
      = ∑ i ∈ S, ∑ j ∈ S, α := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, G i j := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        exact Finset.sum_le_sum (fun j hj => h i hi j hj)

/-- **K1′b** — any Bessel constant for the quadratic form `cᵀGc` is ≥ α·|S|. -/
theorem gram_bessel_const_ge {ι : Type*} (S : Finset ι) (G : ι → ι → ℝ)
    (α B : ℝ)
    (hB : ∀ c : ι → ℝ,
      ∑ i ∈ S, ∑ j ∈ S, c i * c j * G i j ≤ B * ∑ i ∈ S, c i ^ 2)
    (h : ∀ i ∈ S, ∀ j ∈ S, α ≤ G i j) (hS : 0 < S.card) :
    α * (S.card : ℝ) ≤ B := by
  have h1 := gram_sum_ge_of_entries_ge S G α h
  have h2 := hB (fun _ => 1)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h2
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS
  have h3 : α * (S.card : ℝ) * (S.card : ℝ) ≤ B * (S.card : ℝ) := by
    nlinarith [h1, h2]
  exact le_of_mul_le_mul_right h3 hc

/-- Unit-width bump lower bound within distance `3/2` of its center. -/
theorem gaussBump_one_ge_of_sq_le {y : ℝ} (hy : y ^ 2 ≤ 9 / 4) :
    Real.exp (-9 / 8) / Real.sqrt (2 * Real.pi) ≤ gaussBump 1 y := by
  unfold gaussBump
  rw [show (2 : ℝ) * Real.pi * 1 ^ 2 = 2 * Real.pi by ring]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.mpr
  have h' : -y ^ 2 / (2 * (1 : ℝ) ^ 2) = -(y ^ 2 / 2) := by ring
  rw [h']
  linarith

/-- **K2** — window overlap lower bound for two live bumps with interior
centers at distance ≤ 1. -/
theorem gaussBump_window_overlap_ge (L a b : ℝ)
    (ha : 3 / 2 ≤ a) (haL : a ≤ L - 3 / 2)
    (hb : 3 / 2 ≤ b) (hbL : b ≤ L - 3 / 2)
    (hab : |a - b| ≤ 1) :
    Real.exp (-9 / 4) / Real.pi
      ≤ ∫ x in (0:ℝ)..L, gaussBump 1 (x - a) * gaussBump 1 (x - b) := by
  obtain ⟨hab1, hab2⟩ := abs_le.mp hab
  set m : ℝ := (a + b) / 2 with hm
  have hcont : Continuous fun x : ℝ => gaussBump 1 (x - a) * gaussBump 1 (x - b) :=
    ((gaussBump_continuous_any 1).comp (continuous_id.sub continuous_const)).mul
      ((gaussBump_continuous_any 1).comp (continuous_id.sub continuous_const))
  have hnn : ∀ x : ℝ, 0 ≤ gaussBump 1 (x - a) * gaussBump 1 (x - b) :=
    fun x => (mul_pos (gaussBump_pos 1 one_pos _) (gaussBump_pos 1 one_pos _)).le
  have hpt : ∀ x ∈ Set.Icc (m - 1) (m + 1),
      Real.exp (-9 / 4) / (2 * Real.pi)
        ≤ gaussBump 1 (x - a) * gaussBump 1 (x - b) := by
    intro x hx
    have hxa : (x - a) ^ 2 ≤ 9 / 4 := by
      have h1 : x - a ≤ 3 / 2 := by linarith [hx.2]
      have h2 : -(3 / 2) ≤ x - a := by linarith [hx.1]
      nlinarith [h1, h2]
    have hxb : (x - b) ^ 2 ≤ 9 / 4 := by
      have h1 : x - b ≤ 3 / 2 := by linarith [hx.2]
      have h2 : -(3 / 2) ≤ x - b := by linarith [hx.1]
      nlinarith [h1, h2]
    have hA := gaussBump_one_ge_of_sq_le hxa
    have hB := gaussBump_one_ge_of_sq_le hxb
    have hprod : Real.exp (-9 / 8) / Real.sqrt (2 * Real.pi)
        * (Real.exp (-9 / 8) / Real.sqrt (2 * Real.pi))
        = Real.exp (-9 / 4) / (2 * Real.pi) := by
      rw [div_mul_div_comm, ← Real.exp_add,
        Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      norm_num
    rw [← hprod]
    exact mul_le_mul hA hB (by positivity) (gaussBump_pos 1 one_pos _).le
  have h0m : (0 : ℝ) ≤ m - 1 := by rw [hm]; linarith
  have hmL : m + 1 ≤ L := by rw [hm]; linarith
  have hmm : m - 1 ≤ m + 1 := by linarith
  calc Real.exp (-9 / 4) / Real.pi
      = 2 * (Real.exp (-9 / 4) / (2 * Real.pi)) := by
        rw [mul_div_assoc', mul_div_mul_left _ _ (two_ne_zero)]
    _ = ∫ x in (m - 1)..(m + 1), Real.exp (-9 / 4) / (2 * Real.pi) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ ≤ ∫ x in (m - 1)..(m + 1), gaussBump 1 (x - a) * gaussBump 1 (x - b) :=
        intervalIntegral.integral_mono_on hmm intervalIntegrable_const
          (hcont.intervalIntegrable _ _) hpt
    _ ≤ ∫ x in (0:ℝ)..L, gaussBump 1 (x - a) * gaussBump 1 (x - b) :=
        intervalIntegral.integral_mono_interval h0m hmm hmL
          (MeasureTheory.ae_of_all _ hnn) (hcont.intervalIntegrable _ _)

#print axioms gram_sum_ge_of_entries_ge
#print axioms gram_bessel_const_ge
#print axioms gaussBump_one_ge_of_sq_le
#print axioms gaussBump_window_overlap_ge

end RHFormalization
