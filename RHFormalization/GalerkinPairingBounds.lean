import RHFormalization.GalerkinOneLetterNormalizationLock
import RHFormalization.AdaptiveGalerkinStage
import Mathlib

/-!
# Pairing bounds + adaptive lock — BRICK 4 of the canonical-F route

ROUTE CARD
1. `galerkinT_entry_abs_le`: entries of the compressed translation matrix
   bounded by 2, UNIFORMLY IN N — the dimension-free pairing estimate.
2. `adaptiveBcorrWin` + `adaptive_windowedCanonical_lock`: the normalization
   lock at the adaptive window (same cutoff `admR n`, window `adaptiveL c n`).
3. No positivity shortcuts anywhere (frozen rule).
SENTINEL: split_ifs-v2
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- Pointwise: the windowed eigenfunction is bounded by 1. -/
theorem dirichletEigenfunWindowed_abs_le (n : ℕ) (L y : ℝ) :
    |dirichletEigenfunWindowed n L y| ≤ 1 := by
  unfold dirichletEigenfunWindowed dirichletEigenfun
  split_ifs with h
  · exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  · simp

/-- The bare translation matrix element is bounded by the box width. -/
theorem TmatrixElement_abs_le (L a : ℝ) (hL : 0 ≤ L) (m n : ℕ) :
    |TmatrixElement L a m n| ≤ L := by
  unfold TmatrixElement
  have hbound : ∀ x ∈ Set.uIoc (0 : ℝ) L,
      ‖dirichletEigenfun m L x * dirichletEigenfunWindowed n L (x - a)‖ ≤ 1 := by
    intro x _
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |dirichletEigenfun m L x| ≤ 1 := by
      unfold dirichletEigenfun
      exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have h2 : |dirichletEigenfunWindowed n L (x - a)| ≤ 1 :=
      dirichletEigenfunWindowed_abs_le n L (x - a)
    calc |dirichletEigenfun m L x| * |dirichletEigenfunWindowed n L (x - a)|
        ≤ 1 * 1 := by
          exact mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 1 := by ring
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at h
  calc |∫ x in (0:ℝ)..L,
          dirichletEigenfun m L x * dirichletEigenfunWindowed n L (x - a)|
      ≤ 1 * |L - 0| := h
    _ = L := by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ L - 0)]; ring

/-- **N-FREE PAIRING BOUND**: every entry of the orthonormal-normalized
compressed translation matrix is bounded by 2, independent of `N`, `a`, `L`. -/
theorem galerkinT_entry_abs_le (L a : ℝ) (hL : 0 < L) (m n : Fin N) :
    |galerkinT (N := N) L a m n| ≤ 2 := by
  unfold galerkinT
  rw [abs_mul]
  have h1 : |(2 / L : ℝ)| = 2 / L := by
    rw [abs_of_pos]; positivity
  rw [h1]
  have h2 : |TmatrixElement L a ((m : ℕ) + 1) ((n : ℕ) + 1)| ≤ L :=
    TmatrixElement_abs_le L a hL.le _ _
  calc (2 / L) * |TmatrixElement L a ((m : ℕ) + 1) ((n : ℕ) + 1)|
      ≤ (2 / L) * L := by
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 := by field_simp

/-- **Adaptive window deficit** — `BcorrWin` at the adaptive window. -/
def adaptiveBcorrWin (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
    q.weightC * ((q.center / (2 * adaptiveL c n) : ℝ) : ℂ) *
      shiftedLaplaceHeatKernelC q.center s

/-- **The lock at the adaptive stage**. -/
theorem adaptive_windowedCanonical_lock (c : ℝ) (n : ℕ) (s : ℂ) :
    windowedCanonicalPackage
        (activePrimePowerPairsCenterBelow (admR n)) (adaptiveL c n)
        shiftedLaplaceHeatKernelC s
      = (1 / 2 : ℂ) *
          galerkinStagePackage.B_stage (adaptiveGalerkinStageSeq c n) s
        - adaptiveBcorrWin c n s := by
  have hL : adaptiveL c n ≠ 0 := (adaptiveL_pos c n).ne'
  exact windowedCanonicalPackage_lock
    (activePrimePowerPairsCenterBelow (admR n)) (adaptiveL c n) hL
    shiftedLaplaceHeatKernelC s

#print axioms dirichletEigenfunWindowed_abs_le
#print axioms TmatrixElement_abs_le
#print axioms galerkinT_entry_abs_le
#print axioms adaptiveBcorrWin
#print axioms adaptive_windowedCanonical_lock

end

end RHFormalization
