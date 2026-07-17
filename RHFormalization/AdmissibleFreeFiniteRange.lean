import RHFormalization.AdmissibleFreeCellEstimate

/-!
# RHFormalization.AdmissibleFreeFiniteRange

**Front F-adm, brick 1d-i.** Finite-range half of the free Riemann assembly:

  `‖admissibleFreeStage n s − (1/2π)·∫_{Ioc 0 U_n} f‖ ≤ (1/2π)·(π/L_n)/δ²·U_n²`,

with `U_n = freeGridPt (admL n) (admN n)`. Cell bounds telescope
(`Σ(u_{k+1}²−u_k²) = U²`); at the admissible schedule the RHS is
`π²/(2(n+2)δ²) → 0`. Tail + tendsto + DFHLimitData-shape theorem in 1d-ii.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory

/-- **Stage = grid sum**: the admissible free stage is the density constant
times the right-endpoint grid sample sum of the free integrand. -/
theorem admissibleFreeStage_eq_grid_sum (n : ℕ) (s : ℂ) :
    admissibleFreeStage n s
      = admDensityC n *
          ∑ k ∈ Finset.range (admN n),
            freeResolventIntegrand s (freeGridPt (admL n) (k + 1)) := by
  unfold admissibleFreeStage
  congr 1
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => freeResolventIntegrand s (freeGridPt (admL n) (k + 1))) (admN n)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold freeResolventIntegrand
  rw [freeGridPt_sq_eq_mu]

/-- **Density factorization**: `1/(2L) = (1/2π)·(π/L)` as complex scalars. -/
theorem admDensityC_eq_two_pi_inv_mul (n : ℕ) :
    admDensityC n
      = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((Real.pi / admL n : ℝ) : ℂ) := by
  unfold admDensityC
  rw [← Complex.ofReal_mul]
  congr 1
  have hL : admL n ≠ 0 := (admL_pos n).ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  first
    | field_simp
    | (field_simp; ring)

/-- **Telescoped cell-sum bound**: the total Riemann error over the grid is
`≤ (π/L)/δ²·(freeGridPt L N)²` — per-cell `resolvent_diff_norm_le` bounds
telescope, no derivative analysis. -/
theorem freeRiemann_cellsum_le {s : ℂ} (hs : s ∈ Ω) {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ lam : ℝ, 0 ≤ lam → δ ≤ ‖s + (lam : ℂ)‖)
    (L : ℝ) (hL : 0 < L) (N : ℕ) :
    ‖∑ k ∈ Finset.range N,
        (((Real.pi / L : ℝ) : ℂ) *
            freeResolventIntegrand s (freeGridPt L (k + 1))
          - ∫ u in freeGridPt L k..freeGridPt L (k + 1),
              freeResolventIntegrand s u)‖
      ≤ Real.pi / L / δ ^ 2 * freeGridPt L N ^ 2 := by
  have hcell : ∀ k ∈ Finset.range N,
      ‖((Real.pi / L : ℝ) : ℂ) *
            freeResolventIntegrand s (freeGridPt L (k + 1))
          - ∫ u in freeGridPt L k..freeGridPt L (k + 1),
              freeResolventIntegrand s u‖
        ≤ (freeGridPt L (k + 1) ^ 2 - freeGridPt L k ^ 2) / δ ^ 2
            * (Real.pi / L) := by
    intro k _
    have hsm : ((Real.pi / L : ℝ) : ℂ) *
        freeResolventIntegrand s (freeGridPt L (k + 1))
        = (Real.pi / L) • freeResolventIntegrand s (freeGridPt L (k + 1)) := by
      first
        | exact (Complex.real_smul _ _).symm
        | exact Complex.real_smul.symm
        | simp [Complex.real_smul]
    rw [hsm, norm_sub_rev]
    have h := freeResolvent_cell_estimate hs hδ hlow
      (freeGridPt_nonneg L hL k) (freeGridPt_le_succ L hL k)
    rw [freeGridPt_succ_sub L k] at h
    exact h
  calc ‖∑ k ∈ Finset.range N,
        (((Real.pi / L : ℝ) : ℂ) *
            freeResolventIntegrand s (freeGridPt L (k + 1))
          - ∫ u in freeGridPt L k..freeGridPt L (k + 1),
              freeResolventIntegrand s u)‖
      ≤ ∑ k ∈ Finset.range N,
          ‖((Real.pi / L : ℝ) : ℂ) *
              freeResolventIntegrand s (freeGridPt L (k + 1))
            - ∫ u in freeGridPt L k..freeGridPt L (k + 1),
                freeResolventIntegrand s u‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N,
          (freeGridPt L (k + 1) ^ 2 - freeGridPt L k ^ 2) / δ ^ 2
            * (Real.pi / L) := Finset.sum_le_sum hcell
    _ = Real.pi / L / δ ^ 2 * freeGridPt L N ^ 2 := by
        have hterm : ∀ k ∈ Finset.range N,
            (freeGridPt L (k + 1) ^ 2 - freeGridPt L k ^ 2) / δ ^ 2
                * (Real.pi / L)
              = (freeGridPt L (k + 1) ^ 2 - freeGridPt L k ^ 2)
                  * (Real.pi / L / δ ^ 2) := fun k _ => by ring
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
          Finset.sum_range_sub (fun k => freeGridPt L k ^ 2), freeGridPt_zero]
        ring

/-- **Brick 1d-i: finite-range estimate.** The stage differs from the
density-normalized finite-range integral by at most the telescoped Riemann
error. At the admissible schedule the RHS is `π²/(2(n+2)δ²)`. -/
theorem admissibleFreeStage_finiteRange_diff_le {s : ℂ} (hs : s ∈ Ω)
    {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ lam : ℝ, 0 ≤ lam → δ ≤ ‖s + (lam : ℂ)‖) (n : ℕ) :
    ‖admissibleFreeStage n s
        - ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ u in Set.Ioc (0 : ℝ) (freeGridPt (admL n) (admN n)),
              freeResolventIntegrand s u‖
      ≤ 1 / (2 * Real.pi) *
          (Real.pi / admL n / δ ^ 2 * freeGridPt (admL n) (admN n) ^ 2) := by
  have hL : 0 < admL n := admL_pos n
  have hIoc : (∫ u in Set.Ioc (0 : ℝ) (freeGridPt (admL n) (admN n)),
        freeResolventIntegrand s u)
      = ∑ k ∈ Finset.range (admN n),
          ∫ u in freeGridPt (admL n) k..freeGridPt (admL n) (k + 1),
            freeResolventIntegrand s u := by
    have h1 := freeResolvent_grid_integral_sum hs (admL n) (admN n)
    rw [freeGridPt_zero] at h1
    rw [intervalIntegral.integral_of_le
      (freeGridPt_nonneg (admL n) hL (admN n))] at h1
    exact h1.symm
  rw [admissibleFreeStage_eq_grid_sum n s, admDensityC_eq_two_pi_inv_mul n,
    hIoc, mul_assoc, ← mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib,
    norm_mul]
  have hnc : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  rw [hnc]
  exact mul_le_mul_of_nonneg_left
    (freeRiemann_cellsum_le hs hδ hlow (admL n) hL (admN n))
    (by positivity)

#print axioms admissibleFreeStage_eq_grid_sum
#print axioms admDensityC_eq_two_pi_inv_mul
#print axioms freeRiemann_cellsum_le
#print axioms admissibleFreeStage_finiteRange_diff_le

end

end RHFormalization
