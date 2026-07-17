import RHFormalization.AdmissibleFreeStageHolo
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# RHFormalization.AdmissibleFreeCellEstimate

**Front F-adm, brick 1c.** Per-cell Riemann estimate for the free integrand on
the uniform grid `freeGridPt L k = k·π/L`:

  `‖∫_p^q f − (q−p)·f(q)‖ ≤ ((q²−p²)/δ²)·(q−p)`,

via the banked `resolvent_diff_norm_le`. The cell bounds TELESCOPE over the
grid (Σ(u_{k+1}²−u_k²) = U²), so brick 1d's total Riemann error is
`(1/2π)·(π/L)·U²/δ² = π²/(2(n+2)δ²) → 0` — no derivative analysis needed.
Also: grid lemmas and the adjacent-intervals decomposition.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory

/-- The free integrand is continuous in `u` for `s ∈ Ω` (denominator never
vanishes: nonneg real shifts cannot reach the cut). -/
theorem freeResolventIntegrand_continuous {s : ℂ} (hs : s ∈ Ω) :
    Continuous (freeResolventIntegrand s) := by
  have h1 : Continuous (fun u : ℝ => SupVConst + u ^ 2) :=
    continuous_const.add (continuous_pow 2)
  have hden : Continuous (fun u : ℝ => s + ((SupVConst + u ^ 2 : ℝ) : ℂ)) :=
    continuous_const.add (Complex.continuous_ofReal.comp h1)
  first
    | exact hden.inv₀ (fun u => freeResolvent_denom_ne_zero hs u)
    | (unfold freeResolventIntegrand
       exact hden.inv₀ (fun u => freeResolvent_denom_ne_zero hs u))

/-- The uniform free grid: `freeGridPt L k = k·π/L`. -/
def freeGridPt (L : ℝ) (k : ℕ) : ℝ := (k : ℝ) * Real.pi / L

theorem freeGridPt_zero (L : ℝ) : freeGridPt L 0 = 0 := by
  unfold freeGridPt; simp

theorem freeGridPt_nonneg (L : ℝ) (hL : 0 < L) (k : ℕ) :
    0 ≤ freeGridPt L k := by
  unfold freeGridPt; positivity

theorem freeGridPt_le_succ (L : ℝ) (hL : 0 < L) (k : ℕ) :
    freeGridPt L k ≤ freeGridPt L (k + 1) := by
  unfold freeGridPt
  have hpl : (0:ℝ) ≤ Real.pi / L := by positivity
  have hc : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hc, mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right (by linarith) hpl

/-- Cell width is exactly `π/L`. -/
theorem freeGridPt_succ_sub (L : ℝ) (k : ℕ) :
    freeGridPt L (k + 1) - freeGridPt L k = Real.pi / L := by
  unfold freeGridPt
  push_cast
  ring

/-- **Eigenvalue bridge**: the squared grid point at `i+1` IS the free
Dirichlet eigenvalue `galerkinFreeMu N L i`. -/
theorem freeGridPt_sq_eq_mu (L : ℝ) (N : ℕ) (i : Fin N) :
    freeGridPt L ((i : ℕ) + 1) ^ 2 = galerkinFreeMu N L i := by
  unfold freeGridPt galerkinFreeMu
  push_cast
  ring

/-- **Per-cell Riemann estimate** (right endpoint): on `[p,q] ⊆ [0,∞)`,
`‖∫_p^q f − (q−p)·f(q)‖ ≤ ((q²−p²)/δ²)·(q−p)`, where `δ` is any uniform
cut-distance for `s`. -/
theorem freeResolvent_cell_estimate {s : ℂ} (hs : s ∈ Ω)
    {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ lam : ℝ, 0 ≤ lam → δ ≤ ‖s + (lam : ℂ)‖)
    {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    ‖(∫ u in p..q, freeResolventIntegrand s u)
        - (q - p) • freeResolventIntegrand s q‖
      ≤ (q ^ 2 - p ^ 2) / δ ^ 2 * (q - p) := by
  have hcont := freeResolventIntegrand_continuous hs
  have hInt : IntervalIntegrable (freeResolventIntegrand s) volume p q :=
    hcont.intervalIntegrable p q
  have hIntc : IntervalIntegrable
      (fun _ : ℝ => freeResolventIntegrand s q) volume p q :=
    intervalIntegrable_const
  have hkey : (∫ u in p..q, freeResolventIntegrand s u)
      - (q - p) • freeResolventIntegrand s q
      = ∫ u in p..q,
          (freeResolventIntegrand s u - freeResolventIntegrand s q) := by
    rw [intervalIntegral.integral_sub hInt hIntc,
      intervalIntegral.integral_const]
  rw [hkey]
  have hb : ∀ u ∈ Set.uIoc p q,
      ‖freeResolventIntegrand s u - freeResolventIntegrand s q‖
        ≤ (q ^ 2 - p ^ 2) / δ ^ 2 := by
    intro u hu
    rw [Set.uIoc_of_le hpq] at hu
    obtain ⟨hpu, huq⟩ := hu
    have hu0 : (0:ℝ) ≤ u := le_of_lt (lt_of_le_of_lt hp hpu)
    show ‖(s + ((SupVConst + u ^ 2 : ℝ) : ℂ))⁻¹
        - (s + ((SupVConst + q ^ 2 : ℝ) : ℂ))⁻¹‖
      ≤ (q ^ 2 - p ^ 2) / δ ^ 2
    have hlam1 : (0:ℝ) ≤ SupVConst + u ^ 2 :=
      add_nonneg SupVConst_nonneg_adm (sq_nonneg u)
    have hlam2 : (0:ℝ) ≤ SupVConst + q ^ 2 :=
      add_nonneg SupVConst_nonneg_adm (sq_nonneg q)
    have h := resolvent_diff_norm_le s (SupVConst + u ^ 2)
      (SupVConst + q ^ 2) δ hδ (hlow _ hlam1) (hlow _ hlam2)
    have h1 : u ^ 2 ≤ q ^ 2 := by nlinarith [hu0, huq]
    have h2 : p ^ 2 ≤ u ^ 2 := by nlinarith [hp, hpu]
    have habs : |(SupVConst + u ^ 2) - (SupVConst + q ^ 2)|
        ≤ q ^ 2 - p ^ 2 := by
      have hsimp : (SupVConst + u ^ 2) - (SupVConst + q ^ 2)
          = u ^ 2 - q ^ 2 := by ring
      rw [hsimp, abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    refine le_trans h ?_
    have hδ2 : (0:ℝ) < δ ^ 2 := by positivity
    first
      | gcongr
      | exact (div_le_div_right hδ2).mpr habs
      | exact (div_le_div_iff_right hδ2).mpr habs
      | exact div_le_div_of_nonneg_right habs hδ2
  have hfin := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rwa [abs_of_nonneg (sub_nonneg.mpr hpq)] at hfin

/-- **Adjacent-cells decomposition**: the finite-range integral splits along
the free grid. -/
theorem freeResolvent_grid_integral_sum {s : ℂ} (hs : s ∈ Ω)
    (L : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N,
        ∫ u in freeGridPt L k..freeGridPt L (k + 1),
          freeResolventIntegrand s u
      = ∫ u in freeGridPt L 0..freeGridPt L N,
          freeResolventIntegrand s u :=
  intervalIntegral.sum_integral_adjacent_intervals
    (fun k _ => (freeResolventIntegrand_continuous hs).intervalIntegrable _ _)

#print axioms freeResolventIntegrand_continuous
#print axioms freeGridPt_sq_eq_mu
#print axioms freeResolvent_cell_estimate
#print axioms freeResolvent_grid_integral_sum

end

end RHFormalization
