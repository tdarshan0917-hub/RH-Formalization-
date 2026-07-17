import RHFormalization.GalerkinDuhamelTraceBound
import RHFormalization.HeatSumBound

/-!
# Brick 2, stone 8: cutoff-independent bound on the Galerkin Duhamel trace
Composing stone 6 (`|Tr| ≤ B²·(∑|d₁|)(∑|d₂|)`) with stone 7 (uniform heat-sum):
the order-2 Duhamel trace of the genuine non-commuting prime operator is bounded
by `B²·(1-e^{-σ(π/L)²})⁻¹·(1-e^{-τ(π/L)²})⁻¹`, INDEPENDENT of the cutoff N.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix Real
open scoped BigOperators

variable {N : ℕ}

/-- Galerkin kinetic eigenvalue on `ℕ`: `((m+1)π/L)²`. -/
noncomputable def galerkinLam (L : ℝ) (m : ℕ) : ℝ := (((m : ℝ) + 1) * Real.pi / L) ^ 2

/-- Weyl lower bound `λ_m ≥ (π/L)²·m`. -/
theorem galerkinLam_growth (L : ℝ) (hL : 0 < L) (m : ℕ) :
    (Real.pi / L) ^ 2 * (m : ℝ) ≤ galerkinLam L m := by
  unfold galerkinLam
  have hquad : (Real.pi / L) ^ 2 * ((m : ℝ) + 1) ^ 2 = (((m : ℝ) + 1) * Real.pi / L) ^ 2 := by
    rw [div_pow, div_pow, mul_pow]; ring
  rw [← hquad]
  have hm1 : (m : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg ((m : ℝ))]
  exact mul_le_mul_of_nonneg_left hm1 (by positivity)

/-- Heat-semigroup weight `d_m = e^{-t·λ_m}` on `Fin N`. -/
noncomputable def heatWeight (L : ℝ) (t : ℝ) (m : Fin N) : ℝ :=
  Real.exp (-(t * galerkinLam L m))

/-- **Stone 8a**: heat-kernel sum over Galerkin modes, uniform in N. -/
theorem sum_heatWeight_le
    (L : ℝ) (hL : 0 < L) (t : ℝ) (ht : 0 < t) :
    ∑ m : Fin N, heatWeight L t m ≤ (1 - Real.exp (-(t * (Real.pi / L) ^ 2)))⁻¹ := by
  unfold heatWeight
  exact sum_exp_neg_le_geometric (galerkinLam L) ((Real.pi / L) ^ 2) t
    (by positivity) ht (galerkinLam_growth L hL)

/-- **Stone 8**: cutoff-independent Duhamel bound for the genuine Galerkin operator. -/
theorem abs_trace_galerkin_duhamel_uniform
    (δ : ℝ) (hδ : 0 < δ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) :
    |(galerkinV δ qs w L * Matrix.diagonal (heatWeight (N := N) L σ)
        * galerkinV δ qs w L * Matrix.diagonal (heatWeight (N := N) L τ)).trace|
      ≤ ((2 / L) * ∑ q ∈ qs, |w q| * bumpMass δ q L) ^ 2
          * ((1 - Real.exp (-(σ * (Real.pi / L) ^ 2)))⁻¹
             * (1 - Real.exp (-(τ * (Real.pi / L) ^ 2)))⁻¹) := by
  have hLnn : (0:ℝ) ≤ L := le_of_lt hL
  refine le_trans (abs_trace_galerkinV_diag_le δ hδ qs w L hLnn _ _) ?_
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hd1 : ∑ n : Fin N, |heatWeight L σ n| ≤ (1 - Real.exp (-(σ * (Real.pi / L) ^ 2)))⁻¹ := by
    have habs : ∀ n : Fin N, |heatWeight L σ n| = heatWeight L σ n := by
      intro n; unfold heatWeight; exact abs_of_pos (Real.exp_pos _)
    simp only [habs]; exact sum_heatWeight_le L hL σ hσ
  have hd2 : ∑ m : Fin N, |heatWeight L τ m| ≤ (1 - Real.exp (-(τ * (Real.pi / L) ^ 2)))⁻¹ := by
    have habs : ∀ m : Fin N, |heatWeight L τ m| = heatWeight L τ m := by
      intro m; unfold heatWeight; exact abs_of_pos (Real.exp_pos _)
    simp only [habs]; exact sum_heatWeight_le L hL τ hτ
  have hboundσ_nonneg : 0 ≤ (1 - Real.exp (-(σ * (Real.pi / L) ^ 2)))⁻¹ := by
    apply inv_nonneg.mpr
    have hlt : Real.exp (-(σ * (Real.pi / L) ^ 2)) < 1 := by
      rw [Real.exp_lt_one_iff]; have : 0 < σ * (Real.pi / L)^2 := by positivity
      linarith
    linarith
  exact mul_le_mul hd1 hd2 (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hboundσ_nonneg

#print axioms sum_heatWeight_le
#print axioms abs_trace_galerkin_duhamel_uniform
end
end RHFormalization
