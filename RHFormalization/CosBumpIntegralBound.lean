import RHFormalization.BumpMatrixElementCosForm

/-!
# Brick 2, stone 3b-0: uniform bound `|C_j(q)| ≤ ∫₀ᴸ W(x−log q) dx`.
Foundational boundedness of V (|cos| ≤ 1, W > 0); first ingredient of the KLMN
relative-form bound.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Real MeasureTheory intervalIntegral
open scoped Real

/-- Total bump mass `∫₀ᴸ W(x−log q) dx`. -/
noncomputable def bumpMass (δ : ℝ) (q : ℕ) (L : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L, gaussBump δ (x - Real.log q)

theorem intervalIntegrable_gaussBump (δ : ℝ) (q : ℕ) (L : ℝ) :
    IntervalIntegrable (fun x : ℝ => gaussBump δ (x - Real.log q))
      MeasureTheory.volume 0 L := by
  have : Continuous (fun x : ℝ => gaussBump δ (x - Real.log q)) := by
    unfold gaussBump; fun_prop
  exact this.intervalIntegrable 0 L

/-- **Stone 3b-0**: `|C_j(q)| ≤ ∫₀ᴸ W(x−log q) dx`, uniformly in `j`. -/
theorem abs_cosBumpIntegral_le_bumpMass
    (δ : ℝ) (hδ : 0 < δ) (q : ℕ) (L : ℝ) (hL : 0 ≤ L) (j : ℝ) :
    |cosBumpIntegral δ q L j| ≤ bumpMass δ q L := by
  unfold cosBumpIntegral bumpMass
  calc |∫ x in (0:ℝ)..L, Real.cos (j * Real.pi * x / L) * gaussBump δ (x - Real.log q)|
      ≤ ∫ x in (0:ℝ)..L, |Real.cos (j * Real.pi * x / L) * gaussBump δ (x - Real.log q)| := by
        apply intervalIntegral.abs_integral_le_integral_abs hL
    _ ≤ ∫ x in (0:ℝ)..L, gaussBump δ (x - Real.log q) := by
        apply intervalIntegral.integral_mono_on hL
        · exact ((continuous_cosBumpIntegrand δ q L j).abs).intervalIntegrable 0 L
        · exact intervalIntegrable_gaussBump δ q L
        · intro x _
          rw [abs_mul]
          calc |Real.cos (j * Real.pi * x / L)| * |gaussBump δ (x - Real.log q)|
              ≤ 1 * |gaussBump δ (x - Real.log q)| :=
                mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
            _ = gaussBump δ (x - Real.log q) := by
                rw [one_mul, abs_of_pos (gaussBump_pos δ hδ _)]

#print axioms abs_cosBumpIntegral_le_bumpMass
end
end RHFormalization
