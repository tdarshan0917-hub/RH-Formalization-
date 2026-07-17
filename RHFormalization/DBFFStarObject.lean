import RHFormalization.DBFFBStageDirichletForm
import RHFormalization.DBFFCompensatorMainTerm
import RHFormalization.DBFFDeficitCompactBound

/-!
# DBFFStarObject — the discrete (★) object and the D.OP.2 identity

ROUTE CARD
1. Target: Lemma D.OP.2 statement layer, closed. `B_stage − M_α` factors as
   `(2√(s+1/4))⁻¹ · starObject`, where `starObject` is the discrete Stieltjes
   error (Dirichlet partial sum − truncated main term − fixed term). The
   compact-uniform bound on `starObject` is EXACTLY obligation O3.
2. Objects: `galerkin_B_stage_eq_vonMangoldt_partial_sum` (banked),
   `compensatorM_eq_mainTerm` (banked), `kernel_norm_le_on_compact` route
   donors from DBFFDeficitCompactBound.
3. Raw B on Ω? NO — per-stage finite identity, no continuation claim.
4. R = F − raw B forced? NO. 5. Identity true outright; the bound is the
   named hypothesis O3 (NOT claimed here).
6. Manuscript: D.OP-BOUND, Lemma D.OP.2 / obligation O3.
7. Consumer: O3 (operator-side proof fills `hstar`); D.OP-BOUND assembly.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Finset ArithmeticFunction

/-- **The discrete (★) object**: von Mangoldt Dirichlet partial sum at
`w + 1/2` up to `⌊e^{admR n}⌋`, minus the truncated Stieltjes main term,
minus the fixed term `(1/2−w)⁻¹`, at `w = √(s+1/4)`. -/
def starObject (n : ℕ) (s : ℂ) : ℂ :=
  (∑ k ∈ Finset.Ioc 0 ⌊Real.exp (admR n)⌋₊,
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)) k)
  - mainTermIntegral n s
  - 1 / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ)))

/-- **D.OP.2 factored identity** (per stage, on Ω): the compensated B-side
is `(2√(s+1/4))⁻¹` times the discrete (★) object. -/
theorem B_sub_compensator_eq (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
        - compensatorM n s
      = (1 / (2 * Complex.sqrt (s + (1/4:ℂ)))) * starObject n s := by
  have hB := galerkin_B_stage_eq_vonMangoldt_partial_sum n s
  have hM := compensatorM_eq_mainTerm n hs
  have hRfl : (admissibleGalerkinStageSeq n).R = admR n := rfl
  rw [hRfl] at hB
  rw [hB, hM]
  unfold starObject
  ring

/-- **D.OP.2 transfer.** If the discrete (★) object is uniformly bounded over
stages on a compact `K ⊆ Ω` — obligation **O3**, the hypothesis `hstar` — and
the kernel prefactor is bounded on `K` by `c⁻¹` (banked compact geometry),
then the compensated B-side is uniformly bounded on `K`: the boundedness
input D.OP-BOUND claims. -/
theorem compensated_B_bounded_of_starObject_bounded
    (K : Set ℂ) (hK : K ⊆ Ω)
    (c : ℝ) (hc : 0 < c)
    (hker : ∀ s ∈ K, ‖(1:ℂ) / (2 * Complex.sqrt (s + (1/4:ℂ)))‖ ≤ c⁻¹)
    (Cstar : ℝ)
    (hstar : ∀ n : ℕ, ∀ s ∈ K, ‖starObject n s‖ ≤ Cstar) :
    ∀ n : ℕ, ∀ s ∈ K,
      ‖galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
          - compensatorM n s‖ ≤ c⁻¹ * Cstar := by
  intro n s hsK
  have hsΩ : s ∈ Ω := hK hsK
  rw [B_sub_compensator_eq n hsΩ, norm_mul]
  have hCstar0 : (0:ℝ) ≤ Cstar := le_trans (norm_nonneg _) (hstar n s hsK)
  have hcinv0 : (0:ℝ) ≤ c⁻¹ := (inv_pos.mpr hc).le
  first
    | exact mul_le_mul (hker s hsK) (hstar n s hsK) (norm_nonneg _) hcinv0
    | (apply mul_le_mul (hker s hsK) (hstar n s hsK) (norm_nonneg _) hcinv0)

#print axioms starObject
#print axioms B_sub_compensator_eq
#print axioms compensated_B_bounded_of_starObject_bounded

end

end RHFormalization
