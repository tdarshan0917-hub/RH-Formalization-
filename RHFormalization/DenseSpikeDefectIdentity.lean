/-
STAGE B(i) — Brick 2: the F^sp EXACT IDENTITY (GPT-signed).
Fsp := Pcont − Pgal = 2·BcorrWinDense − 2·denseGalerkinTransformDefect,
where Pcont = Σ w(q)·K(a_q,s) (= B_stage, rfl) and Pgal = 2·densePaired
(B(i)-1 pin). Consequence: sup_{n,s∈K}|Fsp| ≤ 2C_w + 2C_d via the banked
D5 + D4b bounds — the aggregate spike defect closes with NO new estimate.
-/

import RHFormalization.DenseCenteredObservable
import RHFormalization.DenseSealEndpoint
import RHFormalization.DenseWindowBound

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- The continuum spike pairing `P^cont = Σ_q w(q)·K(q.center, s)`. -/
def densePcont (n : ℕ) (s : ℂ) : ℂ :=
  ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
    q.weightC * shiftedLaplaceHeatKernelC q.center s

/-- `P^cont` is the admissible B-stage (definitional). -/
theorem densePcont_eq_Bstage (n : ℕ) (s : ℂ) :
    densePcont n s
      = galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s := rfl

/-- The spike defect `F^sp = P^cont − P^gal = P^cont − 2·densePaired`. -/
def denseFsp (n : ℕ) (s : ℂ) : ℂ :=
  densePcont n s - (2 : ℂ) * denseFreePairedTransform n s

/-- **THE F^sp EXACT IDENTITY** (certified algebra; no estimate). -/
theorem denseFsp_eq (n : ℕ) (s : ℂ) :
    denseFsp n s
      = (2 : ℂ) * BcorrWinDense n s
        - (2 : ℂ) * denseGalerkinTransformDefect n s := by
  unfold denseFsp
  rw [densePcont_eq_Bstage]
  have hlock := denseFreePairedTransform_route_lock n s
  linear_combination (-2 : ℂ) * hlock

/-- **F^sp compact-uniform bound — closed by D5 + D4b, no new analysis.** -/
theorem denseFsp_uniform_bound
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖denseFsp n s‖ ≤ C := by
  obtain ⟨Cw, hw⟩ := BcorrWinDense_uniform_bound K hK hKΩ
  obtain ⟨Cd, hd⟩ := denseGalerkinTransformDefect_loc_bdd K hKΩ hK
  refine ⟨2 * Cw + 2 * Cd, fun n s hs => ?_⟩
  rw [denseFsp_eq]
  have e2 : ‖(2:ℂ)‖ = 2 := by norm_num
  calc ‖(2:ℂ) * BcorrWinDense n s - (2:ℂ) * denseGalerkinTransformDefect n s‖
      ≤ ‖(2:ℂ) * BcorrWinDense n s‖
          + ‖(2:ℂ) * denseGalerkinTransformDefect n s‖ := norm_sub_le _ _
    _ = 2 * ‖BcorrWinDense n s‖
          + 2 * ‖denseGalerkinTransformDefect n s‖ := by
        rw [norm_mul, norm_mul, e2]
    _ ≤ 2 * Cw + 2 * Cd := by
        have h1 := hw n s hs
        have h2 := hd n s hs
        linarith

#print axioms densePcont_eq_Bstage
#print axioms denseFsp_eq
#print axioms denseFsp_uniform_bound

end

end RHFormalization
