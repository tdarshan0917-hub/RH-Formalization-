/-
GalerkinStageSequence.lean

The concrete genuine-operator stage exhaustion: alpha n is the galerkin stage
at dimension n+1, free Dirichlet spectrum ((m+1)*pi/L)^2, active prime-power
codes below R = n+1, arithmetic weights, and a definite shift chosen from the
banked existence lemma. Zero hypotheses. This is the alpha the D-export limit
data (B, F, R) will quantify along.
-/
import RHFormalization.GalerkinOpNonnegDischarge
import RHFormalization.PrimeOperatorArithmeticWeights
import RHFormalization.AppendixDActiveSpikeCodesFromCenterCutoff

namespace RHFormalization
noncomputable section
open Real

/-- The genuine free Dirichlet spectrum on the box of width L. -/
def galerkinFreeMu (N : ℕ) (L : ℝ) : Fin N → ℝ :=
  fun m => (((m : ℝ) + 1) * Real.pi / L) ^ 2

/-- A definite shift making the galerkin operator nonnegative. -/
def galerkinStageShift (N : ℕ) (μ : Fin N → ℝ)
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) : ℝ :=
  Classical.choose (exists_shift_making_galerkin_nonneg μ δ qs w L)

theorem galerkinStageShift_spec (N : ℕ) (μ : Fin N → ℝ)
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) :
    ∀ k, growthDrop (galerkinVC (N := N) δ qs w L)
      ≤ μ k + galerkinStageShift N μ δ qs w L :=
  Classical.choose_spec (exists_shift_making_galerkin_nonneg μ δ qs w L)

/-- **The genuine stage exhaustion.** Stage n: dimension n+1, box width 1,
bump width 1, active prime-power codes below n+1, arithmetic prime weights,
definite nonnegativity shift. -/
def galerkinStageSeq (n : ℕ) : DFiniteStage :=
  galerkinOperatorDFiniteStage_ofShift (N := n + 1) n
    (galerkinFreeMu (n + 1) 1)
    1
    (activePrimePowerCodesCenterBelow ((n : ℝ) + 1))
    ppWeightReal
    1
    (galerkinStageShift (n + 1) (galerkinFreeMu (n + 1) 1) 1
      (activePrimePowerCodesCenterBelow ((n : ℝ) + 1)) ppWeightReal 1)
    (galerkinStageShift_spec (n + 1) (galerkinFreeMu (n + 1) 1) 1
      (activePrimePowerCodesCenterBelow ((n : ℝ) + 1)) ppWeightReal 1)

/-- The cutoff radius grows linearly: R at stage n is n+1. -/
theorem galerkinStageSeq_R (n : ℕ) :
    (galerkinStageSeq n).R = (n : ℝ) + 1 := by
  rfl

/-- The stage's F-stage is the genuine perturbed resolvent trace. -/
theorem galerkinStageSeq_F_stage (n : ℕ) :
    (galerkinStageSeq n).appendixDFiniteFStage =
      galerkinPerturbedFStage (N := n + 1)
        (galerkinFreeMu (n + 1) 1) 1
        (activePrimePowerCodesCenterBelow ((n : ℝ) + 1)) ppWeightReal 1 := by
  rfl

#print axioms galerkinStageSeq
#print axioms galerkinStageSeq_R
#print axioms galerkinStageSeq_F_stage

end
end RHFormalization
