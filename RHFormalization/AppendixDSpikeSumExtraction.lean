import RHFormalization.AppendixDPrimePowerFiniteFormulaTarget

/-!
# RHFormalization.AppendixDSpikeSumExtraction

Finite spike-sum bridge for Appendix D.

This file is not an RH endpoint.

It converts the coefficient-level diagonal spike extraction certificate already
stored in each `DFiniteStage`

  `diagonalSpikeContribution q = canonicalSpikeContribution q`

into equality of finite spike sums.

The remaining analytic/model-specific data is:
* `P.B_stage α` equals the finite diagonal spike sum;
* the finite canonical spike sum is the finite canonical prime-power package.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
A finite Nat-indexed spike package.

This is an intermediate layer because the existing fixed-stage extraction data is
indexed by `q : ℕ`, while the canonical prime-power package is indexed by
`PrimePowerPair`.
-/
noncomputable def finiteNatSpikePackage
    (I : Finset ℕ)
    (coeff : ℕ → ℂ)
    (K : ℕ → ℂ → ℂ) :
    ℂ → ℂ :=
  fun s =>
    I.sum (fun q => coeff q * K q s)

/--
If two coefficient functions agree on the finite index set, then the corresponding
finite spike packages agree pointwise.
-/
theorem finiteNatSpikePackage_eq_of_coeff_eq_on_indices
    (I : Finset ℕ)
    (diag canon : ℕ → ℂ)
    (K : ℕ → ℂ → ℂ)
    (hcoeff : ∀ q : ℕ, q ∈ I → diag q = canon q)
    (s : ℂ) :
    finiteNatSpikePackage I diag K s =
      finiteNatSpikePackage I canon K s := by
  dsimp [finiteNatSpikePackage]
  exact
    Finset.sum_congr rfl
      (fun q hq => by
        rw [hcoeff q hq])

/--
Data connecting the existing finite-stage diagonal spike extraction to the
prime-power finite package target.

This is the precise next D-side evidence needed to build
`DFiniteStageCanonicalPrimePowerFormula P`.
-/
structure DFiniteStageSpikeSumData
    (P : DFiniteStagePackage) where
  /-- Nat-indexed active spike indices for each finite stage. -/
  activeIndices :
    DFiniteStage → Finset ℕ

  /-- Kernel attached to a Nat-indexed spike at each finite stage. -/
  spikeKernel :
    DFiniteStage → ℕ → ℂ → ℂ

  /--
  Every index in the finite index set is active for the stage, so the stored
  diagonal extraction certificate applies.
  -/
  h_activeIndices_active :
    ∀ α : DFiniteStage,
    ∀ q : ℕ,
      q ∈ activeIndices α →
        α.diagonalSpikeActive q

  /--
  The D-side finite package is the finite sum of actual diagonal spike
  contributions.
  -/
  h_B_stage_eq_diagonal_sum :
    ∀ α : DFiniteStage,
    ∀ s : ℂ,
      P.B_stage α s =
        finiteNatSpikePackage
          (activeIndices α)
          α.diagonalSpikeContribution
          (spikeKernel α)
          s

  /-- Prime-power indices corresponding to the canonical package. -/
  ppIndices :
    DFiniteStage → Finset PrimePowerPair

  /-- Prime-power kernel corresponding to the canonical package. -/
  ppKernel :
    DFiniteStage → CanonicalKernelC

  /--
  The Nat-indexed canonical spike sum is the same as the canonical prime-power
  package with the frozen normalization.
  -/
  h_canonical_sum_eq_finiteCanonical :
    ∀ α : DFiniteStage,
    ∀ s : ℂ,
      finiteNatSpikePackage
          (activeIndices α)
          α.canonicalSpikeContribution
          (spikeKernel α)
          s =
        finiteCanonicalPrimePowerPackage
          (ppIndices α)
          (ppKernel α)
          s

/--
Build the finite-stage canonical prime-power formula from finite spike-sum data
and the stored diagonal spike extraction certificate.
-/
def buildDFiniteStageCanonicalPrimePowerFormulaFromSpikeSums
    (P : DFiniteStagePackage)
    (S : DFiniteStageSpikeSumData P) :
    DFiniteStageCanonicalPrimePowerFormula P :=
  { indices := S.ppIndices
    kernel := S.ppKernel
    h_B_stage_eq_finiteCanonical := by
      intro α s
      calc
        P.B_stage α s =
            finiteNatSpikePackage
              (S.activeIndices α)
              α.diagonalSpikeContribution
              (S.spikeKernel α)
              s :=
          S.h_B_stage_eq_diagonal_sum α s
        _ =
            finiteNatSpikePackage
              (S.activeIndices α)
              α.canonicalSpikeContribution
              (S.spikeKernel α)
              s := by
          exact
            finiteNatSpikePackage_eq_of_coeff_eq_on_indices
              (S.activeIndices α)
              α.diagonalSpikeContribution
              α.canonicalSpikeContribution
              (S.spikeKernel α)
              (fun q hq =>
                α.h_diagonalSpikeExtraction q
                  (S.h_activeIndices_active α q hq))
              s
        _ =
            finiteCanonicalPrimePowerPackage
              (S.ppIndices α)
              (S.ppKernel α)
              s :=
          S.h_canonical_sum_eq_finiteCanonical α s }

end

end RHFormalization
