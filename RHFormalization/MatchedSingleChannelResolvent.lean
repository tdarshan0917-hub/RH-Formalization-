-- SENTINEL: matched-single-channel-resolvent-v1
import RHFormalization.CouplingExpansionStage1
import RHFormalization.DecodedGalerkinFStageForwardGate
import RHFormalization.GalerkinCanonicalFSlot
import RHFormalization.DecodedPrimePotentialBumpSplit
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module
open scoped BigOperators Classical

variable {N : ℕ}

/--
The unweighted matrix of one physical Gaussian bump at the decoded
prime-power center.  Arithmetic weight is deliberately absent here.
-/
def decodedSingleBumpVC
    (δ : ℝ) (k : ℕ) (L : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    (((2 / L) *
      decodedBumpMatrixElement δ k L
        ((i : ℕ) + 1) ((j : ℕ) + 1) : ℝ) : ℂ)

/--
The actual matched one-channel potential.

The singleton decoded potential already contains exactly one copy of

  ppWeightReal k = Λ(q)/√q.

No outer arithmetic coefficient should multiply this channel later.
-/
def matchedSingleChannelVC
    (k : ℕ) (L : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  decodedGalerkinVC (N := N) 1 {k} ppWeightReal L

/--
Weight-placement lock: the matched singleton potential is exactly one
arithmetic weight times the unweighted bump matrix.
-/
theorem matchedSingleChannelVC_eq_weight_smul_singleBump
    (k : ℕ) (L : ℝ) :
    matchedSingleChannelVC (N := N) k L
      =
    ((ppWeightReal k : ℝ) : ℂ) •
      decodedSingleBumpVC (N := N) 1 k L := by
  ext i j
  unfold matchedSingleChannelVC decodedSingleBumpVC
    decodedGalerkinVC decodedGalerkinV
  rw [decodedVmatrixElement_eq_sum_bumps]
  simp
  push_cast
  ring

/-- The actual singleton potential is Hermitian. -/
theorem matchedSingleChannelVC_isHermitian
    (k : ℕ) (L : ℝ) :
    (matchedSingleChannelVC (N := N) k L).IsHermitian := by
  exact decodedGalerkinVC_isHermitian
    (N := N) 1 {k} ppWeightReal L

/-- Matching displacement observable at the same decoded center. -/
def matchedSingleChannelTC
    (k : ℕ) (L : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  galerkinTC (N := N) L (ppDecode k).center

/-- Free matched-channel response. -/
def matchedSingleChannelFreeResponse
    (μ : Fin N → ℝ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
    (Matrix.toEuclideanLin
        (matchedSingleChannelTC (N := N) k L)
      * freeResolventOpE μ z)

/-- Fully interacting matched-channel response. -/
def matchedSingleChannelPerturbedResponse
    (μ : Fin N → ℝ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
    (Matrix.toEuclideanLin
        (matchedSingleChannelTC (N := N) k L)
      * perturbedResolventOp μ
          (matchedSingleChannelVC_isHermitian
            (N := N) k L) z)

/--
The canonical first-Born channel.  It contains the arithmetic coefficient
once, through `matchedSingleChannelVC`.
-/
def matchedSingleChannelFirstBorn
    (μ : Fin N → ℝ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  -(LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
    (Matrix.toEuclideanLin
        (matchedSingleChannelTC (N := N) k L)
      * freeResolventOpE μ z
      * Matrix.toEuclideanLin
          (matchedSingleChannelVC (N := N) k L)
      * freeResolventOpE μ z))

/--
Exact nonlinear remainder retaining the full singleton interacting
resolvent.  Its quadratic weight is legitimate because it is a remainder,
not the canonical linear term.
-/
def matchedSingleChannelSecondRemainder
    (μ : Fin N → ℝ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
    (Matrix.toEuclideanLin
        (matchedSingleChannelTC (N := N) k L)
      * freeResolventOpE μ z
      * Matrix.toEuclideanLin
          (matchedSingleChannelVC (N := N) k L)
      * perturbedResolventOp μ
          (matchedSingleChannelVC_isHermitian
            (N := N) k L) z
      * Matrix.toEuclideanLin
          (matchedSingleChannelVC (N := N) k L)
      * freeResolventOpE μ z)

/--
ACTUAL MATCHED SINGLE-CHANNEL EXPANSION.

No global potential, no outer arithmetic weight, and no mixed channel.
The singleton potential itself supplies exactly one weight to the
first-Born term.
-/
theorem matchedSingleChannel_response_eq_first_plus_second
    (μ : Fin N → ℝ) (k : ℕ) (L : ℝ) (z : ℂ)
    (hneF : ∀ i, z + ((μ i : ℝ) : ℂ) ≠ 0)
    (hneP : ∀ i,
      z + ((perturbedEigenvalues μ
        (matchedSingleChannelVC_isHermitian
          (N := N) k L) i : ℝ) : ℂ) ≠ 0) :
    matchedSingleChannelPerturbedResponse
        (N := N) μ k L z
      -
    matchedSingleChannelFreeResponse
        (N := N) μ k L z
      =
    matchedSingleChannelFirstBorn
        (N := N) μ k L z
      +
    matchedSingleChannelSecondRemainder
        (N := N) μ k L z := by
  unfold matchedSingleChannelPerturbedResponse
    matchedSingleChannelFreeResponse
    matchedSingleChannelFirstBorn
    matchedSingleChannelSecondRemainder
    matchedSingleChannelTC

  exact paired_resolvent_sub_eq_first_plus_second
    μ
    (matchedSingleChannelVC_isHermitian
      (N := N) k L)
    (galerkinTC (N := N) L (ppDecode k).center)
    z hneF hneP

#print axioms decodedSingleBumpVC
#print axioms matchedSingleChannelVC
#print axioms matchedSingleChannelVC_eq_weight_smul_singleBump
#print axioms matchedSingleChannelVC_isHermitian
#print axioms matchedSingleChannelTC
#print axioms matchedSingleChannel_response_eq_first_plus_second

end

end RHFormalization
