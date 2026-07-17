import RHFormalization.AppendixDPrimePowerPairCode
import RHFormalization.CanonicalPrimePowerPackage
import RHFormalization.PrimeOperatorArithmeticWeights
import RHFormalization.PrimePotentialPosition
import RHFormalization.AdmissibleWeightNonneg
import RHFormalization.GalerkinMatrices
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Real
open scoped BigOperators

variable {N : ℕ}

/--
Prime potential indexed by Nat codes, but spatially centered at the decoded
prime-power center `log (p^m)` rather than at `log (ppCode (p,m))`.

This is the manuscript-faithful position-space potential to be consumed by
the corrected admissible Galerkin F-stage.
-/
noncomputable def decodedPrimePotentialFn
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (x : ℝ) : ℝ :=
  ∑ k ∈ qs,
    w k * gaussBump δ (x - (ppDecode k).center)

/--
Matrix element of the decoded-center position-space potential in the
Dirichlet sine basis.
-/
noncomputable def decodedVmatrixElement
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L : ℝ)
    (m n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..L,
    dirichletEigenfun m L x
      * decodedPrimePotentialFn δ qs w x
      * dirichletEigenfun n L x

/--
Raw decoded-center Galerkin matrix.
-/
noncomputable def decodedGalerkinVRaw
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun m n =>
    decodedVmatrixElement
      δ qs w L
      ((m : ℕ) + 1)
      ((n : ℕ) + 1)

/--
Normalized decoded-center Galerkin matrix, with the live `2 / L`
Dirichlet-basis normalization.
-/
noncomputable def decodedGalerkinV
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun m n =>
    (2 / L) *
      decodedVmatrixElement
        δ qs w L
        ((m : ℕ) + 1)
        ((n : ℕ) + 1)

/--
Atomic center check: a coded singleton produces the physical prime-power
center and weight after decoding.
-/
theorem decodedPrimePotentialFn_singleton_ppCode
    (δ x : ℝ)
    (q : PrimePowerPair) :
    decodedPrimePotentialFn
        δ {ppCode q} ppWeightReal x
      =
    q.weightReal *
      gaussBump δ (x - q.center) := by
  simp
    [decodedPrimePotentialFn,
     ppWeightReal,
     ppDecode_ppCode,
     PrimePowerPair.weightC]

/--
The decoded-center arithmetic potential is pointwise nonnegative.
-/
theorem decodedPrimePotentialFn_nonneg
    (δ : ℝ)
    (hδ : 0 < δ)
    (qs : Finset ℕ)
    (x : ℝ) :
    0 ≤ decodedPrimePotentialFn
      δ qs ppWeightReal x := by
  unfold decodedPrimePotentialFn
  apply Finset.sum_nonneg
  intro k _
  exact
    mul_nonneg
      (ppWeightReal_nonneg k)
      (le_of_lt
        (gaussBump_pos
          δ hδ
          (x - (ppDecode k).center)))

/--
Decoded-center matrix elements are symmetric.
-/
theorem decodedVmatrixElement_symm
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L : ℝ)
    (m n : ℕ) :
    decodedVmatrixElement δ qs w L m n
      =
    decodedVmatrixElement δ qs w L n m := by
  unfold decodedVmatrixElement
  congr 1
  funext x
  ring

/--
The normalized decoded-center Galerkin matrix is symmetric.
-/
theorem decodedGalerkinV_symm
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L : ℝ)
    (m n : Fin N) :
    decodedGalerkinV δ qs w L m n
      =
    decodedGalerkinV δ qs w L n m := by
  unfold decodedGalerkinV
  rw [decodedVmatrixElement_symm]

#print axioms decodedPrimePotentialFn_singleton_ppCode
#print axioms decodedPrimePotentialFn_nonneg
#print axioms decodedVmatrixElement_symm
#print axioms decodedGalerkinV_symm

end

end RHFormalization
