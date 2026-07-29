-- SENTINEL: matched-admissible-channel-stage-v1
import RHFormalization.MatchedPrimeChannelSum
import RHFormalization.DecodedAdaptivePrimeSplit
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Module
open scoped BigOperators Classical

/--
Density-normalized sum of the singleton interacting response differences
at the literal admissible stage.
-/
def matchedAdmissiblePerturbedDifference
    (n : ℕ) (s : ℂ) : ℂ :=
  admDensityC n *
    matchedPrimeChannelPerturbedDifference
      (N := admN n)
      (galerkinFreeMu (admN n) (admL n))
      (activePrimePowerCodesCenterBelow (admR n))
      (admL n)
      (s + (SupVConst : ℂ))

/--
Density-normalized matched first-Born sum at the literal admissible stage.

Each singleton potential already contains exactly one copy of
`ppWeightReal k = Λ(q)/√q`.
-/
def matchedAdmissibleFirstBornSum
    (n : ℕ) (s : ℂ) : ℂ :=
  admDensityC n *
    matchedPrimeChannelFirstBornSum
      (N := admN n)
      (galerkinFreeMu (admN n) (admL n))
      (activePrimePowerCodesCenterBelow (admR n))
      (admL n)
      (s + (SupVConst : ℂ))

/--
Density-normalized matched nonlinear remainder at the literal admissible
stage.
-/
def matchedAdmissibleSecondRemainderSum
    (n : ℕ) (s : ℂ) : ℂ :=
  admDensityC n *
    matchedPrimeChannelSecondRemainderSum
      (N := admN n)
      (galerkinFreeMu (admN n) (admL n))
      (activePrimePowerCodesCenterBelow (admR n))
      (admL n)
      (s + (SupVConst : ℂ))

/--
The free admissible spectrum is nonnegative.
-/
theorem matchedAdmissible_freeMu_nonneg
    (n : ℕ) :
    ∀ i : Fin (admN n),
      0 ≤ galerkinFreeMu (admN n) (admL n) i := by
  intro i
  first
    | exact galerkinFreeMu_nonneg _ _ i
    | (unfold galerkinFreeMu; positivity)
    | exact sq_nonneg _

/--
Every singleton perturbed eigenvalue at the admissible stage is
nonnegative.
-/
theorem matchedAdmissible_singletonEigenvalue_nonneg
    (n k : ℕ) (i : Fin (admN n)) :
    0 ≤ perturbedEigenvalues
      (galerkinFreeMu (admN n) (admL n))
      (matchedSingleChannelVC_isHermitian
        (N := admN n) k (admL n)) i := by
  have hL : 0 < admL n := by
    first
      | exact admL_pos n
      | (unfold admL; positivity)

  have hraw :=
    decodedEigenvalue_nonneg
      (N := admN n)
      (admL n) hL
      ({k} : Finset ℕ)
      (galerkinFreeMu (admN n) (admL n))
      (matchedAdmissible_freeMu_nonneg n)
      i

  simpa [matchedSingleChannelVC] using hraw

/--
The shifted free singleton denominator avoids zero on Ω.
-/
theorem matchedAdmissible_freeDenominator_ne
    (n : ℕ) {s : ℂ} (hs : s ∈ Ω)
    (i : Fin (admN n)) :
    (s + (SupVConst : ℂ))
        + ((galerkinFreeMu
              (admN n) (admL n) i : ℝ) : ℂ) ≠ 0 := by
  have hμ :=
    matchedAdmissible_freeMu_nonneg n i

  have hcast :
      (s + (SupVConst : ℂ))
          + ((galerkinFreeMu
                (admN n) (admL n) i : ℝ) : ℂ)
        =
      s + ((SupVConst
          + galerkinFreeMu
              (admN n) (admL n) i : ℝ) : ℂ) := by
    push_cast
    ring

  rw [hcast]
  exact add_real_ne_zero_of_mem_Omega hs
    (add_nonneg SupVConst_nonneg_adm hμ)

/--
The shifted singleton perturbed denominator avoids zero on Ω.
-/
theorem matchedAdmissible_perturbedDenominator_ne
    (n k : ℕ) {s : ℂ} (hs : s ∈ Ω)
    (i : Fin (admN n)) :
    (s + (SupVConst : ℂ))
        + ((perturbedEigenvalues
              (galerkinFreeMu (admN n) (admL n))
              (matchedSingleChannelVC_isHermitian
                (N := admN n) k (admL n)) i : ℝ) : ℂ) ≠ 0 := by
  have hlam :=
    matchedAdmissible_singletonEigenvalue_nonneg n k i

  have hcast :
      (s + (SupVConst : ℂ))
          + ((perturbedEigenvalues
                (galerkinFreeMu (admN n) (admL n))
                (matchedSingleChannelVC_isHermitian
                  (N := admN n) k (admL n)) i : ℝ) : ℂ)
        =
      s + ((SupVConst
          + perturbedEigenvalues
              (galerkinFreeMu (admN n) (admL n))
              (matchedSingleChannelVC_isHermitian
                (N := admN n) k (admL n)) i : ℝ) : ℂ) := by
    push_cast
    ring

  rw [hcast]
  exact add_real_ne_zero_of_mem_Omega hs
    (add_nonneg SupVConst_nonneg_adm hlam)

/--
LIVE ADMISSIBLE MATCHED-CHANNEL IDENTITY.

This is the literal admissible schedule, active prime-power code set,
density normalization, frozen arithmetic weight, and shifted spectral
parameter.

No boundedness or RH-equivalent hypothesis is consumed.
-/
theorem matchedAdmissible_sum_eq_first_plus_second
    (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    matchedAdmissiblePerturbedDifference n s
      =
    matchedAdmissibleFirstBornSum n s
      +
    matchedAdmissibleSecondRemainderSum n s := by
  unfold matchedAdmissiblePerturbedDifference
    matchedAdmissibleFirstBornSum
    matchedAdmissibleSecondRemainderSum

  exact
    matchedPrimeChannel_scalar_mul_sum_eq_first_plus_second
      (N := admN n)
      (admDensityC n)
      (galerkinFreeMu (admN n) (admL n))
      (activePrimePowerCodesCenterBelow (admR n))
      (admL n)
      (s + (SupVConst : ℂ))
      (fun i =>
        matchedAdmissible_freeDenominator_ne n hs i)
      (fun k _hk i =>
        matchedAdmissible_perturbedDenominator_ne n k hs i)

#print axioms matchedAdmissible_freeMu_nonneg
#print axioms matchedAdmissible_singletonEigenvalue_nonneg
#print axioms matchedAdmissible_freeDenominator_ne
#print axioms matchedAdmissible_perturbedDenominator_ne
#print axioms matchedAdmissible_sum_eq_first_plus_second

end

end RHFormalization
