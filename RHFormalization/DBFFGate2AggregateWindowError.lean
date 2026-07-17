import RHFormalization.CanonicalPrimePowerUniformWindowError
import Mathlib

/-!
# DBFFGate2AggregateWindowError

This file performs only the genuine termwise-to-aggregate step.

It does not assert that the raw mass

  ∑ q ∈ A, ‖q.weightC‖

is uniformly bounded for the live admissible stages.

For the live Gate-2/O3 route, the relevant quantity carries the density
normalization `1 / (2 * L)`.  The final theorem below therefore leaves the
normalized mass estimate explicit instead of hiding it in an unproved raw-mass
hypothesis.

The domain issue is also unchanged: any concrete kernel-window estimate used
to instantiate these lemmas retains its own overlap-half-plane hypotheses.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

/--
Finite-sum aggregation of the banked pointwise canonical prime-power
window-error estimate.

This theorem contains no uniform-in-stage mass assertion.
-/
theorem canonicalPrimePowerActualTermError_sum_le_weight_sum_mul_window
    (X : DFiniteStagePackageFromOperatorLayer)
    (alpha : ℕ → DFiniteStage)
    (Kshared : CanonicalKernelC)
    (s : ℂ)
    (n : ℕ)
    (A : Finset PrimePowerPair)
    (windowError : ℝ)
    (hkernel :
      ∀ q ∈ A,
        ‖X.toFiniteCanonicalPrimePowerFormula.kernel
              (alpha n) q.center s
            - Kshared q.center s‖
          ≤ windowError) :
    (∑ q ∈ A,
        canonicalPrimePowerActualTermError
          X alpha Kshared s n q)
      ≤
    (∑ q ∈ A, ‖q.weightC‖) * windowError := by
  classical
  calc
    (∑ q ∈ A,
        canonicalPrimePowerActualTermError
          X alpha Kshared s n q)
        ≤
      ∑ q ∈ A, ‖q.weightC‖ * windowError := by
        refine Finset.sum_le_sum ?_
        intro q hq
        exact
          canonicalPrimePowerActualTermError_le_weight_norm_mul_window
            X alpha Kshared s n q windowError
            (hkernel q hq)
    _ =
      (∑ q ∈ A, ‖q.weightC‖) * windowError := by
        rw [Finset.sum_mul]

/--
Density-normalized aggregate estimate.

The hypothesis `hnormalizedMass` is intentionally explicit.  For the live
admissible construction it must be discharged using the actual density and
active prime-power set; this theorem does not replace that analytic estimate.
-/
theorem canonicalPrimePowerActualTermError_density_normalized_sum_le
    (X : DFiniteStagePackageFromOperatorLayer)
    (alpha : ℕ → DFiniteStage)
    (Kshared : CanonicalKernelC)
    (s : ℂ)
    (n : ℕ)
    (A : Finset PrimePowerPair)
    (windowError density normalizedMassBound : ℝ)
    (hkernel :
      ∀ q ∈ A,
        ‖X.toFiniteCanonicalPrimePowerFormula.kernel
              (alpha n) q.center s
            - Kshared q.center s‖
          ≤ windowError)
    (hdensity : 0 ≤ density)
    (hwindow : 0 ≤ windowError)
    (hnormalizedMass :
      density * (∑ q ∈ A, ‖q.weightC‖)
        ≤ normalizedMassBound) :
    density *
        (∑ q ∈ A,
          canonicalPrimePowerActualTermError
            X alpha Kshared s n q)
      ≤
    normalizedMassBound * windowError := by
  have hsum :
      (∑ q ∈ A,
          canonicalPrimePowerActualTermError
            X alpha Kshared s n q)
        ≤
      (∑ q ∈ A, ‖q.weightC‖) * windowError :=
    canonicalPrimePowerActualTermError_sum_le_weight_sum_mul_window
      (X := X)
      (alpha := alpha)
      (Kshared := Kshared)
      (s := s)
      (n := n)
      (A := A)
      (windowError := windowError)
      (hkernel := hkernel)

  calc
    density *
        (∑ q ∈ A,
          canonicalPrimePowerActualTermError
            X alpha Kshared s n q)
        ≤
      density *
        ((∑ q ∈ A, ‖q.weightC‖) * windowError) :=
          mul_le_mul_of_nonneg_left hsum hdensity
    _ =
      (density * (∑ q ∈ A, ‖q.weightC‖)) * windowError := by
        ring
    _ ≤
      normalizedMassBound * windowError :=
        mul_le_mul_of_nonneg_right hnormalizedMass hwindow

/--
The density-normalized aggregate estimate in the precise `1 / (2 * L)` form
used by the prime-weighted operator normalization.
-/
theorem canonicalPrimePowerActualTermError_one_div_two_length_sum_le
    (X : DFiniteStagePackageFromOperatorLayer)
    (alpha : ℕ → DFiniteStage)
    (Kshared : CanonicalKernelC)
    (s : ℂ)
    (n : ℕ)
    (A : Finset PrimePowerPair)
    (L windowError normalizedMassBound : ℝ)
    (hL : 0 < L)
    (hkernel :
      ∀ q ∈ A,
        ‖X.toFiniteCanonicalPrimePowerFormula.kernel
              (alpha n) q.center s
            - Kshared q.center s‖
          ≤ windowError)
    (hwindow : 0 ≤ windowError)
    (hnormalizedMass :
      (1 / (2 * L)) * (∑ q ∈ A, ‖q.weightC‖)
        ≤ normalizedMassBound) :
    (1 / (2 * L)) *
        (∑ q ∈ A,
          canonicalPrimePowerActualTermError
            X alpha Kshared s n q)
      ≤
    normalizedMassBound * windowError := by
  have h2L : 0 < (2 : ℝ) * L :=
    mul_pos (by norm_num) hL

  have hdensity : 0 ≤ (1 / (2 * L) : ℝ) :=
    le_of_lt (one_div_pos.mpr h2L)

  exact
    canonicalPrimePowerActualTermError_density_normalized_sum_le
      (X := X)
      (alpha := alpha)
      (Kshared := Kshared)
      (s := s)
      (n := n)
      (A := A)
      (windowError := windowError)
      (density := 1 / (2 * L))
      (normalizedMassBound := normalizedMassBound)
      (hkernel := hkernel)
      (hdensity := hdensity)
      (hwindow := hwindow)
      (hnormalizedMass := hnormalizedMass)

#print axioms canonicalPrimePowerActualTermError_sum_le_weight_sum_mul_window
#print axioms canonicalPrimePowerActualTermError_density_normalized_sum_le
#print axioms canonicalPrimePowerActualTermError_one_div_two_length_sum_le

end

end RHFormalization
