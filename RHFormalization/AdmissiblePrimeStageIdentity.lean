import RHFormalization.AdmissibleFreeFH

/-!
# RHFormalization.AdmissiblePrimeStageIdentity

**Front F-adm, brick 2b-i.** The exact finite-n representation of the prime
layer: `FadmPrimeStage` IS the density-normalized difference of the perturbed
and free finite resolvent traces (both shifted by `SupVConst`). Pure algebra —
pins the object that the Duhamel representation (2b-ii) must expand. The
residual stays combined downstream (hQint discipline).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- The perturbed spectrum at the admissible stage (genuine eigenvalues of
`K + galerkinV` at window `admL n`, dimension `admN n`, primes below `n+1`). -/
def admPerturbedLam (n : ℕ) : Fin (admN n) → ℝ :=
  fun i => perturbedEigenvalues (galerkinFreeMu (admN n) (admL n))
    (galerkinVC_isHermitian (N := admN n) 1
      (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n)) i

/-- **Brick 2b-i: exact prime-layer representation.** The prime stage equals
the density constant times (perturbed trace − free trace), both at shift
`SupVConst`. -/
theorem FadmPrimeStage_eq_trace_diff (n : ℕ) (s : ℂ) :
    FadmPrimeStage n s
      = admDensityC n *
          (FstageFinite (fun i => admPerturbedLam n i + SupVConst) s
            - FstageFinite (fun i : Fin (admN n) =>
                SupVConst + galerkinFreeMu (admN n) (admL n) i) s) := by
  unfold FadmPrimeStage
  rw [galerkinStagePackage_F_at_admissible n s,
    admissibleFreeStage_eq_FstageFinite n s]
  have hshift : galerkinPerturbedFStage (N := admN n)
      (galerkinFreeMu (admN n) (admL n)) 1
      (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
      (admL n) (s + (SupVConst : ℂ))
      = FstageFinite (fun i => admPerturbedLam n i + SupVConst) s := by
    unfold admPerturbedLam
    exact perturbedFStage_shift_eq (galerkinFreeMu (admN n) (admL n))
      (galerkinVC_isHermitian (N := admN n) 1
        (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
        (admL n)) SupVConst s
  rw [hshift]
  ring

/-- Termwise form: the prime stage is the density-normalized sum of resolvent
differences over the finite spectrum — the shape the second-resolvent-identity
expansion (2b-ii) attaches to. -/
theorem FadmPrimeStage_eq_sum_diff (n : ℕ) (s : ℂ) :
    FadmPrimeStage n s
      = admDensityC n *
          ∑ i : Fin (admN n),
            ((s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ))⁻¹
              - (s + ((SupVConst + galerkinFreeMu (admN n) (admL n) i : ℝ) : ℂ))⁻¹) := by
  rw [FadmPrimeStage_eq_trace_diff n s]
  congr 1
  unfold FstageFinite
  rw [← Finset.sum_sub_distrib]

#print axioms FadmPrimeStage_eq_trace_diff
#print axioms FadmPrimeStage_eq_sum_diff

end

end RHFormalization
