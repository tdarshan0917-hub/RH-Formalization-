import RHFormalization.DBFFM2ExactResidualExpansion
import RHFormalization.SeamCoreForm

/-!
# RHFormalization.DBFFM2TotalProfileErrorLocBdd
**THE FROZEN GO/NO-GO STATEMENT.** No proof here — statement only.

The complete M2 total profile error: the exact Gaussian-smoothed,
Λ(q)/√q-weighted finite-stage F-slot expansion (Gate 1's RHS, verbatim)
minus the arithmetic seam profile (seamCore), uniformly bounded in n on
every compact K ⊆ Ω. Uses only concrete repo objects. NO Htail, Hstar,
RH, or zero-free hypothesis. Every future brick must name which conjunct
of this Prop it advances, or it is an island.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set

/-- The complete stage total-profile error at stage `n`, point `s`:
Gate 1's exact expanded F-slot minus the arithmetic seam core. -/
noncomputable def m2TotalProfileError (n : ℕ) (s : ℂ) : ℂ :=
  admDensityC n *
      (FstageFinite (fun m : Fin (admN n) =>
          galerkinLam (admL n) (m : ℕ)) (s + (SupVConst : ℂ))
        - (∑ k ∈ activePrimePowerCodesCenterBelow (admR n),
            ((ppWeightReal k : ℝ) : ℂ) *
              (primeSpikeDensityPart (N := admN n) (admL n)
                  (s + (SupVConst : ℂ))
                - primeSpikeOscPart (N := admN n) 1 k (admL n)
                    (s + (SupVConst : ℂ))
                + primeSpikeErrPart (N := admN n) 1 k (admL n)
                    (s + (SupVConst : ℂ))))
        + spikeE2Transform (N := admN n) 1
            (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
            (admL n) (s + (SupVConst : ℂ)))
    - seamCore n s

/-- **THE GO/NO-GO PROPOSITION.** For every compact `K ⊆ Ω`, the total
profile error is uniformly bounded over `K` and over all stages `n`. -/
def DBFFM2TotalProfileErrorLocBdd : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Omega →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ s ∈ K, ‖m2TotalProfileError n s‖ ≤ C

#print axioms m2TotalProfileError

end

end RHFormalization
