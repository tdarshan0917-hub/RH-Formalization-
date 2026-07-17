import RHFormalization.DBFFAdmissibleProfileProvider
import RHFormalization.AdmissiblePrimeFirstOrderSplit
import RHFormalization.AdmissibleFirstOrderVanish
import RHFormalization.AdmissibleResidualUniform

/-!
# DBFFAdmissibleVanishingError

ROUTE CARD

This file isolates the already-banked vanishing part of the admissible residual.

It proves:

  R_stage_n
    = (free_stage_n - B_stage_n)
      + (FirstOrderWindow_n + SecondResolventResidual_n),

and proves the second parenthesis tends uniformly to zero on Ω-compacts.

This does NOT instantiate the DBFF profile catalog.
This does NOT manufacture profiles.
This does NOT use a fake one-profile shortcut.
This does NOT use raw B on Ω.

After this file, the remaining D.BFF burden is the genuine finite-profile
expansion for the nonvanishing core

  admissibleFreeStage n s - galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s

plus any canonical D.BFF profile error.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology

/-- The vanishing admissible DBFF error: first-order window plus second-resolvent residual. -/
def admissibleDBFFVanishingError (n : ℕ) (s : ℂ) : ℂ :=
  FirstOrderWindow n s + SecondResolventResidual n s

/--
Exact decomposition of the actual admissible `R_stage` into the nonvanishing
free-minus-B core plus the already-banked vanishing FOW/residual error.
-/
theorem admissible_R_stage_eq_core_plus_vanishing
    (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s =
      (admissibleFreeStage n s
        - galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s)
      + admissibleDBFFVanishingError n s := by
  have hR :
      galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s =
        galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
          - galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s := by
    rfl
  rw [hR, package_F_stage_eq_free_add_prime n s,
    FadmPrimeStage_eq_first_plus_second n hs]
  unfold admissibleDBFFVanishingError
  ring

/--
The vanishing admissible DBFF error tends to zero uniformly on Ω-compacts,
in the same eps-N style as the underlying FOW/residual bricks.
-/
theorem admissibleDBFFVanishingError_epsN
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ s ∈ K,
      ‖admissibleDBFFVanishingError n s‖ ≤ ε := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  obtain ⟨N₁, hFOW⟩ := FirstOrderWindow_epsN K hK hKO (ε / 2) hε2
  obtain ⟨N₂, hRES⟩ := SecondResolventResidual_epsN K hK hKO (ε / 2) hε2
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn s hs
  have hn₁ : N₁ ≤ n := le_trans (Nat.le_max_left N₁ N₂) hn
  have hn₂ : N₂ ≤ n := le_trans (Nat.le_max_right N₁ N₂) hn
  have h1 : ‖FirstOrderWindow n s‖ ≤ ε / 2 := hFOW n hn₁ s hs
  have h2 : ‖SecondResolventResidual n s‖ ≤ ε / 2 := hRES n hn₂ s hs
  unfold admissibleDBFFVanishingError
  calc
    ‖FirstOrderWindow n s + SecondResolventResidual n s‖
        ≤ ‖FirstOrderWindow n s‖ + ‖SecondResolventResidual n s‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := by ring

/-- Filter-form version of `admissibleDBFFVanishingError_epsN`. -/
theorem admissibleDBFFVanishingError_eventually_eps0
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∀ s ∈ K,
        ‖admissibleDBFFVanishingError n s‖ ≤ ε := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := admissibleDBFFVanishingError_epsN K hK hKO ε hε
  exact Filter.eventually_atTop.2 ⟨N₀, hN₀⟩

#print axioms admissibleDBFFVanishingError
#print axioms admissible_R_stage_eq_core_plus_vanishing
#print axioms admissibleDBFFVanishingError_epsN
#print axioms admissibleDBFFVanishingError_eventually_eps0

end

end RHFormalization
