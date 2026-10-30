import RHFormalization.QuasiRHDetector
import RHFormalization.DecodedFlatTerminus
import Mathlib

/-!
# QuasiRHFlatTerminus — QR-5: the quasi-RH flat terminus

The θ-analogue of `RH_from_holomorphic_remainder`: the same split identity
`FHadmFree = Bcan + RHcand` on `Re s > 1`, but the remainder is only required to be
holomorphic on `Ω_θ`. Conclusion: `QuasiRH θ` — every nontrivial zero lies within θ of
the critical line. At θ = 0 this is RH (`quasiRH_zero_iff`). Uses the banked H-side package
(`unconditionalX_from_overlap shiftedLaplaceOverlap`) and its genuine-pole data, fed into
the QR-4 detector.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- The banked H-side package used by the flat terminus. -/
abbrev flatX : HMeromorphicWithNormalFormPoles :=
  unconditionalX_from_overlap shiftedLaplaceOverlap

abbrev flatH : ZeroPolePackageAPI := flatX.toLegacyZeroPolePackageAPI

/-- The zero package has a genuine pole (negative order) at every off-line zero's pole. -/
theorem flatH_pole_order_neg {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ)
    (h_off : ρ.re ≠ (1/2:ℝ)) :
    meromorphicOrderAt flatH.Zpole (polePoint ρ) < 0 := by
  let W : ZeroWitness := mkZeroWitness provenZetaZeroFacts ρ hρ h_off
  have h_genuine : HasGenuinePole flatH.Zpole W.s0 := by
    change HasGenuinePole flatX.toLegacyZeroPolePackageAPI.Zpole W.s0
    exact
      ((flatX.toArithmeticGroupedPoles.toHMeromorphicWithGroupedPoles.toHSidePoleWitnessLayer).toPoleWitnessAPI).h_genuine_pole W
  let G : GenuinePoleNormalForm flatH.Zpole W.s0 :=
    (flatX.toLegacyGenuinePoleNormalFormAPI).h_normal_form W h_genuine
  have h_principal : PrincipalPartNormalForm flatH.Zpole W.s0 G.principalCoeff :=
    principalPartNormalFormOfGenuine flatX.toPoleNormalFormLayer G
  exact defaultPrincipalPartNegativeOrderAPI.h_negative_order
    flatH.Zpole W.s0 G.principalCoeff h_principal

/-- **QR-5 — the quasi-RH flat terminus.** A remainder holomorphic on `Ω_θ` that completes
the split identity on `Re s > 1` forces every nontrivial zero into `|Re ρ − ½| ≤ θ`. -/
theorem quasiRH_from_holomorphic_remainder (θ : ℝ) (hθ : 0 ≤ θ)
    (RHcand : ℂ → ℂ)
    (h_holo : HolomorphicOnC RHcand (OmegaTheta θ))
    (h_split : ∀ s ∈ RightHalfPlane (1 : ℝ),
      FHadmFree s = galerkinBcanLimitData.Bcan s + RHcand s) :
    QuasiRH θ := by
  have hsub := OmegaTheta_subset_Omega θ
  refine quasiRH_of_detector provenZetaZeroFacts (σ := 1) hθ FHadmFree
    (fun s => RHcand s + flatH.Harch s) flatH.Zpole
    (FHadmFree_holo.mono hsub) ?_ ?_ ?_ ?_
  · first
      | exact h_holo.add (flatH.hHarch_holo.mono hsub)
      | exact AnalyticOn.add h_holo (flatH.hHarch_holo.mono hsub)
      | exact fun z hz => (h_holo z hz).add (flatH.hHarch_holo z (hsub hz))
  · first
      | exact flatH.hZ_meromorphic.mono_set hsub
      | exact fun z hz => flatH.hZ_meromorphic z (hsub hz)
  · intro s hs
    beta_reduce
    have hB : galerkinBcanLimitData.Bcan s = flatH.Bzero s := by
      have h1 : galerkinBcanLimitData.Bcan s = (shiftedLaplacePrimePackageAt 1).Bshared s := by
        first
          | rfl
          | simp [galerkinBcanLimitData]
      rw [h1]
      exact (shiftedLaplaceOverlap.h_Bzero_matches_shared s hs).symm
    have hH : flatH.Bzero s = flatH.Harch s - flatH.Zpole s := by
      first
        | exact flatH.h_split s hs
        | exact flatH.h_split s (by simpa using hs)
    rw [h_split s hs, hB, hH]
    ring
  · intro ρ hρ hcon
    have h_off : ρ.re ≠ (1/2:ℝ) := by
      intro h
      rw [h, sub_self, abs_zero] at hcon
      linarith
    exact flatH_pole_order_neg hρ h_off

#print axioms flatH_pole_order_neg
#print axioms quasiRH_from_holomorphic_remainder

end

end RHFormalization
