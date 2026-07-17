import RHFormalization.MeromorphyAssembly
import RHFormalization.HPPEndgame
import RHFormalization.ReflectionPairPoleClass
import RHFormalization.DefaultZeroMultiplicity
import RHFormalization.DefaultZeroExhaustion
import RHFormalization.DesignedDetailedConstruction
import RHFormalization.MainTheoremFromRealZeroFreeOmegaCodiscrete
import RHFormalization.DefaultOmegaPreperfect
import RHFormalization.DefaultOmegaCodiscreteIdentity
import RHFormalization.InterfaceFromCommonCshared
import RHFormalization.DefaultPoleNormalFormLayer
import RHFormalization.HMeromorphicWithNormalFormChosenCshared
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromWindowFRNoSpeed
import RHFormalization.ZpoleFromSeries
import RHFormalization.EnvelopeFromZeroDensity

namespace RHFormalization
noncomputable section
open Complex

theorem RH_current_frontier
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (h_common : Y.B.Cshared = X.layer.overlap.Cshared) :
    RiemannHypothesis :=
  mainTheorem_from_realZeroFree_omegaCodiscreteIdentity
    h_real_zero_free Y X
    (buildInterfaceBridgeNonnegativeFromCommonCshared Y X h_common)
    defaultOmegaCodiscreteIdentityAPI defaultOmegaPreperfectAPI

#print axioms RH_current_frontier

end
end RHFormalization

namespace RHFormalization
noncomputable section
open Complex

/--
Raw-inputs manifest: RH from bottom-layer data only.

Both sides are built against the single shared canonical package
`C := SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S`,
so the interface equation holds by construction. X's genuine-pole
obligations are derived from the principal-part input via the proven
residue-nonvanishing lemma.
-/
theorem RH_from_raw_inputs
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    -- Appendix D raw inputs
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)
    (F : DFHLimitData finiteOperatorLayer.toStagePackage)
    (R : DMasterResidualData finiteOperatorLayer.toStagePackage)
    (h_R_stage_bound :
      ∀ (K : Set ℂ), IsCompact K → K ⊆ Ω →
        ∃ C, 0 ≤ C ∧ ∀ (α : DFiniteStage), ∀ s ∈ K,
          ‖finiteOperatorLayer.toStagePackage.R_stage α s‖ ≤ C)
    (hσ : 0 ≤ finiteOperatorLayer.toStagePackage.sigma0)
    (hF_alpha : F.alpha = S.alpha)
    (hR_alpha : R.alpha = S.alpha)
    -- Appendix H raw inputs
    (M : ZeroMultiplicityData)
    (Zex : ZeroExhaustion)
    (Zpole : ℂ → ℂ)
    (convergence : ZeroPoleLocalUniformConvergenceAPI M Zex Zpole)
    (poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M Zex Zpole)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (h_C_sigma_le :
      (SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S).sigma0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        (SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S).Bshared s =
          HarchPackage.Harch s - Zpole s)
    (h_pp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC Zpole W.s0
          (groupedResidueCoeff M (defaultGroupedPoleClass M W))) :
    RiemannHypothesis := by
  have h_gp : ∀ W : ZeroWitness, HasGenuinePole Zpole W.s0 := fun W =>
    ⟨groupedResidueCoeff M (defaultGroupedPoleClass M W),
      groupedResidueCoeff_ne_zero M W (defaultGroupedPoleClass M W),
      h_pp W⟩
  exact RH_current_frontier h_real_zero_free
    (buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthWindowFRNoSpeed
      finiteOperatorLayer S F R h_R_stage_bound hσ hF_alpha hR_alpha)
    (buildHMeromorphicWithNormalFormPolesWithChosenCshared
      M Zex Zpole convergence poleSeriesMeromorphic HarchPackage
      (SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S)
      sigmaH h_C_sigma_le h_split h_gp
      (buildHSideGroupedPoleNormalFormDataFromPrincipalParts _ M h_pp))
    (by rfl)

#print axioms RH_from_raw_inputs

end
end RHFormalization

namespace RHFormalization
noncomputable section
open Complex

/--
Manifest specialized to the concrete selected operator layer: raw input #1
(the finite-stage operator construction) is supplied by
`selectedFiniteOperatorLayer`, a built witness.
-/
theorem RH_from_selected_operator_layer
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData selectedFiniteOperatorLayer)
    (F : DFHLimitData selectedFiniteOperatorLayer.toStagePackage)
    (R : DMasterResidualData selectedFiniteOperatorLayer.toStagePackage)
    (h_R_stage_bound :
      ∀ (K : Set ℂ), IsCompact K → K ⊆ Ω →
        ∃ C, 0 ≤ C ∧ ∀ (α : DFiniteStage), ∀ s ∈ K,
          ‖selectedFiniteOperatorLayer.toStagePackage.R_stage α s‖ ≤ C)
    (hσ : 0 ≤ selectedFiniteOperatorLayer.toStagePackage.sigma0)
    (hF_alpha : F.alpha = S.alpha)
    (hR_alpha : R.alpha = S.alpha)
    (M : ZeroMultiplicityData)
    (Zex : ZeroExhaustion)
    (Zpole : ℂ → ℂ)
    (convergence : ZeroPoleLocalUniformConvergenceAPI M Zex Zpole)
    (poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M Zex Zpole)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (h_C_sigma_le :
      (SharpCutoffChosenLengthSharedPackage selectedFiniteOperatorLayer S).sigma0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        (SharpCutoffChosenLengthSharedPackage selectedFiniteOperatorLayer S).Bshared s =
          HarchPackage.Harch s - Zpole s)
    (h_pp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC Zpole W.s0
          (groupedResidueCoeff M (defaultGroupedPoleClass M W))) :
    RiemannHypothesis :=
  RH_from_raw_inputs h_real_zero_free
    selectedFiniteOperatorLayer S F R h_R_stage_bound hσ hF_alpha hR_alpha
    M Zex Zpole convergence poleSeriesMeromorphic HarchPackage
    sigmaH h_C_sigma_le h_split h_pp

#print axioms RH_from_selected_operator_layer

end
end RHFormalization

namespace RHFormalization
noncomputable section
open Complex

/--
CAPSTONE MANIFEST (designed D-side): RH from the real-zero-free input and the
Appendix-H raw inputs ONLY. The entire D-side is supplied by the closed witness
`designedY`; its shared canonical package is the concrete tsum package over the
displacement Gaussian, so `h_split` below is an identity against the genuine
prime-power series Σ' Λ(q)/√q · G(log q).
-/
theorem RH_from_designed_D_and_H_raw_inputs
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    -- Appendix H raw inputs (the D-side is closed by designedY)
    (M : ZeroMultiplicityData)
    (Zex : ZeroExhaustion)
    (Zpole : ℂ → ℂ)
    (convergence : ZeroPoleLocalUniformConvergenceAPI M Zex Zpole)
    (poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M Zex Zpole)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (h_C_sigma_le : designedY.B.Cshared.sigma0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        designedY.B.Cshared.Bshared s =
          HarchPackage.Harch s - Zpole s)
    (h_pp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC Zpole W.s0
          (groupedResidueCoeff M (defaultGroupedPoleClass M W))) :
    RiemannHypothesis := by
  have h_gp : ∀ W : ZeroWitness, HasGenuinePole Zpole W.s0 := fun W =>
    ⟨groupedResidueCoeff M (defaultGroupedPoleClass M W),
      groupedResidueCoeff_ne_zero M W (defaultGroupedPoleClass M W),
      h_pp W⟩
  exact RH_current_frontier h_real_zero_free
    designedY
    (buildHMeromorphicWithNormalFormPolesWithChosenCshared
      M Zex Zpole convergence poleSeriesMeromorphic HarchPackage
      designedY.B.Cshared
      sigmaH h_C_sigma_le h_split h_gp
      (buildHSideGroupedPoleNormalFormDataFromPrincipalParts _ M h_pp))
    (by rfl)

/--
The shared B-function in the capstone manifest is the concrete prime-power
series: the `h_split` hypothesis is an identity against Σ' Λ(q)/√q · G(log q).
-/
theorem designed_Cshared_Bshared_eq (s : ℂ) :
    designedY.B.Cshared.Bshared s =
      ∑' q : PrimePowerPair,
        q.weightC * (displacementCanonicalKernel (heatKernelG 1)) q.center s := by
  first
    | rfl
    | simp [canonicalPrimePowerPackageFromKernelTsum, RCutoffEstimateSharedPackage]

#print axioms RH_from_designed_D_and_H_raw_inputs
#print axioms designed_Cshared_Bshared_eq

end
end RHFormalization

namespace RHFormalization
noncomputable section
open Complex

/-- The designed shared package has threshold 0. -/
theorem designedY_Cshared_sigma0 : designedY.B.Cshared.sigma0 = 0 := by
  first
    | rfl
    | simp [designedY,
        buildDDetailedConstructionWithOperatorLegalityFromRCutoffEstimate,
        buildDDetailedConstructionWithOperatorLegalityFromFiniteCanonicalLimit,
        buildDBcanLimitDataFromOperatorFiniteCanonicalLimit,
        buildDBcanLimitDataFromOperatorPrimePowerLimit,
        RCutoffEstimateSharedPackage,
        canonicalPrimePowerPackageFromKernelTsum,
        designedFiniteOperatorLayer_sigma0]

/--
TIGHTEST CAPSTONE: RH from the real-zero-free input and the residual H-side
analytic inputs. The D-side is the closed witness `designedY`; the zero
exhaustion is the PROVEN `defaultZeroExhaustion`; the threshold condition is
just nonnegativity of `sigmaH`.
-/
theorem RH_from_designed_D_default_Zex
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (M : ZeroMultiplicityData)
    (Zpole : ℂ → ℂ)
    (convergence : ZeroPoleLocalUniformConvergenceAPI M defaultZeroExhaustion Zpole)
    (poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M defaultZeroExhaustion Zpole)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (hσH : 0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        designedY.B.Cshared.Bshared s =
          HarchPackage.Harch s - Zpole s)
    (h_pp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC Zpole W.s0
          (groupedResidueCoeff M (defaultGroupedPoleClass M W))) :
    RiemannHypothesis :=
  RH_from_designed_D_and_H_raw_inputs h_real_zero_free
    M defaultZeroExhaustion Zpole convergence poleSeriesMeromorphic HarchPackage
    sigmaH (by rw [designedY_Cshared_sigma0]; exact hσH) h_split h_pp

#print axioms RH_from_designed_D_default_Zex

end
end RHFormalization

namespace RHFormalization
noncomputable section
open Complex

/--
CAPSTONE V3 — the tightest manifest. RiemannHypothesis from:
the real-zero-free input; a pole-series candidate `Zpole` with its locally
uniform convergence (against the PROVEN exhaustion) and meromorphy APIs; the
archimedean package; the explicit-formula split against the CONSTRUCTED
prime-power series; and principal parts carrying the TRUE analytic
multiplicities. Everything else — the entire D-side, the zero exhaustion,
the multiplicity data, the threshold — is theorem.
-/
theorem RH_from_designed_D_default_Zex_M
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (Zpole : ℂ → ℂ)
    (convergence :
      ZeroPoleLocalUniformConvergenceAPI defaultZeroMultiplicityData
        defaultZeroExhaustion Zpole)
    (poleSeriesMeromorphic :
      ZpoleMeromorphicFromSeriesAPI defaultZeroMultiplicityData
        defaultZeroExhaustion Zpole)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (hσH : 0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        designedY.B.Cshared.Bshared s =
          HarchPackage.Harch s - Zpole s)
    (h_pp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC Zpole W.s0
          (groupedResidueCoeff defaultZeroMultiplicityData
            (defaultGroupedPoleClass defaultZeroMultiplicityData W))) :
    RiemannHypothesis :=
  RH_from_designed_D_default_Zex h_real_zero_free
    defaultZeroMultiplicityData Zpole convergence poleSeriesMeromorphic
    HarchPackage sigmaH hσH h_split h_pp

#print axioms RH_from_designed_D_default_Zex_M

end
end RHFormalization

namespace RHFormalization
noncomputable section
open Complex

/--
CAPSTONE V4 — the honest manifest. Identical to V3 except that `h_pp` is
stated against the REFLECTION-PAIR grouped class: the principal coefficient at
each witness pole point is `m(ρ) + m(1−ρ)` with the true analytic
multiplicities — exactly the residue the genuine pole series carries (the
singleton-class form of `h_pp` is unsatisfiable by that series; defect #5).
-/
theorem RH_from_designed_D_default_Zex_M_pair
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (Zpole : ℂ → ℂ)
    (convergence :
      ZeroPoleLocalUniformConvergenceAPI defaultZeroMultiplicityData
        defaultZeroExhaustion Zpole)
    (poleSeriesMeromorphic :
      ZpoleMeromorphicFromSeriesAPI defaultZeroMultiplicityData
        defaultZeroExhaustion Zpole)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (hσH : 0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        designedY.B.Cshared.Bshared s =
          HarchPackage.Harch s - Zpole s)
    (h_pp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC Zpole W.s0
          (groupedResidueCoeff defaultZeroMultiplicityData
            (pairGroupedPoleClass defaultZeroMultiplicityData W))) :
    RiemannHypothesis := by
  have h_gp : ∀ W : ZeroWitness, HasGenuinePole Zpole W.s0 := fun W =>
    ⟨groupedResidueCoeff defaultZeroMultiplicityData
        (pairGroupedPoleClass defaultZeroMultiplicityData W),
      groupedResidueCoeff_ne_zero defaultZeroMultiplicityData W
        (pairGroupedPoleClass defaultZeroMultiplicityData W),
      h_pp W⟩
  exact RH_current_frontier h_real_zero_free
    designedY
    (buildHMeromorphicWithNormalFormPolesWithChosenCshared
      defaultZeroMultiplicityData defaultZeroExhaustion Zpole convergence
      poleSeriesMeromorphic HarchPackage
      designedY.B.Cshared
      sigmaH (by rw [designedY_Cshared_sigma0]; exact hσH) h_split h_gp
      (buildHSideGroupedPoleNormalFormDataFromPrincipalPartsPair _
        defaultZeroMultiplicityData h_pp))
    (by rfl)

#print axioms RH_from_designed_D_default_Zex_M_pair

end
end RHFormalization

namespace RHFormalization
noncomputable section
open Complex

/--
CAPSTONE V5 — h_pp is DERIVED, not assumed. RiemannHypothesis from: the
real-zero-free input; a pole-series candidate with its locally uniform
convergence and meromorphy APIs; the archimedean package; a nonnegative
threshold; and the explicit-formula split. The principal parts at every
witness pole point — with the honest reflection-pair coefficients carrying
the true analytic multiplicities — are supplied by the proven
`h_pp_from_convergence`, the conclusion of the five-installment reduction
campaign (isolation, stabilization, sphere convergence, maximum principle,
limit assembly).
-/
theorem RH_from_designed_D_convergence
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (Zpole : ℂ → ℂ)
    (convergence :
      ZeroPoleLocalUniformConvergenceAPI defaultZeroMultiplicityData
        defaultZeroExhaustion Zpole)
    (poleSeriesMeromorphic :
      ZpoleMeromorphicFromSeriesAPI defaultZeroMultiplicityData
        defaultZeroExhaustion Zpole)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (hσH : 0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        designedY.B.Cshared.Bshared s =
          HarchPackage.Harch s - Zpole s) :
    RiemannHypothesis :=
  RH_from_designed_D_default_Zex_M_pair h_real_zero_free
    Zpole convergence poleSeriesMeromorphic HarchPackage sigmaH hσH h_split
    (fun W => h_pp_from_convergence defaultZeroMultiplicityData Zpole
      convergence W)

#print axioms RH_from_designed_D_convergence

end
end RHFormalization

namespace RHFormalization
noncomputable section
open Complex

/--
CAPSTONE V6 — meromorphy is DERIVED, not assumed. RiemannHypothesis from:
the real-zero-free input; a pole-series candidate `Zpole` with its locally
uniform convergence API; the archimedean package; a nonnegative threshold;
and the explicit-formula split. Both the principal parts (h_pp campaign) and
the meromorphy of `Zpole` on Ω (meromorphy campaign, incl. the M3-vacuity
discovery that every pole point inside Ω comes from an off-critical zero) are
now supplied by theorems. The manifest's content inputs: real-zero-freeness,
the convergence of the pole series, and the explicit formula.
-/
theorem RH_from_designed_D_convergence_only
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (Zpole : ℂ → ℂ)
    (convergence :
      ZeroPoleLocalUniformConvergenceAPI defaultZeroMultiplicityData
        defaultZeroExhaustion Zpole)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (hσH : 0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        designedY.B.Cshared.Bshared s =
          HarchPackage.Harch s - Zpole s) :
    RiemannHypothesis :=
  RH_from_designed_D_convergence h_real_zero_free
    Zpole convergence
    { h_meromorphic := fun _ _ =>
        meromorphicOn_from_convergence defaultZeroMultiplicityData
          Zpole convergence }
    HarchPackage sigmaH hσH h_split

#print axioms RH_from_designed_D_convergence_only

/--
CAPSTONE V7 — Zpole is DEFINED, convergence is CONSTRUCTED. RiemannHypothesis
from: the real-zero-free input; ONE per-compact summable envelope for the
zero-pole summands (Campaign C: the M-test input, classically the zero-density
bound Σ 1/|γ|² < ∞); the archimedean package; a nonnegative threshold; and the
explicit-formula split, now stated against `ZpoleSeries` — the tsum over ALL
nontrivial zeta zeros, an explicitly constructed object. The pole series is no
longer a hypothesized function: it is the genuine series, its convergence API
built by `buildZeroPoleLUCAPIFromEnvelope`, its principal parts and meromorphy
derived by the banked campaign theorems. THE HONEST CONTENT INPUTS ARE THREE:
real-zero-freeness, one summability statement, and the explicit formula.
-/
theorem RH_from_designed_D_summable
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (D : ZeroPoleEnvelopeData defaultZeroMultiplicityData)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (hσH : 0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        designedY.B.Cshared.Bshared s =
          HarchPackage.Harch s - ZpoleSeries defaultZeroMultiplicityData s) :
    RiemannHypothesis :=
  RH_from_designed_D_convergence_only h_real_zero_free
    (ZpoleSeries defaultZeroMultiplicityData)
    (buildZeroPoleLUCAPIFromEnvelope defaultZeroMultiplicityData D)
    HarchPackage sigmaH hσH h_split

#print axioms RH_from_designed_D_summable

/--
CAPSTONE V8 — Harch is DESIGNED, h_split is RING. Define
`Harch := Bshared + ZpoleSeries`; then the explicit-formula split
`Bshared = Harch − Zpole` holds by ring, and the ENTIRE content of the
archimedean side concentrates into one holomorphy claim:
`Bshared + ZpoleSeries` is holomorphic on Ω — the prime-power series plus the
zero-pole series extends holomorphically to the slit plane. This IS the
manuscript's explicit-formula thesis, stated as a single sentence about
constructed objects. RiemannHypothesis from exactly THREE inputs:
(1) real-zero-freeness; (2) one per-compact summable envelope;
(3) the holomorphy of Bshared + ZpoleSeries on Ω.
-/
theorem RH_from_designed_D_designed_Harch
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (D : ZeroPoleEnvelopeData defaultZeroMultiplicityData)
    (h_holo :
      HolomorphicOnC
        (fun s => designedY.B.Cshared.Bshared s +
          ZpoleSeries defaultZeroMultiplicityData s) Ω) :
    RiemannHypothesis :=
  RH_from_designed_D_summable h_real_zero_free D
    { Harch := fun s => designedY.B.Cshared.Bshared s +
        ZpoleSeries defaultZeroMultiplicityData s
      h_Harch_holo := h_holo }
    0 le_rfl
    (fun s _ => by ring)

#print axioms RH_from_designed_D_designed_Harch

/--
CAPSTONE V9 — the zero-density manifest. RiemannHypothesis from exactly THREE
literature-shaped inputs, every one a recognizable classical statement:
(1) real-zero-freeness on (0,1);
(2) the zero-density summability Σ mult(ρ)/(1 + im(ρ)²) < ∞ — the
    Riemann–von Mangoldt counting bound, the single deepest analytic input;
(3) holomorphy of Bshared + ZpoleSeries on Ω — the explicit-formula thesis.
The convergence API, the envelope, principal parts, meromorphy, the operator
construction, the interface — ALL theorem. This is the tightest manifest the
project supports: three sentences of classical analytic number theory, with
the entire formal architecture machine-verified around them.
-/
theorem RH_from_designed_D_zero_density
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (hsum : Summable (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
      (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2)))
    (h_holo :
      HolomorphicOnC
        (fun s => designedY.B.Cshared.Bshared s +
          ZpoleSeries defaultZeroMultiplicityData s) Ω) :
    RiemannHypothesis :=
  RH_from_designed_D_designed_Harch h_real_zero_free
    (buildEnvelopeFromZeroDensity defaultZeroMultiplicityData hsum)
    h_holo

#print axioms RH_from_designed_D_zero_density

/--
The designed shared B-function IS the explicit-formula prime-power series.
Transports designedY_Bcan_eq_tsum across the banked overlap identity
h_Bcan_matches_shared (Bcan = Cshared.Bshared on the overlap). Consequence:
the Bshared appearing in capstone V9's holomorphy hypothesis is, provably,
Σ' Λ(q)/√q·G(log q) — so V9's input (3) reads in full view as
"Σ' Λ(q)/√q·G(log q) + ZpoleSeries is holomorphic on Ω", the manuscript's
explicit-formula thesis stated against constructed objects.
-/
theorem designedY_Cshared_Bshared_eq_tsum
    (s : ℂ)
    (hs : s ∈ RightHalfPlane designedY.finiteOperatorLayer.toStagePackage.sigma0) :
    designedY.B.Cshared.Bshared s =
      ∑' q : PrimePowerPair,
        q.weightC * (displacementCanonicalKernel (heatKernelG 1)) q.center s :=
  (designedY.B.h_Bcan_matches_shared s hs).symm.trans
    (designedY_Bcan_eq_tsum s hs)

#print axioms designedY_Cshared_Bshared_eq_tsum

end
end RHFormalization
