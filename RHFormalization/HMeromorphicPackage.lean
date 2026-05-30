import RHFormalization.HSidePoleWitness
import RHFormalization.CanonicalPrimePowerPackage

/-!
# RHFormalization.HMeromorphicPackage

Iteration 7: Appendix-H zero-side meromorphic package skeleton.

The manuscript's Appendix H must construct independently

  Zpole(s) = Σρ m(ρ)/(s + ρ(1-ρ))

as a meromorphic function on `Ω`, together with a holomorphic archimedean term
`Harch`, and an overlap identity

  Bzero = Harch - Zpole

on a right half-plane.

This file does not yet prove convergence of the zero-pole series. It makes the
Appendix-H proof obligations precise:

* pole set on `Ω`;
* compact avoidance of the pole set;
* zero-counting/summability input;
* local uniform convergence away from poles;
* meromorphicity from local convergence plus principal parts;
* H-side package construction.

This is the zero-side analogue of the Appendix-D export skeleton.
-/


namespace RHFormalization

noncomputable section

open Complex

/-!
## 1. The zero-side pole set
-/

/-- The pole set induced by nontrivial zeta zeros. -/
def ZeroPoleSet : Set ℂ :=
  {s : ℂ | ∃ ρ : ℂ, IsNontrivialZetaZero ρ ∧ s = polePoint ρ}

/-- Membership helper for the pole set. -/
theorem mem_ZeroPoleSet_iff (s : ℂ) :
    s ∈ ZeroPoleSet ↔
      ∃ ρ : ℂ, IsNontrivialZetaZero ρ ∧ s = polePoint ρ := by
  rfl

/--
A compact set avoids the zero-pole set.

We keep compactness as a separate field because the local-uniform convergence
statements in Appendix H are always made on compacta away from poles.
-/
structure CompactAwayFromZeroPoles where
  K : Set ℂ
  h_compact : IsCompact K
  h_subset_Omega : K ⊆ Ω
  h_avoid :
    ∀ s : ℂ, s ∈ K → s ∉ ZeroPoleSet

/-!
## 2. Formal zero-pole summands
-/

/-- Denominator for the zero-pole summand. -/
def zeroPoleDenom (ρ s : ℂ) : ℂ :=
  s + ρ * (1 - ρ)

/-- Zero-pole summand with multiplicity coefficient as a natural number. -/
def zeroPoleSummand
    (M : ZeroMultiplicityData)
    (ρ s : ℂ) : ℂ :=
  (M.mult ρ : ℂ) / zeroPoleDenom ρ s

/--
A finite partial pole series indexed by a finite set of zeros.

This is useful for approximating the H-side infinite series.
-/
def finiteZeroPoleSeries
    (M : ZeroMultiplicityData)
    (S : Finset ℂ)
    (s : ℂ) : ℂ :=
  Finset.sum S (fun ρ => zeroPoleSummand M ρ s)

/-!
## 3. Exhaustion of the zero set
-/

/--
A finite exhaustion of the nontrivial zero set.

This is an abstract replacement for an ordering/truncation of zeros by height.
The field `h_eventually_contains` records that every nontrivial zero enters
the exhaustion at some stage.
-/
structure ZeroExhaustion where
  zeroSet : ℕ → Finset ℂ
  h_all_zeros :
    ∀ n ρ, ρ ∈ zeroSet n → IsNontrivialZetaZero ρ
  h_eventually_contains :
    ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ∃ n, ρ ∈ zeroSet n

/-- Partial H-side pole series along a zero exhaustion. -/
def zeroPolePartial
    (M : ZeroMultiplicityData)
    (E : ZeroExhaustion)
    (n : ℕ)
    (s : ℂ) : ℂ :=
  finiteZeroPoleSeries M (E.zeroSet n) s

/-!
## 4. Zero-counting and summability inputs
-/

/--
Dyadic zero-counting / denominator summability input.

Analytically, this packages the standard argument:
away from the pole set, denominators grow quadratically in zero height while
the number of zeros in dyadic shells grows like `O(T log T)`.
-/
structure ZeroPoleSummabilityAPI
    (M : ZeroMultiplicityData)
    (E : ZeroExhaustion) where
  h_compact_uniform_summable :
    ∀ K : CompactAwayFromZeroPoles,
      True

/--
Appendix-H local convergence theorem, as an explicit API.

It says that the partial zero-pole series converges locally uniformly to the
candidate `Zpole` on every compact set away from the pole set.
-/
structure ZeroPoleLocalUniformConvergenceAPI
    (M : ZeroMultiplicityData)
    (E : ZeroExhaustion)
    (Zpole : ℂ → ℂ) where
  h_luc :
    ∀ K : CompactAwayFromZeroPoles,
      LocallyUniformConvergesOnC
        (fun n s => zeroPolePartial M E n s)
        Zpole
        K.K

/-!
## 5. Meromorphicity from local convergence plus principal parts
-/

/--
From local uniform convergence away from poles and local principal-part ownership at
the pole set, obtain meromorphicity of `Zpole` on `Ω`.

This is the H-side meromorphic package theorem in its clean formal-interface form.
-/
structure ZpoleMeromorphicFromSeriesAPI
    (M : ZeroMultiplicityData)
    (E : ZeroExhaustion)
    (Zpole : ℂ → ℂ) where
  h_meromorphic :
    ZeroPoleLocalUniformConvergenceAPI M E Zpole →
    (∀ W : ZeroWitness, HasGenuinePole Zpole W.s0) →
    MeromorphicOnC Zpole Ω

/-!
## 6. Archimedean and overlap package
-/

/--
Archimedean term package from Appendix H.

`Harch` is holomorphic on `Ω`.
-/
structure HArchPackage where
  Harch : ℂ → ℂ
  h_Harch_holo : HolomorphicOnC Harch Ω

/--
H-side overlap package identity.

On a right half-plane, the canonical package representative is
`Bzero = Harch - Zpole`.
-/
structure HSideOverlapPackage
    (Zpole : ℂ → ℂ)
    (Harch : ℂ → ℂ) where
  Bzero : ℂ → ℂ
  sigma0 : ℝ

  /--
  The shared canonical prime-power package which this H-side package represents
  on its overlap half-plane.
  -/
  Cshared : CanonicalPrimePowerPackage

  /--
  The H-side overlap half-plane is at least as far right as the intrinsic
  convergence half-plane of the shared package.
  -/
  h_Cshared_sigma_le :
    Cshared.sigma0 ≤ sigma0

  /--
  Appendix-H package identity against the shared canonical package on the
  overlap half-plane.
  -/
  h_Bzero_matches_shared :
    ∀ s : ℂ, s ∈ RightHalfPlane sigma0 →
      Bzero s = Cshared.Bshared s

  h_split :
    ∀ s : ℂ, s ∈ RightHalfPlane sigma0 →
      Bzero s = Harch s - Zpole s

/-!
## 7. Full Appendix-H package skeleton
-/
/--
Clean final Appendix-H package data, avoiding the dummy-index issue.

This is the preferred object for Iteration 7.
-/
structure HMeromorphicPackageLayerV2 where
  M : ZeroMultiplicityData
  E : ZeroExhaustion
  Zpole : ℂ → ℂ
  convergence : ZeroPoleLocalUniformConvergenceAPI M E Zpole
  poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M E Zpole
  HarchPackage : HArchPackage
  overlap : HSideOverlapPackage Zpole HarchPackage.Harch
  h_genuine_poles :
    ∀ W : ZeroWitness, HasGenuinePole Zpole W.s0

/--
Build the manuscript's `ZeroPolePackageAPI` from the explicit Appendix-H
meromorphic package layer.
-/
def buildZeroPolePackageFromHMeromorphicLayer
    (L : HMeromorphicPackageLayerV2) :
    ZeroPolePackageAPI :=
  { Zpole := L.Zpole
    Harch := L.HarchPackage.Harch
    Bzero := L.overlap.Bzero
    sigma0 := L.overlap.sigma0
    hZ_meromorphic :=
      L.poleSeriesMeromorphic.h_meromorphic
        L.convergence
        L.h_genuine_poles
    hHarch_holo := L.HarchPackage.h_Harch_holo
    h_split := L.overlap.h_split }

/--
Attach grouped pole data after the final H package has been built.

This is the preferred way to combine Iteration 6 and Iteration 7.
-/
structure HMeromorphicWithGroupedPoles where
  layer : HMeromorphicPackageLayerV2
  groupedLayer :
    HSidePoleWitnessLayer (buildZeroPolePackageFromHMeromorphicLayer layer)

/-- Extract the finished zero-side package. -/
def HMeromorphicWithGroupedPoles.toZeroPolePackageAPI
    (X : HMeromorphicWithGroupedPoles) :
    ZeroPolePackageAPI :=
  buildZeroPolePackageFromHMeromorphicLayer X.layer

/-- Extract the finished H-side pole witness layer. -/
def HMeromorphicWithGroupedPoles.toHSidePoleWitnessLayer
    (X : HMeromorphicWithGroupedPoles) :
    HSidePoleWitnessLayer X.toZeroPolePackageAPI :=
  X.groupedLayer

end

end RHFormalization
