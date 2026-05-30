import RHFormalization.RigidityBridge
import RHFormalization.PoleObstruction

/-!
# RHFormalization.HSidePoleWitness

Iteration 6: H-side grouped pole witness layer.

The manuscript's Appendix-H/F pole input is not merely:

  "there is a pole."

It is more specific:

* each nontrivial zero `ρ` contributes a pole at `s = -ρ(1-ρ)`;
* if several zeros induce the same pole point, they are grouped;
* the grouped principal coefficient is a positive sum of multiplicities;
* hence the principal coefficient is nonzero and cannot cancel.

This file makes that bookkeeping explicit at the Lean companion level.

It does not yet construct the full `Zpole` series or prove meromorphic convergence.
That remains part of the Appendix-H zero package. This layer only refines the
pole-witness / grouped-residue output consumed by Appendix F.
-/


namespace RHFormalization

noncomputable section

open Complex

/-!
## 1. Multiplicity data for nontrivial zeros
-/

/--
Multiplicity data for nontrivial zeta zeros.

The positivity field records that every zero counted by the package has strictly
positive multiplicity.
-/
structure ZeroMultiplicityData where
  mult : ℂ → ℕ
  h_mult_pos :
    ∀ ρ : ℂ, IsNontrivialZetaZero ρ → 0 < mult ρ

/-!
## 2. Grouped pole classes
-/

/--
A finite group of zeros that induce the same pole point as a witness `W`.

This is the Lean-facing form of the manuscript's grouped-pole convention:
if multiple zeros have the same value of `ρ(1-ρ)`, their multiplicities are
added at the shared pole location.
-/
structure GroupedPoleClass
    (M : ZeroMultiplicityData)
    (W : ZeroWitness) where
  zeros : Finset ℂ

  h_witness_mem :
    W.ρ ∈ zeros

  h_all_zeros :
    ∀ ρ : ℂ, ρ ∈ zeros → IsNontrivialZetaZero ρ

  h_same_pole :
    ∀ ρ : ℂ, ρ ∈ zeros → polePoint ρ = W.s0

/-- The grouped multiplicity sum at a witness pole point. -/
def groupedMultiplicitySum
    (M : ZeroMultiplicityData)
    {W : ZeroWitness}
    (C : GroupedPoleClass M W) : ℕ :=
  Finset.sum C.zeros (fun ρ => M.mult ρ)

/--
The grouped multiplicity sum is positive because the witness zero belongs to
the group and has positive multiplicity.

This is the precise formal version of "positive multiplicities cannot cancel."
-/
structure GroupedMultiplicityPositiveAPI
    (M : ZeroMultiplicityData) where
  h_grouped_sum_pos :
    ∀ W : ZeroWitness,
    ∀ C : GroupedPoleClass M W,
      0 < groupedMultiplicitySum M C

/--
Cast a grouped multiplicity sum into `ℂ`.

This is the principal coefficient expected for the simple-pole principal part.
-/
def groupedResidueCoeff
    (M : ZeroMultiplicityData)
    {W : ZeroWitness}
    (C : GroupedPoleClass M W) : ℂ :=
  (groupedMultiplicitySum M C : ℂ)

/--
Nonzero grouped residue coefficient.

The arithmetic reason is positivity of the natural-number multiplicity sum.
We keep the exact `Nat.cast` proof as an API because its final Lean form depends
on the chosen `norm_num`/`exact_mod_cast` path.
-/
structure GroupedResidueNonzeroAPI
    (M : ZeroMultiplicityData)
    (P : GroupedMultiplicityPositiveAPI M) where
  h_groupedResidue_ne_zero :
    ∀ W : ZeroWitness,
    ∀ C : GroupedPoleClass M W,
      groupedResidueCoeff M C ≠ 0

/-!
## 3. H-side ownership of grouped principal parts
-/

/--
H-side grouped pole data for `Zpole`.

For every off-critical zero witness, Appendix H supplies:
* the finite grouped pole class at the same pole location;
* the principal part with coefficient equal to the grouped multiplicity sum.
-/
structure HSideGroupedPoleData
    (H : ZeroPolePackageAPI) where
  M : ZeroMultiplicityData
  Pos : GroupedMultiplicityPositiveAPI M
  Nonzero : GroupedResidueNonzeroAPI M Pos

  groupedClass :
    ∀ W : ZeroWitness, GroupedPoleClass M W

  h_principalPart :
    ∀ W : ZeroWitness,
      HasPrincipalPartAtC H.Zpole W.s0
        (groupedResidueCoeff M (groupedClass W))

/--
Converting a nonzero principal part into a genuine pole.

This is a local complex-analysis theorem to be discharged later from the chosen
definition of `HasGenuinePole`.
-/
structure PrincipalPartImpliesGenuinePoleAPI where
  h_genuine :
    ∀ (f : ℂ → ℂ) (s0 c : ℂ),
      c ≠ 0 →
      HasPrincipalPartAtC f s0 c →
      HasGenuinePole f s0

/--
Build the existing `PoleWitnessAPI` from H-side grouped pole data.

This replaces the earlier primitive field:
`∀ W, HasGenuinePole H.Zpole W.s0`.
-/
def buildPoleWitnessFromHSideGrouped
    (H : ZeroPolePackageAPI)
    (G : HSideGroupedPoleData H)
    (Q : PrincipalPartImpliesGenuinePoleAPI) :
    PoleWitnessAPI H :=
  { h_genuine_pole := fun W =>
      Q.h_genuine H.Zpole W.s0
        (groupedResidueCoeff G.M (G.groupedClass W))
        (G.Nonzero.h_groupedResidue_ne_zero W (G.groupedClass W))
        (G.h_principalPart W) }

/--
Build the normal-form API used by the pole-obstruction layer.

This states that every H-side witness pole has a concrete principal coefficient,
namely the grouped multiplicity sum.
-/
def buildGenuinePoleNormalFormFromHSideGrouped
    (H : ZeroPolePackageAPI)
    (G : HSideGroupedPoleData H) :
    GenuinePoleNormalFormAPI H :=
  { h_normal_form := fun W _hPole =>
      { principalCoeff := groupedResidueCoeff G.M (G.groupedClass W)
        h_principalCoeff_ne_zero :=
          G.Nonzero.h_groupedResidue_ne_zero W (G.groupedClass W)
        h_principalPart := G.h_principalPart W } }

/-!
## 4. Preferred Iteration-6 endpoint builder
-/

/--
The H-side grouped-pole layer supplies both:
* the pole witness consumed by the final contradiction;
* the normal-form package consumed by future local pole-obstruction discharge.
-/
structure HSidePoleWitnessLayer
    (H : ZeroPolePackageAPI) where
  groupedData : HSideGroupedPoleData H
  principalPartToPole : PrincipalPartImpliesGenuinePoleAPI

/-- Extract the old pole witness API from the new grouped H-side layer. -/
def HSidePoleWitnessLayer.toPoleWitnessAPI
    {H : ZeroPolePackageAPI}
    (L : HSidePoleWitnessLayer H) :
    PoleWitnessAPI H :=
  buildPoleWitnessFromHSideGrouped H L.groupedData L.principalPartToPole

/-- Extract the normal-form API from the new grouped H-side layer. -/
def HSidePoleWitnessLayer.toNormalFormAPI
    {H : ZeroPolePackageAPI}
    (L : HSidePoleWitnessLayer H) :
    GenuinePoleNormalFormAPI H :=
  buildGenuinePoleNormalFormFromHSideGrouped H L.groupedData

end

end RHFormalization
