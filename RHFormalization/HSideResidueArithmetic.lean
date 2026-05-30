import RHFormalization.HMeromorphicPackage

/-!
# RHFormalization.HSideResidueArithmetic

Iteration 14: H-side grouped-residue arithmetic.

Appendix H/F uses a simple but important arithmetic fact:

If several zeta zeros produce the same pole location, their multiplicities are
positive natural numbers and hence their grouped residue coefficient cannot
cancel to zero.

Earlier iterations represented this with two APIs:

* `GroupedMultiplicityPositiveAPI`
* `GroupedResidueNonzeroAPI`

This file reduces those APIs to theorem builders from the data already present in
`GroupedPoleClass` and `ZeroMultiplicityData`.

The remaining H-side analytic burden is not this arithmetic step.  The hard part
is still the principal-part ownership of the actual meromorphic zero-pole series.
-/


namespace RHFormalization

noncomputable section

open Complex

/-!
## 1. Positivity of the grouped multiplicity sum
-/

/--
The grouped multiplicity sum is positive because the witness zero belongs to the
finite grouped class and has positive multiplicity.
-/
theorem groupedMultiplicitySum_pos
    (M : ZeroMultiplicityData)
    (W : ZeroWitness)
    (C : GroupedPoleClass M W) :
    0 < groupedMultiplicitySum M C := by
  have h_witness_pos : 0 < M.mult W.ρ :=
    M.h_mult_pos W.ρ W.h_zero
  have h_witness_le_sum :
      M.mult W.ρ ≤ groupedMultiplicitySum M C := by
    unfold groupedMultiplicitySum
    exact Finset.single_le_sum
      (fun ρ _hρ => Nat.zero_le (M.mult ρ))
      C.h_witness_mem
  exact lt_of_lt_of_le h_witness_pos h_witness_le_sum

/--
Build `GroupedMultiplicityPositiveAPI` from the grouped-class data.
-/
def buildGroupedMultiplicityPositiveAPI
    (M : ZeroMultiplicityData) :
    GroupedMultiplicityPositiveAPI M :=
  { h_grouped_sum_pos := fun W C =>
      groupedMultiplicitySum_pos M W C }

/-!
## 2. Nonzero complex grouped residue coefficient
-/

/--
A positive natural number coerces to a nonzero complex number.

This is a small arithmetic bridge between the natural-number multiplicity sum and
the complex principal coefficient.
-/
theorem complex_natCast_ne_zero_of_pos
    {n : ℕ}
    (hn : 0 < n) :
    (n : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt hn)

/--
The grouped residue coefficient is nonzero.
-/
theorem groupedResidueCoeff_ne_zero
    (M : ZeroMultiplicityData)
    (W : ZeroWitness)
    (C : GroupedPoleClass M W) :
    groupedResidueCoeff M C ≠ 0 := by
  unfold groupedResidueCoeff
  exact complex_natCast_ne_zero_of_pos
    (groupedMultiplicitySum_pos M W C)

/--
Build `GroupedResidueNonzeroAPI` from the positive grouped multiplicity theorem.
-/
def buildGroupedResidueNonzeroAPI
    (M : ZeroMultiplicityData)
    (P : GroupedMultiplicityPositiveAPI M) :
    GroupedResidueNonzeroAPI M P :=
  { h_groupedResidue_ne_zero := fun W C =>
      -- We can use `P`, but the direct theorem is stronger and avoids any
      -- dependence on the representation of `P`.
      groupedResidueCoeff_ne_zero M W C }

/-!
## 3. H-side grouped pole data from arithmetic fields
-/

/--
H-side grouped-pole data with arithmetic positivity derived automatically.

The remaining load-bearing analytic field is `h_principalPart`, which says the
actual H-side meromorphic package has the stated grouped principal part.
-/
structure HSideGroupedPoleArithmeticData
    (H : ZeroPolePackageAPI) where
  M : ZeroMultiplicityData
  groupedClass :
    ∀ W : ZeroWitness, GroupedPoleClass M W
  h_principalPart :
    ∀ W : ZeroWitness,
      HasPrincipalPartAtC H.Zpole W.s0
        (groupedResidueCoeff M (groupedClass W))
  principalPartToPole :
    PrincipalPartImpliesGenuinePoleAPI

/--
Convert arithmetic grouped-pole data into the previous `HSideGroupedPoleData`.
-/
def HSideGroupedPoleArithmeticData.toGroupedPoleData
    {H : ZeroPolePackageAPI}
    (A : HSideGroupedPoleArithmeticData H) :
    HSideGroupedPoleData H :=
  let Pos := buildGroupedMultiplicityPositiveAPI A.M
  { M := A.M
    Pos := Pos
    Nonzero := buildGroupedResidueNonzeroAPI A.M Pos
    groupedClass := A.groupedClass
    h_principalPart := A.h_principalPart }

/--
Convert arithmetic grouped-pole data into the previous `HSidePoleWitnessLayer`.
-/
def HSideGroupedPoleArithmeticData.toHSidePoleWitnessLayer
    {H : ZeroPolePackageAPI}
    (A : HSideGroupedPoleArithmeticData H) :
    HSidePoleWitnessLayer H :=
  { groupedData := A.toGroupedPoleData
    principalPartToPole := A.principalPartToPole }

/-!
## 4. H meromorphic package with arithmetic grouped poles
-/

/--
H-side meromorphic package plus arithmetic grouped-pole data.

Compared with `HMeromorphicWithGroupedPoles`, this object does not ask the user
to provide the grouped residue positivity/nonzero APIs. Those are built here.
-/
structure HMeromorphicWithArithmeticGroupedPoles where
  layer : HMeromorphicPackageLayerV2
  arithmeticGroupedLayer :
    HSideGroupedPoleArithmeticData
      (buildZeroPolePackageFromHMeromorphicLayer layer)

/-- Extract the finished zero-side package. -/
def HMeromorphicWithArithmeticGroupedPoles.toZeroPolePackageAPI
    (X : HMeromorphicWithArithmeticGroupedPoles) :
    ZeroPolePackageAPI :=
  buildZeroPolePackageFromHMeromorphicLayer X.layer

/-- Extract the H-side pole witness layer. -/
def HMeromorphicWithArithmeticGroupedPoles.toHSidePoleWitnessLayer
    (X : HMeromorphicWithArithmeticGroupedPoles) :
    HSidePoleWitnessLayer X.toZeroPolePackageAPI :=
  X.arithmeticGroupedLayer.toHSidePoleWitnessLayer

/--
Convert to the older packaged H-side object.
-/
def HMeromorphicWithArithmeticGroupedPoles.toHMeromorphicWithGroupedPoles
    (X : HMeromorphicWithArithmeticGroupedPoles) :
    HMeromorphicWithGroupedPoles :=
  { layer := X.layer
    groupedLayer := X.toHSidePoleWitnessLayer }

end

end RHFormalization
