import RHFormalization.AppendixHZeroDensityInterfaceEndpoint

/-!
# RHFormalization.AppendixHHoloClosure

This file reconciles the new Appendix-H interface endpoint with the older V9
`h_holo` frontier.

The new Appendix-H endpoint says RH follows from:

  h_real_zero_free
  + hsum
  + Hpkg : HArchPackage
  + Bshared = Harch - ZpoleSeries on a half-plane.

The old V9 frontier says RH follows from:

  h_real_zero_free
  + hsum
  + HolomorphicOnC (Bshared + ZpoleSeries) Ω.

This file proves the bridge between the two by choosing

  Harch(s) := Bshared(s) + ZpoleSeries(s).

So the remaining Appendix-H payload is exactly the holomorphy of
`Bshared + ZpoleSeries`, not a principal-part theorem for the raw displacement
kernel.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

/--
The Appendix-H package obtained from the V9 holomorphy frontier.
-/
def appendixHDesignedPackageFromHolo
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ =>
          designedY.B.Cshared.Bshared s
            + ZpoleSeries defaultZeroMultiplicityData s)
        Ω) :
    HArchPackage :=
  { Harch :=
      fun s : ℂ =>
        designedY.B.Cshared.Bshared s
          + ZpoleSeries defaultZeroMultiplicityData s
    h_Harch_holo := h_holo }

/--
With `Harch := Bshared + ZpoleSeries`, the Appendix-H overlap split is tautological.
-/
theorem appendixHDesignedOverlapFromHolo
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ =>
          designedY.B.Cshared.Bshared s
            + ZpoleSeries defaultZeroMultiplicityData s)
        Ω) :
    ∀ s : ℂ,
      s ∈ RightHalfPlane (0 : ℝ) →
        designedY.B.Cshared.Bshared s =
          (appendixHDesignedPackageFromHolo h_holo).Harch s
            - ZpoleSeries defaultZeroMultiplicityData s := by
  intro s hs
  simp [appendixHDesignedPackageFromHolo]

/--
Appendix-H interface closure reduced exactly to the old V9 `h_holo` frontier.

Remaining payload:
* real-zero-freeness;
* zero-density summability;
* holomorphy of `Bshared + ZpoleSeries` on Ω.
-/
theorem RH_from_appendixH_interface_zeroDensity_holo
    (h_real_zero_free :
      ∀ s : ℂ,
        s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
          (defaultZeroMultiplicityData.mult ρ.1 : ℝ) /
            (1 + ρ.1.im ^ 2)))
    (h_holo :
      HolomorphicOnC
        (fun s : ℂ =>
          designedY.B.Cshared.Bshared s
            + ZpoleSeries defaultZeroMultiplicityData s)
        Ω) :
    RiemannHypothesis :=
  RH_from_appendixH_interface_zeroDensity
    h_real_zero_free
    hsum
    (appendixHDesignedPackageFromHolo h_holo)
    0
    (le_refl (0 : ℝ))
    (appendixHDesignedOverlapFromHolo h_holo)

#check appendixHDesignedPackageFromHolo
#check appendixHDesignedOverlapFromHolo
#check RH_from_appendixH_interface_zeroDensity_holo
#print axioms RH_from_appendixH_interface_zeroDensity_holo

end

end RHFormalization
