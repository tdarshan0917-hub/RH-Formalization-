import RHFormalization.AppendixDSpikeSumExtraction

/-!
# Finite Nat-to-prime-power bridge

This file proves the finite reindexing lemma needed at the current D-side gate.

The selected finite trace/spike payload has a Nat-indexed diagonal/canonical
finite package, while the canonical prime-power package is indexed by
`PrimePowerPair`.  This theorem packages the finite image/reindexing step.
-/

namespace RHFormalization

noncomputable section

open scoped BigOperators

/--
Finite image bridge from a Nat-indexed spike package to the canonical
prime-power finite package.

This is the generic lemma needed to fill the `h_canonical_sum_eq_finiteCanonical`
field of `SelectedFiniteTraceSpikePayload`, once the actual finite extraction
provides:

* a finite Nat index set `I`;
* an injection `toPP` from those Nat indices to `PrimePowerPair`;
* coefficient compatibility;
* kernel compatibility.
-/
theorem finiteNatSpikePackage_eq_finiteCanonicalPrimePowerPackage_image
    (I : Finset ℕ)
    (toPP : ℕ → PrimePowerPair)
    (coeff : ℕ → ℂ)
    (Knat : ℕ → ℂ → ℂ)
    (Kcan : CanonicalKernelC)
    (hinj :
      ∀ m ∈ I, ∀ n ∈ I,
        toPP m = toPP n → m = n)
    (hcoeff :
      ∀ n ∈ I,
        coeff n = (toPP n).weightC)
    (hkernel :
      ∀ n ∈ I, ∀ s : ℂ,
        Knat n s = Kcan (toPP n).center s)
    (s : ℂ) :
    finiteNatSpikePackage I coeff Knat s =
      finiteCanonicalPrimePowerPackage (I.image toPP) Kcan s := by
  dsimp [finiteNatSpikePackage, finiteCanonicalPrimePowerPackage]
  rw [Finset.sum_image]
  · exact
      Finset.sum_congr rfl
        (fun n hn => by
          rw [hcoeff n hn, hkernel n hn s])
  · intro m hm n hn hmn
    exact hinj m hm n hn hmn

end

end RHFormalization
