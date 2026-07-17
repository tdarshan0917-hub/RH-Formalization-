-- SENTINEL: native-montel-adapter-v1
import RHFormalization.ArithmeticPrimeNativeFrontier
import RHFormalization.DCanRemFromMontel
import RHFormalization.MontelSubsequenceAssembly
import RHFormalization.AscoliLocBddBridge
import RHFormalization.AscoliBridgeLayer3
import Mathlib

/-!
# ArithmeticPrimeMontelAdapter — h_conv from loc-bdd + overlap (GPT step)
Converts the native frontier's h_conv into: R_H holo + along-net loc-bdd +
overlap seed, via banked ascoliExtraction_of_loc_bdd +
holomorphicMontelConvergence_from_ascoli. Proves no estimates; reduces
the frontier from full convergence to D.MR.2-shaped boundedness.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-- **h_conv from Montel inputs at the native package.** -/
theorem arithmeticPrimeNative_hconv_from_montel
    (Nfun : ℕ → ℕ) (μ : ∀ n, Fin (Nfun n) → ℝ) (M : ℝ)
    (hnn : ∀ n : ℕ, ∀ y : EuclideanSpace ℂ (Fin (Nfun n)),
      0 ≤ RCLike.re (inner ℂ y
        (primeOpCLM (μ n) (primeStageWeights (N := Nfun n) n) M y)))
    (R_H : ℂ → ℂ)
    (hRH_holo : HolomorphicOnC R_H Ω)
    (h_stage_holo : ∀ n : ℕ,
      HolomorphicOnC (fun s => arithmeticPrimeNativePackage.R_stage
        (arithmeticPrimeNet Nfun μ M hnn n) s) Ω)
    (h_loc_bdd :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K,
          ‖arithmeticPrimeNativePackage.R_stage
            (arithmeticPrimeNet Nfun μ M hnn n) s‖ ≤ C)
    (h_overlap :
      ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ Ω ∧
        ∀ s ∈ U, Filter.Tendsto
          (fun n => arithmeticPrimeNativePackage.R_stage
            (arithmeticPrimeNet Nfun μ M hnn n) s) atTop (nhds (R_H s))) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in Filter.atTop, ∀ s : ℂ, s ∈ K →
          dist (arithmeticPrimeNativePackage.R_stage
            (arithmeticPrimeNet Nfun μ M hnn n) s) (R_H s) < ε := by
  have hAscoli : AscoliExtraction
      (fun n s => arithmeticPrimeNativePackage.R_stage
        (arithmeticPrimeNet Nfun μ M hnn n) s) :=
    ascoliExtraction_of_relativelyCompact (ascoliExtractionHyp_of_loc_bdd _ h_loc_bdd)
  exact holomorphicMontelConvergence_from_ascoli hRH_holo hAscoli
    h_stage_holo h_loc_bdd h_overlap

#print axioms arithmeticPrimeNative_hconv_from_montel

end

end RHFormalization
