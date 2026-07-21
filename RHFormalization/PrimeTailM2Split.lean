import RHFormalization.PrimeHeatIntegrandM2
import RHFormalization.GalerkinStieltjesRep
import Mathlib

/-!
# PrimeTailM2Split — T2: the prime tail integral in M2 coordinates

ROUTE CARD
1. Target: for Re s > 0, the tail Laplace of the prime heat difference
   splits as diag-tail + E₂-tail (integral of the banked T1 identity over
   Ioi t₀, using integrability of each piece). Unconditional, live net.
2. Consumer: T3a (diag-tail vs B-spike-tail matching) and T3b (E₂-tail
   schedule bound) → galTail control at depth → DBFFO3ParabolaDepthHstar.
3. Raw B on Ω? NO. hstar-equivalent hypothesis? NONE.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators

/-- The tail diag-term Laplace integral. -/
def diagTailIntegral (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t in Ioi spikeT0,
    Complex.exp (-(s + (SupVConst : ℂ)) * (t:ℂ)) *
      ((- t * (∑ m : Fin (admN n),
        galerkinV (N := admN n) 1
          (activePrimePowerCodesCenterBelow (admR n))
          ppWeightReal (admL n) m m
        * Real.exp (-(t * galerkinLam (admL n) (m : ℕ)))) : ℝ) : ℂ)

/-- The tail E₂ Laplace integral. -/
def e2TailIntegral (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t in Ioi spikeT0,
    Complex.exp (-(s + (SupVConst : ℂ)) * (t:ℂ)) *
      ((spikeTransferE2 (N := admN n) 1
        (activePrimePowerCodesCenterBelow (admR n))
        ppWeightReal (admL n) t : ℝ) : ℂ)

/-- **T2: the prime tail = diag-tail + E₂-tail**, given integrability of
the two pieces (both to be discharged by T3's estimates; stated with the
integrability hypotheses explicit so the split itself is unconditional
algebra + integral_add). -/
theorem primeTail_eq_diag_add_e2
    (n : ℕ) (s : ℂ)
    (hdiag : IntegrableOn (fun t : ℝ =>
      Complex.exp (-(s + (SupVConst : ℂ)) * (t:ℂ)) *
        ((- t * (∑ m : Fin (admN n),
          galerkinV (N := admN n) 1
            (activePrimePowerCodesCenterBelow (admR n))
            ppWeightReal (admL n) m m
          * Real.exp (-(t * galerkinLam (admL n) (m : ℕ)))) : ℝ) : ℂ))
      (Ioi spikeT0) volume)
    (he2 : IntegrableOn (fun t : ℝ =>
      Complex.exp (-(s + (SupVConst : ℂ)) * (t:ℂ)) *
        ((spikeTransferE2 (N := admN n) 1
          (activePrimePowerCodesCenterBelow (admR n))
          ppWeightReal (admL n) t : ℝ) : ℂ))
      (Ioi spikeT0) volume) :
    (∫ t in Ioi spikeT0,
      Complex.exp (-(s + (SupVConst : ℂ)) * (t:ℂ)) *
        (((∑ i : Fin (admN n), Real.exp (-t * admPerturbedLam n i))
          - (∑ i : Fin (admN n),
              Real.exp (-t * galerkinLam (admL n) (i : ℕ))) : ℝ) : ℂ))
      = diagTailIntegral n s + e2TailIntegral n s := by
  unfold diagTailIntegral e2TailIntegral
  rw [← MeasureTheory.integral_add hdiag he2]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  show Complex.exp (-(s + (SupVConst : ℂ)) * (t:ℂ)) *
      (((∑ i : Fin (admN n), Real.exp (-t * admPerturbedLam n i))
        - (∑ i : Fin (admN n),
            Real.exp (-t * galerkinLam (admL n) (i : ℕ))) : ℝ) : ℂ)
    = Complex.exp (-(s + (SupVConst : ℂ)) * (t:ℂ)) *
        ((- t * (∑ m : Fin (admN n),
          galerkinV (N := admN n) 1
            (activePrimePowerCodesCenterBelow (admR n))
            ppWeightReal (admL n) m m
          * Real.exp (-(t * galerkinLam (admL n) (m : ℕ)))) : ℝ) : ℂ)
      + Complex.exp (-(s + (SupVConst : ℂ)) * (t:ℂ)) *
          ((spikeTransferE2 (N := admN n) 1
            (activePrimePowerCodesCenterBelow (admR n))
            ppWeightReal (admL n) t : ℝ) : ℂ)
  rw [primeHeatDiff_eq_M2 n t]
  push_cast
  ring

#print axioms diagTailIntegral
#print axioms e2TailIntegral
#print axioms primeTail_eq_diag_add_e2

end

end RHFormalization
