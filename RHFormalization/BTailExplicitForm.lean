import RHFormalization.GalerkinStieltjesRep
import RHFormalization.GalerkinTailSplit
import Mathlib

/-!
# BTailExplicitForm — C1: the B-tail as an explicit spike integral

ROUTE CARD
1. Target: define `bTail n s := ∫_{Ioi t₀} galBIntegrand n s t` and prove
   (i) it is the B-side of galTail (split identity, Re s > 0), and
   (ii) per-q integrability on the tail (from the banked full-line
   integrability restricted). Unconditional, live net, no bounds asserted.
2. Consumer: C2 (bTail vs mainTermIntegral tail — THE cancellation) →
   B-tail control ⇔ O3 ⇔ DBFFO3ParabolaDepthHstar → RH.
3. Raw B on Ω? NO — Re s > 0 representation only, no continuation claim.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators

/-- The B-spike tail integral. -/
def bTail (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t in Ioi spikeT0, galBIntegrand n s t

/-- The F-side tail integral (Laplace form). -/
def fTailIntegral (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t in Ioi spikeT0, galFIntegrand n s t

/-- B-integrand integrable on the tail (restriction of banked full-line). -/
theorem galB_integrand_integrableOn_tail (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => galBIntegrand n s t) (Ioi spikeT0) volume := by
  have hfull := galB_integrand_integrableOn n s hs
  have hsub : Ioi spikeT0 ⊆ Ioi (0:ℝ) := by
    intro t ht
    have h0 : (0:ℝ) < spikeT0 := spikeT0_pos
    exact lt_trans h0 ht
  exact hfull.mono_set hsub

/-- F-integrand integrable on the tail. -/
theorem galF_integrand_integrableOn_tail (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => galFIntegrand n s t) (Ioi spikeT0) volume := by
  have hfull := galF_integrand_integrableOn n s hs
  have hsub : Ioi spikeT0 ⊆ Ioi (0:ℝ) := by
    intro t ht
    exact lt_trans spikeT0_pos ht
  exact hfull.mono_set hsub

/-- **C1: galTail = F-tail − B-tail** (Re s > 0). -/
theorem galTail_eq_fTail_sub_bTail (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    galTail n s = fTailIntegral n s - bTail n s := by
  unfold galTail fTailIntegral bTail galQResIntegrand
  exact MeasureTheory.integral_sub
    (galF_integrand_integrableOn_tail n s hs)
    (galB_integrand_integrableOn_tail n s hs)

#print axioms bTail
#print axioms galB_integrand_integrableOn_tail
#print axioms galTail_eq_fTail_sub_bTail

end

end RHFormalization
