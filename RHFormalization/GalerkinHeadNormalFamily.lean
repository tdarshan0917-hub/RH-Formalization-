import RHFormalization.GalerkinHeadHolo
import RHFormalization.GalerkinHeadIntegralBound
import RHFormalization.GalerkinTailSplit
import Mathlib

/-!
# GalerkinHeadNormalFamily — the head is a normal family on Ω

ROUTE CARD
1. Target: `galHead n` is `HolomorphicOnC … Ω` for every `n`, and the family
   `{galHead n}` is uniformly bounded on every Ω-compact.
2. Objects: `galQResHead_differentiableAt` (banked, entire),
   `galQRes_head_integral_bound` (banked, uniform on ℂ-compacts),
   `Differentiable.analyticAt`.
3. Raw B on Ω? NO. 4. R = F − raw B? NO. 5. True outright.
6. Manuscript: D.KEY-FORM ⟹ D.MR.2 (local boundedness), the Montel input.
7. Consumer: Vitali–Porter on the head sector.

SCOPE, STATED HONESTLY. This gives the normal-family property for the HEAD, not
for `R_stage`. By `R_stage_eq_head_add_tail`, `R_stage = head + tail` on RHP(0),
and `tail = F-tail − B-tail`. The F-tail is banked (`galF_tail_uniform_bound`,
`galFTailClosed_holo`). The B-tail is NOT bounded uniformly in `n` by any argument
in this repo, and by `B_sub_compensator_eq` +
`galerkin_B_stage_eq_vonMangoldt_partial_sum`, an `n`-uniform B-side bound at
parabola depth IS `DBFFO3ParabolaDepthHstar`. So `R_stage` local boundedness
remains equivalent to O3. Bounding the B-tail is not a step toward O3; it is O3.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex MeasureTheory
open scoped BigOperators

/-- The head is entire. -/
theorem galHead_differentiable (n : ℕ) : Differentiable ℂ (galHead n) :=
  fun z => galQResHead_differentiableAt n z

/-- **THE HEAD IS Ω-HOLOMORPHIC.** A fortiori: it is entire. -/
theorem galHead_holo (n : ℕ) : HolomorphicOnC (galHead n) Ω := by
  intro z _
  exact ((galHead_differentiable n).analyticAt z).analyticWithinAt

/-- **THE HEAD IS A NORMAL FAMILY.** Ω-holomorphic, and uniformly bounded on
every Ω-compact, uniformly in `n`, AT ANY PARABOLA DEPTH. -/
theorem galHead_normal_family (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty) :
    (∀ n : ℕ, HolomorphicOnC (galHead n) Ω) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), ∀ s ∈ K, ‖galHead n s‖ ≤ C) := by
  refine ⟨galHead_holo, ?_⟩
  obtain ⟨C, hC0, hbd⟩ := galQRes_head_integral_bound K hK hne
  exact ⟨C, hC0, fun n s hs => hbd n s hs⟩

#print axioms galHead_differentiable
#print axioms galHead_holo
#print axioms galHead_normal_family

end RHFormalization
