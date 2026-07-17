import RHFormalization.EigenvalueGrowthSummable

/-!
# RHFormalization.ResolventTraceHoloFromGrowth

Compatibility wrapper.

The old file expected a theorem named
`summable_one_div_one_add_lam_of_sq_growth`.  The current banked theorem is
`Fstage_holo_from_weyl`, which proves the same holomorphy statement directly
from Weyl growth.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter

/-- Resolvent trace holomorphy from pure square growth `c n^2 ≤ λ_n`.

This is a compatibility theorem for the older `DiscreteResolventModel` route.
It is now proved by the banked `Fstage_holo_from_weyl` theorem with `C = 0`.
-/
theorem resolvent_trace_holo_from_sq_growth
    (lam : ℕ → ℝ)
    (c : ℝ)
    (hc : 0 < c)
    (hnonneg : ∀ n : ℕ, 0 ≤ lam n)
    (hgrowth : ∀ n : ℕ, c * (n : ℝ) ^ 2 ≤ lam n) :
    HolomorphicOnC (fun s => ∑' n, (s + (lam n : ℂ))⁻¹) Ω :=
  Fstage_holo_from_weyl
    lam
    hnonneg
    c
    0
    hc
    (by
      intro n
      simpa using hgrowth n)

#print axioms resolvent_trace_holo_from_sq_growth

end

end RHFormalization
