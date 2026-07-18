import RHFormalization.DefaultZeroExhaustion
open Complex Set Topology Filter
#check @analyticOrderAt
#check @analyticOrderAt_eq_top
#check @analyticOrderAt_eq_zero
#check @AnalyticAt.analyticOrderAt_eq_zero
#check @AnalyticAt.order
#check @AnalyticAt.order_eq_top_iff
#check @AnalyticAt.order_eq_zero_iff
#check @AnalyticAt.order_pos_iff
#check @ENat.toNat
#check @ENat.toNat_pos
#check @ENat.pos_iff_ne_zero
example (x : ℕ∞) (h0 : x ≠ 0) (htop : x ≠ ⊤) : 0 < x.toNat := by
  first
    | exact ENat.toNat_pos.mpr ⟨h0, htop⟩
    | (lift x to ℕ using htop; simpa using Nat.pos_of_ne_zero (by exact_mod_cast h0))
    | sorry
