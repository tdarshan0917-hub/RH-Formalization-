import RHFormalization.MeromorphyAssembly
open Complex Set Topology Filter Metric RHFormalization
-- A: THE BRIDGE — does index-precomposition typecheck against the raw def?
example {ι κ : Type} {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {s : Set ℂ}
    {p : Filter ι} {q : Filter κ} {g : κ → ι}
    (h : TendstoUniformlyOn F f p s) (hg : Filter.Tendsto g q p) :
    TendstoUniformlyOn (fun m => F (g m)) f q s := by
  first
    | exact fun u hu => hg.eventually (h u hu)
    | (intro u hu; exact hg.eventually (h u hu))
    | sorry
-- B: sum over a subtype-finset vs the original finset
#check @Finset.sum_subtype
#check @Finset.sum_attach
#check @Finset.subtype
-- C: Summable comparison signatures in this Mathlib
#check @Summable.of_nonneg_of_le
example (u : ℕ → ℝ) (c : ℝ) (hu : Summable u) : Summable (fun n => c * u n) := by
  first
    | exact hu.mul_left c
    | exact (hu.mul_left c :)
    | sorry
-- D: tsum of norms bound (for C2's majorant on compacts)
#check @norm_tsum_le_tsum_norm
#check @Summable.of_norm
