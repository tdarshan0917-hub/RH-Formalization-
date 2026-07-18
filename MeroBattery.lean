import RHFormalization.HPPEndgame
open Complex Set Topology Filter Metric RHFormalization
#check @MeromorphicOn
#check @MeromorphicAt
#check @AnalyticAt.meromorphicAt
#check @MeromorphicAt.add
#check @MeromorphicAt.div
#check @MeromorphicAt.const_smul
example (c s0 : ℂ) : MeromorphicAt (fun s => c / (s - s0)) s0 := by
  first
    | exact (analyticAt_const (v := c)).meromorphicAt.div
        ((analyticAt_id.sub analyticAt_const).meromorphicAt)
    | sorry
example (f g : ℂ → ℂ) (z : ℂ) (hf : MeromorphicAt f z) (hg : AnalyticAt ℂ g z) :
    MeromorphicAt (fun s => f s + g s) z := by
  first
    | exact hf.add hg.meromorphicAt
    | sorry
