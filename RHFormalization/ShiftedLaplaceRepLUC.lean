import RHFormalization.ShiftedLaplaceRepConvergence

namespace RHFormalization
noncomputable section
open Complex Filter Topology

def repZeroPolePartial (M : ZeroMultiplicityData) (n : ℕ) (s : ℂ) : ℂ :=
  ∑ ρ ∈ repSubtypeStage n, zeroPoleSummand M ρ.1 s

theorem repZpole_luc
    (M : ZeroMultiplicityData) (D : ZeroPoleEnvelopeData M)
    (K : CompactAwayFromZeroPoles) :
    LocallyUniformConvergesOnC
      (fun n s => repZeroPolePartial M n s)
      (ZpoleRepSeries M) K.K := by
  have hM := repZpole_tendstoUniformlyOn M D K
  have hcomp := tendstoUniformlyOn_index_comp hM repSubtypeStage_tendsto
  have hfinal : TendstoUniformlyOn
      (fun n s => repZeroPolePartial M n s)
      (ZpoleRepSeries M) atTop K.K := by
    refine hcomp.congr ?_
    filter_upwards with n
    intro x _
    rfl
  exact hfinal.tendstoLocallyUniformlyOn

#print axioms repZpole_luc

end
end RHFormalization
