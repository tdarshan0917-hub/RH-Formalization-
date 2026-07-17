import RHFormalization.ShiftedLaplaceRepRestAnalytic
import RHFormalization.ShiftedLaplaceRepLUC

namespace RHFormalization
noncomputable section
open Complex Filter Topology Metric

def ZpoleRepSeriesExcept (M : ZeroMultiplicityData) (ρrep : ℂ) (s : ℂ) : ℂ :=
  ∑' ρ : RepZeroIndex, (if ρ.1 = ρrep then 0 else zeroPoleSummand M ρ.1 s)

theorem repRest_tendstoUniformlyOn
    (M : ZeroMultiplicityData) (D : ZeroPoleEnvelopeData M) (ρrep : ℂ)
    (K : CompactAwayFromZeroPoles) :
    TendstoUniformlyOn
      (fun (t : Finset RepZeroIndex) x =>
        ∑ ρ ∈ t, (if ρ.1 = ρrep then 0 else zeroPoleSummand M ρ.1 x))
      (fun x => ∑' ρ : RepZeroIndex,
        (if ρ.1 = ρrep then 0 else zeroPoleSummand M ρ.1 x))
      atTop K.K := by
  have hsummable : Summable (fun ρ : RepZeroIndex => (D.u K) (repToFull ρ)) :=
    (D.h_summable K).comp_injective repToFull_injective
  refine tendstoUniformlyOn_tsum hsummable ?_
  intro ρ x hx
  by_cases hr : ρ.1 = ρrep
  · simp only [hr, if_pos]
    have : (0:ℝ) ≤ (D.u K) (repToFull ρ) := by
      have := D.h_bound K (repToFull ρ) x hx
      exact le_trans (norm_nonneg _) this
    simpa using this
  · simp only [if_neg hr]
    exact D.h_bound K (repToFull ρ) x hx

theorem repRest_luc
    (M : ZeroMultiplicityData) (D : ZeroPoleEnvelopeData M) (ρrep : ℂ)
    (K : CompactAwayFromZeroPoles) :
    LocallyUniformConvergesOnC
      (fun n s => repRestPartial M ρrep n s)
      (ZpoleRepSeriesExcept M ρrep) K.K := by
  have hM := repRest_tendstoUniformlyOn M D ρrep K
  have hcomp := tendstoUniformlyOn_index_comp hM repSubtypeStage_tendsto
  have hfinal : TendstoUniformlyOn
      (fun n s => repRestPartial M ρrep n s)
      (ZpoleRepSeriesExcept M ρrep) atTop K.K := by
    refine hcomp.congr ?_
    filter_upwards with n
    intro x _
    rfl
  exact hfinal.tendstoLocallyUniformlyOn

#print axioms repRest_tendstoUniformlyOn
#print axioms repRest_luc

end
end RHFormalization
