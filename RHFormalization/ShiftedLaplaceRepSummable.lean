import RHFormalization.ShiftedLaplaceRepMeromorphic

namespace RHFormalization
noncomputable section
open Complex Filter Topology Metric

theorem repZpole_summable_at
    (M : ZeroMultiplicityData) (D : ZeroPoleEnvelopeData M)
    (K : CompactAwayFromZeroPoles) (x : ℂ) (hx : x ∈ K.K) :
    Summable (fun ρ : RepZeroIndex => zeroPoleSummand M ρ.1 x) := by
  have hbound : Summable (fun ρ : RepZeroIndex => (D.u K) (repToFull ρ)) :=
    (D.h_summable K).comp_injective repToFull_injective
  refine Summable.of_norm_bounded hbound ?_
  intro ρ
  exact D.h_bound K (repToFull ρ) x hx

#print axioms repZpole_summable_at

end
end RHFormalization
