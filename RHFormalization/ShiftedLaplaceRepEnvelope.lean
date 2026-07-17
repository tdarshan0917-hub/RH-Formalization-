import RHFormalization.ZpoleFromSeries
import RHFormalization.ShiftedLaplaceRepZpoleResidue

namespace RHFormalization
noncomputable section
open Complex Filter Topology

abbrev RepZeroIndex := {ρ : ℂ // IsNontrivialZetaZero ρ ∧ ρ.re < 1/2}

def repToFull (ρ : RepZeroIndex) : {ρ : ℂ // IsNontrivialZetaZero ρ} :=
  ⟨ρ.1, ρ.2.1⟩

theorem repToFull_injective : Function.Injective repToFull := by
  intro a b h
  apply Subtype.ext
  have : (repToFull a).1 = (repToFull b).1 := congrArg Subtype.val h
  exact this

theorem repZpole_tendstoUniformlyOn
    (M : ZeroMultiplicityData) (D : ZeroPoleEnvelopeData M)
    (K : CompactAwayFromZeroPoles) :
    TendstoUniformlyOn
      (fun (t : Finset RepZeroIndex) x =>
        ∑ ρ ∈ t, zeroPoleSummand M ρ.1 x)
      (fun x => ∑' ρ : RepZeroIndex, zeroPoleSummand M ρ.1 x)
      atTop K.K := by
  have hsummable : Summable (fun ρ : RepZeroIndex => (D.u K) (repToFull ρ)) :=
    (D.h_summable K).comp_injective repToFull_injective
  exact tendstoUniformlyOn_tsum hsummable
    (fun ρ x hx => D.h_bound K (repToFull ρ) x hx)

#print axioms repZpole_tendstoUniformlyOn

end
end RHFormalization
