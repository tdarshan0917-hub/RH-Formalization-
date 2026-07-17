import RHFormalization.MainTheorem
import RHFormalization.FSideWrapperBuilders
import RHFormalization.HSidePoleWitness
import RHFormalization.DefaultLocalPoleObstruction
import RHFormalization.OmegaTopology

/-!
# THE HONEST ENDPOINT (manuscript-faithful, firewall-enforced)

RH from exactly the manuscript's content inputs, through the banked engine
(`mainTheorem_from_H_grouped_pole_layer`). No designed witnesses anywhere.

## FIREWALL RULE (binding on all future files feeding this endpoint)
The raw prime-power series B may only ever be evaluated/asserted on its
convergence half-plane `RightHalfPlane σ₀`. NO hypothesis may assert
holomorphy/regularity of raw `Bshared` at any point of Ω outside that
half-plane. Any such hypothesis is unconditionally FALSE for the genuine
package (divergence inside the parabola Re s = −(Im s)²) or secretly RH
for a degenerate one. Ω-continuation lives ONLY in FH, RH, Harch, Zpole.

## The content inputs (the manuscript's burden, nothing else)
* ZF        — zeta zero facts (nontrivial zeros off the real axis)
* D         — Appendix D export: FH, RH ∈ O(Ω), FH = B + RH on ℜs > D.σ₀
* H         — Appendix H package: Zpole ∈ Mer(Ω), Harch ∈ O(Ω),
              Bzero = Harch − Zpole on ℜs > H.σ₀
* E         — Appendix E: D.B = H.Bzero on a common half-plane
* G         — H-side pole witness layer (grouped principal parts of Zpole
              at witness pole points; supplied by the envelope/normal-form
              chain, NOT by raw-B regularity)
* M         — meromorphic identity theorem (overlap EqOn ⟹ Ω EqOn)
* O         — local pole obstruction (local identity + holo ⟹ no pole)
-/

namespace RHFormalization
noncomputable section
open Complex Set

theorem RH_from_manuscript_inputs
    (ZF : ZetaZeroFacts)
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (G : HSidePoleWitnessLayer H)
    (M : MeromorphicIdentityTheoremAPI D H E)
    (O : LocalPoleObstructionAPI D H E) :
    RiemannHypothesis :=
  mainTheorem_from_H_grouped_pole_layer
    ZF D H E G M
    (buildHtotHolomorphicAPIFromSummands D H)
    (buildLocalEqualityAtWitnessAPIFromOmega defaultOpenOmegaAPI D H E)
    (buildHolomorphicOnToAtAPIFromOmega defaultOpenOmegaAPI)
    O

#check @RH_from_manuscript_inputs
#print axioms RH_from_manuscript_inputs

end
end RHFormalization
