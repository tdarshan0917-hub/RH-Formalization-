import RHFormalization.MontelSubsequenceAssembly
import RHFormalization.MontelEquicontinuousOn
import Mathlib

/-!
# AscoliExtraction factored: one named hard lemma + connective wiring

The σ-compactness of `Ω` (open ⊆ ℂ) makes convergence in `C(↥Ω, ℂ)` equal to locally
uniform convergence on every compact (`tendsto_iff_forall_isCompact_tendstoUniformlyOn`),
and `IsCompact.isSeqCompact` is unconditional — so the diagonalization is FREE.
`AscoliExtraction` thus reduces to ONE named hard lemma: `AscoliRelativelyCompact`.
-/

namespace RHFormalization
open Filter Topology Complex

/-- **The single named hard Ascoli lemma.** The bundled holomorphic sequence (as maps in
`C(↥Ω, ℂ)`) has compact closure. (To be discharged from
`ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`.) -/
def AscoliRelativelyCompact (G : ℕ → C(Ω, ℂ)) : Prop :=
  ∃ S : Set C(Ω, ℂ), IsCompact S ∧ ∀ n, G n ∈ S

end RHFormalization
