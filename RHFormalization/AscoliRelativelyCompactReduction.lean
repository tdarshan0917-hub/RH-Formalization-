import RHFormalization.AscoliFactored
import RHFormalization.MontelEquicontinuousOn
import Mathlib

/-!
# AscoliRelativelyCompact reduced to two standard inputs

Via Mathlib's clean `ArzelaAscoli.isCompact_of_equicontinuous` (which internally handles the
`UniformOnFun`/`IsClosedEmbedding` plumbing), `AscoliRelativelyCompact G` follows from:
  (1) pointwise compactness: `IsCompact (toFun '' range G)`  (← local boundedness)
  (2) equicontinuity: `Equicontinuous (↑ : range G → ↥Ω → ℂ)`  (← banked Montel equicontinuity)
-/

namespace RHFormalization
open Filter Topology Complex

/-- **AscoliRelativelyCompact from pointwise-compactness + equicontinuity.** -/
theorem ascoliRelativelyCompact_of_pointwiseCompact_equicontinuous
    (G : ℕ → C(Ω, ℂ))
    (hcompact_img : IsCompact (ContinuousMap.toFun '' (Set.range G)))
    (hequi : Equicontinuous ((↑) : (Set.range G) → (Ω : Set ℂ) → ℂ)) :
    AscoliRelativelyCompact G := by
  refine ⟨Set.range G, ?_, fun n => Set.mem_range_self n⟩
  exact ArzelaAscoli.isCompact_of_equicontinuous (Set.range G) hcompact_img hequi

#print axioms ascoliRelativelyCompact_of_pointwiseCompact_equicontinuous

end RHFormalization
