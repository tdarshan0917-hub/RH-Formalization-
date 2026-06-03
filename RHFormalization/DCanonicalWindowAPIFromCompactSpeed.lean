import RHFormalization.DCanonicalWindowConcrete
import RHFormalization.CanonicalPrimePowerDWindowSpeedAPI

/-!
# RHFormalization.DCanonicalWindowAPIFromCompactSpeed

Bridge from quantitative compact-speed window convergence to the qualitative
`DCanonicalWindowAPI`.

The compact-speed API gives an explicit rate
`dist (...) (...) ≤ 1 / speed A n`.

To obtain qualitative local-uniform convergence, we additionally assume
`1 / speed A n → 0` on each compact set.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Build `DCanonicalWindowAPI W` from a compact-speed API, provided the inverse
speed tends to zero on every compact real set.
-/
def buildDCanonicalWindowAPIFromCompactSpeed
    {W : DCanonicalWindowData}
    {alpha : ℕ → DFiniteStage}
    (A : DCanonicalWindowCompactSpeedAPI W alpha)
    (h_cw_eq_one : W.c_w = 1)
    (h_inv_speed_tendsto_zero :
      ∀ (K : Set ℝ),
        IsCompact K →
          ∀ (ε : ℝ),
            0 < ε →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                (1 : ℝ) / A.speed K n < ε) :
    DCanonicalWindowAPI W :=
  { alpha := alpha
    h_cw_eq_one := h_cw_eq_one
    h_local_uniform_window := by
      intro K hK ε hε
      have hsmall :
          ∀ᶠ (n : ℕ) in Filter.atTop,
            (1 : ℝ) / A.speed K n < ε :=
        h_inv_speed_tendsto_zero K hK ε hε
      exact hsmall.mono (by
        intro n hn
        intro a ha
        have hle :
            dist (W.gbar_stage (alpha n) a) (W.G_limit a)
              ≤ (1 : ℝ) / A.speed K n :=
          A.h_compact_window_speed_rate K hK n a ha
        have hlt :
            dist (W.gbar_stage (alpha n) a) (W.G_limit a) < ε :=
          lt_of_le_of_lt hle hn
        simpa [h_cw_eq_one, one_mul] using hlt) }

end

end RHFormalization
