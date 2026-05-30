import RHFormalization.DOperatorExport

/-!
# RHFormalization.DCanonicalWindowConcrete

Theorem-backed helper layer for D.CANONICAL-WINDOW.

This file replaces the old `True`-shaped window placeholder by a concrete
compact-uniform epsilon statement and records the consequence after the
normalization `c_w = 1`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/--
Build the canonical-window API from an explicit compact-uniform epsilon
convergence theorem.
-/
def buildDCanonicalWindowAPIFromCompactUniform
    (W : DCanonicalWindowData)
    (alpha : ℕ → DFiniteStage)
    (h_cw_eq_one : W.c_w = 1)
    (h_local_uniform_window :
      ∀ A : Set ℝ,
        IsCompact A →
          ∀ ε : ℝ,
            0 < ε →
              ∀ᶠ n in Filter.atTop,
                ∀ a : ℝ,
                  a ∈ A →
                    dist
                      (W.gbar_stage (alpha n) a)
                      (W.c_w * W.G_limit a) < ε) :
    DCanonicalWindowAPI W :=
  { alpha := alpha
    h_cw_eq_one := h_cw_eq_one
    h_local_uniform_window := h_local_uniform_window }

/--
After the canonical normalization `c_w = 1`, the compact-uniform convergence is
to `G_limit` itself.
-/
theorem DCanonicalWindowAPI.local_uniform_to_G_limit
    {W : DCanonicalWindowData}
    (A : DCanonicalWindowAPI W)
    (K : Set ℝ)
    (hK : IsCompact K)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      ∀ a : ℝ,
        a ∈ K →
          dist
            (W.gbar_stage (A.alpha n) a)
            (W.G_limit a) < ε := by
  have hraw :=
    A.h_local_uniform_window K hK ε hε
  simpa [A.h_cw_eq_one] using hraw

end

end RHFormalization
