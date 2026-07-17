import RHFormalization.ResolventTraceHoloFromGrowth

/-!
# RHFormalization.DiscreteResolventModel

**Phase 2.** Package the spectral data + Weyl growth into a structure, and
expose `resolvent_trace_holo_from_sq_growth` as a method `FH_holo`.  This is the
reusable interface the operator-connection phase will produce and the limit/
identity phases will consume — replacing the old abstract `h_FH_holo` field with
a theorem grounded in explicit spectral data.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter

/-- A discrete spectral resolvent model: a real eigenvalue sequence that is
nonnegative and has Weyl growth `λₙ ≥ c·n²`.  This is exactly the data the
operator side exports (Appendix A: discrete spectrum bounded below with
quadratic growth), with no trace-class structure required. -/
structure DiscreteResolventModel where
  lam : ℕ → ℝ
  nonneg : ∀ n : ℕ, 0 ≤ lam n
  growthConst : ℝ
  growthConst_pos : 0 < growthConst
  growth : ∀ n : ℕ, growthConst * (n : ℝ) ^ 2 ≤ lam n

namespace DiscreteResolventModel

/-- The resolvent trace `F(s) = ∑ₙ 1/(s + λₙ)` of the model. -/
noncomputable def FH (M : DiscreteResolventModel) (s : ℂ) : ℂ :=
  ∑' n, (s + (M.lam n : ℂ))⁻¹

/-- **The model's resolvent trace is holomorphic on Ω** — a theorem, grounded
only in the model's spectral growth data.  This is the real replacement for the
abstract holomorphy assumption. -/
theorem FH_holo (M : DiscreteResolventModel) :
    HolomorphicOnC M.FH Ω :=
  resolvent_trace_holo_from_sq_growth M.lam M.growthConst M.growthConst_pos
    M.nonneg M.growth

#print axioms FH
#print axioms FH_holo

end DiscreteResolventModel

