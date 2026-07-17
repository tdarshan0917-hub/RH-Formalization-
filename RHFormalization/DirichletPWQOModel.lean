import RHFormalization.DiscreteResolventModel

/-!
# RHFormalization.DirichletPWQOModel
**Phase 3 (Option B).** Lemma A.GROWTH encoded faithfully → `DiscreteResolventModel`
→ operator-side holomorphy `FH_holo` for the Dirichlet PWQO spectrum.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter

/-- Faithful encoding of the manuscript's Dirichlet PWQO spectral data, after
the Section-2.5 global nonnegativity shift `H̃ = H + M·I`. -/
structure DirichletPWQOData where
  L : ℝ
  L_pos : 0 < L
  lamShifted : ℕ → ℝ
  nonneg : ∀ n : ℕ, 0 ≤ lamShifted n
  /-- **Lemma A.GROWTH (shifted):** `λₙ(H̃) ≥ (n·π / 2L)²`. -/
  growth : ∀ n : ℕ, ((n : ℝ) * Real.pi / (2 * L)) ^ 2 ≤ lamShifted n

namespace DirichletPWQOData

noncomputable def growthConst (D : DirichletPWQOData) : ℝ :=
  (Real.pi / (2 * D.L)) ^ 2

theorem growthConst_pos (D : DirichletPWQOData) : 0 < D.growthConst := by
  unfold growthConst
  have h2L : 0 < 2 * D.L := by linarith [D.L_pos]
  positivity

theorem growth_sq (D : DirichletPWQOData) :
    ∀ n : ℕ, D.growthConst * (n : ℝ) ^ 2 ≤ D.lamShifted n := by
  intro n
  have h := D.growth n
  unfold growthConst
  have hrw : ((n : ℝ) * Real.pi / (2 * D.L)) ^ 2
      = (Real.pi / (2 * D.L)) ^ 2 * (n : ℝ) ^ 2 := by
    rw [mul_comm, mul_div_assoc]; ring
  rw [hrw] at h
  exact h

noncomputable def toModel (D : DirichletPWQOData) : DiscreteResolventModel where
  lam := D.lamShifted
  nonneg := D.nonneg
  growthConst := D.growthConst
  growthConst_pos := D.growthConst_pos
  growth := D.growth_sq

theorem FH_holo (D : DirichletPWQOData) :
    HolomorphicOnC (fun s => ∑' n, (s + (D.lamShifted n : ℂ))⁻¹) Ω :=
  D.toModel.FH_holo

#print axioms growth_sq
#print axioms toModel
#print axioms FH_holo

end DirichletPWQOData
