import Mathlib.NumberTheory.LSeries.ZetaZeros
import RHFormalization.ZetaZeroCounting

/-!
# Band finiteness for nontrivial zeta zeros (Pillar 2, provider brick 1)

Each height-band `{ρ : 0<re<1, ⌊|im ρ|⌋₊ = k}` of nontrivial zeros is FINITE,
via Mathlib's `IsCompact.inter_riemannZetaZeros_finite` applied to the compact
rectangle `[0,1] × [-(k+1), k+1]`.

This does NOT bound how the band cardinality grows with `k` — that growth is the
genuine analytic counting input and remains the single open hypothesis downstream.
This brick only establishes finiteness, so `rate k` can be DEFINED.
-/

namespace RHFormalization
open Complex Set

/-- A nontrivial zeta zero (our predicate) lies in Mathlib's `riemannZetaZeros`. -/
theorem mem_riemannZetaZeros_of_isNontrivial {ρ : ℂ} (h : IsNontrivialZetaZero ρ) :
    ρ ∈ riemannZetaZeros := by
  rw [mem_riemannZetaZeros]
  exact h.1

/-- The closed band rectangle at height index `k`. -/
def bandRect (k : ℕ) : Set ℂ :=
  {z : ℂ | z.re ∈ Set.Icc (0:ℝ) 1 ∧ z.im ∈ Set.Icc (-(k+1 : ℝ)) (k+1)}

theorem isCompact_bandRect (k : ℕ) : IsCompact (bandRect k) := by
  have : bandRect k = (Complex.equivRealProdCLM.symm) ''
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-(k+1 : ℝ)) (k+1)) := by
    ext z
    simp only [bandRect, Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Set.mem_Icc]
    constructor
    · rintro ⟨hre, him⟩
      exact ⟨(z.re, z.im), ⟨hre, him⟩, by apply Complex.ext <;> simp⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact ⟨ha, hb⟩
  rw [this]
  apply (isCompact_Icc.prod isCompact_Icc).image
  exact Complex.equivRealProdCLM.symm.continuous

/-- **Band finiteness.** The set of nontrivial zeta zeros in band `k` is finite. -/
theorem band_finite (k : ℕ) :
    {ρ : ℂ | IsNontrivialZetaZero ρ ∧ ⌊|ρ.im|⌋₊ = k}.Finite := by
  apply Set.Finite.subset ((isCompact_bandRect k).inter_riemannZetaZeros_finite)
  intro ρ hρ
  obtain ⟨hnt, hband⟩ := hρ
  refine ⟨?_, mem_riemannZetaZeros_of_isNontrivial hnt⟩
  obtain ⟨_, h0, h1⟩ := hnt
  refine ⟨⟨h0.le, h1.le⟩, ?_⟩
  have : |ρ.im| ≤ (k : ℝ) + 1 := by
    have := Nat.lt_floor_add_one |ρ.im|
    rw [hband] at this
    linarith [this]
  rw [Set.mem_Icc]
  constructor
  · linarith [abs_le.mp this |>.1]
  · linarith [abs_le.mp this |>.2]

#print axioms band_finite

end RHFormalization
