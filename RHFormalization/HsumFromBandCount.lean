import RHFormalization.ZetaZeroBandFinite
import RHFormalization.HsumFromRate

/-!
# Step 1 — the band-count interface to `hsum`

Defines `bandTotal k` = total multiplicity of nontrivial zeros in height-band `k`
(finite, via `band_finite`), and proves:

  `Summable (fun k => bandTotal k / (1+k²))  →  hsum`.

After this, the ENTIRE remaining content of Pillar 2 is the single hypothesis
`Summable (fun k => bandTotal k / (1+k²))` — the zero-counting/density bound,
which the Gamma → zeta-strip → counting bricks exist to discharge.
-/

namespace RHFormalization
open Complex Set Classical

/-- Total multiplicity of nontrivial zeros in height-band `k`, as a real number.
Finite because `band_finite k` makes the band a finite set. -/
noncomputable def bandTotal (k : ℕ) : ℝ :=
  ∑ ρ ∈ (band_finite k).toFinset, (defaultZeroMultiplicityData.mult ρ : ℝ)

theorem bandTotal_nonneg (k : ℕ) : 0 ≤ bandTotal k := by
  unfold bandTotal
  apply Finset.sum_nonneg
  intro ρ _
  exact Nat.cast_nonneg _

/-- The filtered band sum over any finite `S` of *subtype* zeros is `≤ bandTotal k`. -/
theorem band_filter_le_bandTotal
    (S : Finset {ρ : ℂ // IsNontrivialZetaZero ρ}) (k : ℕ) :
    ∑ ρ ∈ S.filter (fun ρ => ⌊|ρ.1.im|⌋₊ = k),
      (defaultZeroMultiplicityData.mult ρ.1 : ℝ) ≤ bandTotal k := by
  classical
  unfold bandTotal
  set T : Finset {ρ : ℂ // IsNontrivialZetaZero ρ} := S.filter (fun ρ => ⌊|ρ.1.im|⌋₊ = k) with hT
  -- image of T under the coercion ρ ↦ ρ.1
  set TI : Finset ℂ := T.image (fun ρ => ρ.1) with hTI
  -- LHS = sum over TI (coercion is injective on T)
  have hsum_eq : ∑ ρ ∈ T, (defaultZeroMultiplicityData.mult ρ.1 : ℝ)
      = ∑ z ∈ TI, (defaultZeroMultiplicityData.mult z : ℝ) := by
    rw [hTI, Finset.sum_image]
    intro a _ b _ hab
    exact Subtype.ext hab
  rw [hsum_eq]
  -- TI ⊆ band set, mult ≥ 0
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    rw [hTI, Finset.mem_image] at hz
    obtain ⟨ρ, hρT, rfl⟩ := hz
    rw [hT, Finset.mem_filter] at hρT
    rw [Set.Finite.mem_toFinset]
    exact ⟨ρ.2, hρT.2⟩
  · intro z _ _
    exact Nat.cast_nonneg _

#print axioms band_filter_le_bandTotal

/-- **Step 1 interface.** If the band totals, weighted by `1/(1+k²)`, are summable,
then `hsum` holds. -/
theorem hsum_from_bandCount_summable
    (hsum_band : Summable (fun k => bandTotal k / (1 + (k : ℝ) ^ 2))) :
    Summable (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
      (defaultZeroMultiplicityData.mult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2)) :=
  hsum_of_count_rate defaultZeroMultiplicityData bandTotal bandTotal_nonneg
    band_filter_le_bandTotal hsum_band

#print axioms hsum_from_bandCount_summable

end RHFormalization
