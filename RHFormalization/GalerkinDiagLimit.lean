/-
GalerkinDiagLimit.lean

THE DIAGONAL SPECTRUM LIMIT: along the genuine stage exhaustion (dimension
n+1, codes below n+1, both moving), each k-th smallest eigenvalue
converges. Step split: dimension growth is a pure decrease (banked
interlacing), code growth drifts by at most the envelope tail over the new
codes (banked drift bound); the drift increments are nonneg with partial
sums dominated by the global envelope tsum, hence summable; the banked
almost-antitone engine closes it. The limit inherits the pi^2 floor.

lamDiag is the limiting spectrum of Front F's FH.
-/
import RHFormalization.GalerkinDimMonotone
import RHFormalization.GalerkinCodeDrift
import RHFormalization.AlmostAntitoneLimit

namespace RHFormalization

noncomputable section

open Complex Filter

/-- Stage code set (dimension n+1's codes). -/
def stageCodes (n : ℕ) : Finset ℕ :=
  activePrimePowerCodesCenterBelow ((n : ℝ) + 1)

theorem stageCodes_mono {n m : ℕ} (h : n ≤ m) :
    stageCodes n ⊆ stageCodes m := by
  apply activePrimePowerCodesCenterBelow_mono
  have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr h
  linarith

/-- The k-th SMALLEST genuine eigenvalue at stage k+1+j (dimension k+2+j,
codes at cutoff k+2+j). -/
def diagLamAt (k : ℕ) (j : ℕ) : ℝ :=
  perturbedEigenvalues (galerkinFreeMu (k + 2 + j) 1)
    (galerkinVC_isHermitian (N := k + 2 + j) 1 (stageCodes (k + 1 + j))
      ppWeightReal 1)
    (Fin.rev (⟨k, by omega⟩ : Fin (k + 2 + j)))

/-- The drift increment at diagonal step j. -/
def diagEps (k : ℕ) (j : ℕ) : ℝ :=
  tailConst (stageCodes (k + 2 + j) \ stageCodes (k + 1 + j))

theorem diagEps_nonneg (k j : ℕ) : 0 ≤ diagEps k j :=
  tailConst_nonneg _

/-- Partial sums of the drift increments are dominated by the global
envelope sum: disjoint code increments inject into ℕ. -/
theorem diagEps_partial_le (k : ℕ) (J : ℕ) :
    ∑ j ∈ Finset.range J, diagEps k j ≤ SupVConst := by
  unfold diagEps tailConst
  rw [← Finset.sum_biUnion]
  · calc ∑ q ∈ (Finset.range J).biUnion
          (fun j => stageCodes (k + 2 + j) \ stageCodes (k + 1 + j)),
          |ppWeightReal q| * bumpEnvelope q
        ≤ ∑' q : ℕ, |ppWeightReal q| * bumpEnvelope q := by
          first
            | exact sum_le_tsum _
                (fun i _ => mul_nonneg (abs_nonneg _) (bumpEnvelope_nonneg _))
                summable_weight_envelope
            | exact Finset.sum_le_tsum _
                (fun i _ => mul_nonneg (abs_nonneg _) (bumpEnvelope_nonneg _))
                summable_weight_envelope
            | exact summable_weight_envelope.sum_le_tsum _
                (fun i _ => mul_nonneg (abs_nonneg _) (bumpEnvelope_nonneg _))
      _ = SupVConst := rfl
  · intro a ha b hb hab
    -- increments at different steps are disjoint: nested sdiffs
    wlog hlt : a < b generalizing a b
    · exact (this hb ha (Ne.symm hab) (by omega)).symm
    first
      | { apply Finset.disjoint_left.mpr
          intro q hqa hqb
          have h1 : q ∈ stageCodes (k + 2 + a) :=
            (Finset.mem_sdiff.mp hqa).1
          have h2 : q ∉ stageCodes (k + 1 + b) :=
            (Finset.mem_sdiff.mp hqb).2
          apply h2
          apply stageCodes_mono (by omega : k + 2 + a ≤ k + 1 + b) h1 }
      | { simp only [Finset.disjoint_left, Finset.mem_sdiff]
          rintro q ⟨h1, _⟩ ⟨_, h2⟩
          exact h2 (stageCodes_mono (by omega : k + 2 + a ≤ k + 1 + b) h1) }

theorem diagEps_summable (k : ℕ) : Summable (diagEps k) := by
  first
    | exact summable_of_sum_range_le (fun j => diagEps_nonneg k j)
        (fun J => diagEps_partial_le k J)
    | exact Summable.of_sum_range_le (fun j => diagEps_nonneg k j)
        (fun J => diagEps_partial_le k J)

/-- The diagonal step estimate: dim step decreases, code step drifts. -/
theorem diagLamAt_step (k j : ℕ) :
    diagLamAt k (j + 1) ≤ diagLamAt k j + diagEps k j := by
  -- intermediate: dimension k+2+(j+1), OLD codes
  set mid : ℝ := perturbedEigenvalues (galerkinFreeMu (k + 2 + (j + 1)) 1)
    (galerkinVC_isHermitian (N := k + 2 + (j + 1)) 1 (stageCodes (k + 1 + j))
      ppWeightReal 1)
    (Fin.rev (⟨k, by omega⟩ : Fin (k + 2 + (j + 1)))) with hmid
  have hdim : mid ≤ diagLamAt k j := by
    rw [hmid]
    unfold diagLamAt
    have hle : k + 2 + j ≤ k + 2 + (j + 1) := by omega
    have h := galerkinEigenvalues_dim_mono (n := k + 2 + j)
      (m := k + 2 + (j + 1)) (stageCodes (k + 1 + j)) hle
      (⟨k, by omega⟩ : Fin (k + 2 + j))
    have hcast : Fin.castLE hle (⟨k, by omega⟩ : Fin (k + 2 + j))
        = (⟨k, by omega⟩ : Fin (k + 2 + (j + 1))) := by
      apply Fin.eq_of_val_eq
      first
        | simp [Fin.val_castLE]
        | rfl
    rw [hcast] at h
    exact h
  have hcode : diagLamAt k (j + 1) ≤ mid + diagEps k j := by
    rw [hmid]
    unfold diagLamAt diagEps
    have hsub : stageCodes (k + 1 + j) ⊆ stageCodes (k + 2 + j) := by
      apply stageCodes_mono; omega
    have hsub' : stageCodes (k + 1 + j) ⊆ stageCodes (k + 1 + (j + 1)) := by
      apply stageCodes_mono; omega
    have hsame : k + 2 + j = k + 1 + (j + 1) := by omega
    have h := galerkinEigenvalues_code_drift
      (stageCodes (k + 1 + j)) (stageCodes (k + 1 + (j + 1)))
      hsub' (galerkinFreeMu (k + 2 + (j + 1)) 1)
      (Fin.rev (⟨k, by omega⟩ : Fin (k + 2 + (j + 1))))
    have habs := (abs_le.mp h).2
    have hrw : stageCodes (k + 2 + j) = stageCodes (k + 1 + (j + 1)) := by
      rw [hsame]
    rw [hrw]
    linarith [habs]
  linarith

/-- Floor transport to the diagonal. -/
theorem diagLamAt_floor (k j : ℕ) :
    Real.pi ^ 2 * ((k : ℝ) + 1) ^ 2 - SupVConst ≤ diagLamAt k j := by
  unfold diagLamAt
  have h := galerkinEigenvalue_ge_pi_sq (N := k + 2 + j)
    (stageCodes (k + 1 + j))
    (Fin.rev (⟨k, by omega⟩ : Fin (k + 2 + j)))
  have hrevrev : ((Fin.rev (Fin.rev (⟨k, by omega⟩ : Fin (k + 2 + j)))) : ℕ)
      = k := by
    first
      | (rw [Fin.rev_rev])
      | (rw [Fin.val_rev, Fin.val_rev]; omega)
      | simp
  rw [hrevrev] at h
  exact h

/-- **THE DIAGONAL LIMITING SPECTRUM.** -/
theorem exists_diagLam_limit (k : ℕ) :
    ∃ L : ℝ, Real.pi ^ 2 * ((k : ℝ) + 1) ^ 2 - SupVConst ≤ L ∧
      Tendsto (diagLamAt k) atTop (nhds L) :=
  exists_tendsto_of_almost_antitone (diagLamAt k) (diagEps k)
    (diagEps_nonneg k) (diagEps_summable k) (diagLamAt_step k)
    (Real.pi ^ 2 * ((k : ℝ) + 1) ^ 2 - SupVConst) (diagLamAt_floor k)

/-- The diagonal limiting spectrum, extracted. -/
def lamDiag (k : ℕ) : ℝ := Classical.choose (exists_diagLam_limit k)

theorem lamDiag_floor (k : ℕ) :
    Real.pi ^ 2 * ((k : ℝ) + 1) ^ 2 - SupVConst ≤ lamDiag k :=
  (Classical.choose_spec (exists_diagLam_limit k)).1

theorem diagLamAt_tendsto_lamDiag (k : ℕ) :
    Tendsto (diagLamAt k) atTop (nhds (lamDiag k)) :=
  (Classical.choose_spec (exists_diagLam_limit k)).2

/-- The SHIFTED diagonal limit is nonneg with full pi^2 Weyl growth --
DiscreteResolventModel's hypotheses, verbatim. -/
theorem lamDiag_shifted_nonneg (k : ℕ) : 0 ≤ lamDiag k + SupVConst := by
  have h := lamDiag_floor k
  have hsq : (0:ℝ) ≤ Real.pi ^ 2 * ((k : ℝ) + 1) ^ 2 := by positivity
  linarith

theorem lamDiag_shifted_growth (k : ℕ) :
    Real.pi ^ 2 * (k : ℝ) ^ 2 ≤ lamDiag k + SupVConst := by
  have h := lamDiag_floor k
  have hsq : Real.pi ^ 2 * (k : ℝ) ^ 2
      ≤ Real.pi ^ 2 * ((k : ℝ) + 1) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg Real.pi)
    have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith
  linarith

#print axioms stageCodes_mono
#print axioms diagEps_partial_le
#print axioms diagEps_summable
#print axioms diagLamAt_step
#print axioms diagLamAt_floor
#print axioms exists_diagLam_limit
#print axioms lamDiag_shifted_nonneg
#print axioms lamDiag_shifted_growth

end

end RHFormalization
