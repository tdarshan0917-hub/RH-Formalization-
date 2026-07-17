/-
GalerkinLimitSpectrum.lean

THE LIMITING SPECTRUM AT FIXED CODES: for each fixed code set qs and each
index k, the k-th SMALLEST genuine galerkin eigenvalue at dimension
k+1+j is antitone in j (banked dimension monotonicity) and floored by
pi^2 (k+1)^2 - SupVConst (banked concrete Weyl floor), hence converges to
its infimum lamInf qs k. The limit inherits the floor -- exactly the
growth hypothesis DiscreteResolventModel needs after the SupVConst shift.
-/
import RHFormalization.GalerkinDimMonotone

namespace RHFormalization

noncomputable section

open Complex Filter

/-- The k-th SMALLEST genuine eigenvalue at dimension k+1+j, as a total
function of j (dimension always exceeds the index). -/
def lamAt (qs : Finset ℕ) (k : ℕ) (j : ℕ) : ℝ :=
  perturbedEigenvalues (galerkinFreeMu (k + 1 + j) 1)
    (galerkinVC_isHermitian (N := k + 1 + j) 1 qs ppWeightReal 1)
    (Fin.rev (⟨k, by omega⟩ : Fin (k + 1 + j)))

/-- The floor transports to lamAt: the val of rev ⟨k,_⟩ in Fin (k+1+j) is
k + j... no: rev has val (k+1+j) - 1 - k = j. CAREFUL: the k-th SMALLEST
means rev index; galerkinEigenvalue_ge_pi_sq at index (rev i) gives growth
in (rev (rev i)) = i. We state the floor directly. -/
theorem lamAt_floor (qs : Finset ℕ) (k j : ℕ) :
    Real.pi ^ 2 * ((k : ℝ) + 1) ^ 2 - SupVConst ≤ lamAt qs k j := by
  unfold lamAt
  have h := galerkinEigenvalue_ge_pi_sq (N := k + 1 + j) qs
    (Fin.rev (⟨k, by omega⟩ : Fin (k + 1 + j)))
  have hrevrev : ((Fin.rev (Fin.rev (⟨k, by omega⟩ : Fin (k + 1 + j)))) : ℕ)
      = k := by
    first
      | (rw [Fin.rev_rev])
      | (rw [Fin.val_rev, Fin.val_rev]; omega)
      | simp
  rw [hrevrev] at h
  exact h

/-- lamAt is antitone in the dimension parameter. -/
theorem lamAt_antitone (qs : Finset ℕ) (k : ℕ) : Antitone (lamAt qs k) := by
  apply antitone_nat_of_succ_le
  intro j
  unfold lamAt
  have hle : k + 1 + j ≤ k + 1 + (j + 1) := by omega
  have h := galerkinEigenvalues_dim_mono (n := k + 1 + j) (m := k + 1 + (j + 1))
    qs hle (⟨k, by omega⟩ : Fin (k + 1 + j))
  have hcast : Fin.castLE hle (⟨k, by omega⟩ : Fin (k + 1 + j))
      = (⟨k, by omega⟩ : Fin (k + 1 + (j + 1))) := by
    apply Fin.eq_of_val_eq
    first
      | simp [Fin.val_castLE]
      | rfl
  rw [hcast] at h
  exact h

/-- lamAt is bounded below (range form). -/
theorem lamAt_bddBelow (qs : Finset ℕ) (k : ℕ) :
    BddBelow (Set.range (lamAt qs k)) := by
  refine ⟨Real.pi ^ 2 * ((k : ℝ) + 1) ^ 2 - SupVConst, ?_⟩
  rintro x ⟨j, rfl⟩
  exact lamAt_floor qs k j

/-- **THE LIMITING SPECTRUM** at fixed codes. -/
def lamInf (qs : Finset ℕ) (k : ℕ) : ℝ :=
  ⨅ j, lamAt qs k j

/-- **Convergence to the limiting spectrum.** -/
theorem lamAt_tendsto_lamInf (qs : Finset ℕ) (k : ℕ) :
    Tendsto (lamAt qs k) atTop (nhds (lamInf qs k)) :=
  tendsto_atTop_ciInf (lamAt_antitone qs k) (lamAt_bddBelow qs k)

/-- The limit inherits the concrete Weyl floor. -/
theorem lamInf_floor (qs : Finset ℕ) (k : ℕ) :
    Real.pi ^ 2 * ((k : ℝ) + 1) ^ 2 - SupVConst ≤ lamInf qs k := by
  unfold lamInf
  apply le_ciInf
  intro j
  exact lamAt_floor qs k j

/-- The SHIFTED limit has full free Weyl growth with constant pi^2 --
the DiscreteResolventModel growth hypothesis, verbatim shape. -/
theorem lamInf_shifted_growth (qs : Finset ℕ) (k : ℕ) :
    Real.pi ^ 2 * (k : ℝ) ^ 2 ≤ lamInf qs k + SupVConst := by
  have h := lamInf_floor qs k
  have hsq : Real.pi ^ 2 * (k : ℝ) ^ 2
      ≤ Real.pi ^ 2 * ((k : ℝ) + 1) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg Real.pi)
    have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith
  linarith

/-- The SHIFTED limit is nonnegative (from the banked uniform eigenvalue
floor, transported through the limit). -/
theorem lamInf_shifted_nonneg (qs : Finset ℕ) (k : ℕ) :
    0 ≤ lamInf qs k + SupVConst := by
  have h := lamInf_floor qs k
  have hsq : (0:ℝ) ≤ Real.pi ^ 2 * ((k : ℝ) + 1) ^ 2 := by positivity
  linarith

#print axioms lamAt_floor
#print axioms lamAt_antitone
#print axioms lamAt_tendsto_lamInf
#print axioms lamInf_floor
#print axioms lamInf_shifted_growth
#print axioms lamInf_shifted_nonneg

end

end RHFormalization
