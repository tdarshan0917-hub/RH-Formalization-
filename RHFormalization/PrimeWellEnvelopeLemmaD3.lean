import RHFormalization.PrimeWellEnvelopeLemmaD2

/-!
# Prime-well envelope (DQ1), Lemma D.3: the per-term distance bound
-/

namespace RHFormalization

open Real Filter Asymptotics

/-- The squared-distance bound: for `k ≠ m` (nearest integer to `c/log2`),
`(log2)²·(k-m)²/4 ≤ (k log2 - c)²`. -/
theorem latticeDist_sq_ge (c : ℝ) (k : ℕ) (m : ℤ) (hm : m = round (c / Real.log 2))
    (hkm : (k : ℤ) ≠ m) :
    (Real.log 2)^2 * (((k : ℤ) - m : ℝ))^2 / 4 ≤ ((k : ℝ) * Real.log 2 - c)^2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hround : |c / Real.log 2 - (m : ℝ)| ≤ 1/2 := by
    rw [hm]; exact abs_sub_round (c / Real.log 2)
  have hround' : -(1/2) ≤ c / Real.log 2 - (m : ℝ) ∧ c / Real.log 2 - (m : ℝ) ≤ 1/2 :=
    abs_le.mp hround
  have habs : (1 : ℝ) ≤ |(((k : ℤ) - m : ℝ))| := by
    have hz : (1 : ℤ) ≤ |(k : ℤ) - m| := Int.one_le_abs (sub_ne_zero.mpr hkm)
    have : ((1:ℤ):ℝ) ≤ ((|(k : ℤ) - m| : ℤ) : ℝ) := by exact_mod_cast hz
    rwa [Int.cast_abs, Int.cast_one, Int.cast_sub, Int.cast_natCast] at this
  have hone_sq : (1 : ℝ) ≤ (((k : ℤ) - m : ℝ))^2 := by
    nlinarith [sq_abs (((k : ℤ) - m : ℝ)), habs]
  have hfactor : (k : ℝ) * Real.log 2 - c = Real.log 2 * ((k : ℝ) - c / Real.log 2) := by
    field_simp
  rw [hfactor, mul_pow, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  set D : ℝ := ((k : ℤ) - m : ℝ) with hD
  set e : ℝ := c / Real.log 2 - (m : ℝ) with he
  have hkc : (k : ℝ) - c / Real.log 2 = D - e := by rw [hD, he]; push_cast; ring
  rw [hkc]
  have he_abs : |e| ≤ 1/2 := abs_le.mpr ⟨hround'.1, hround'.2⟩
  have hDe : |D| - 1/2 ≤ |D - e| := by
    have h := abs_sub_abs_le_abs_sub D e
    linarith [he_abs]
  have hhalf : |D| / 2 ≤ |D - e| := by linarith [habs]
  have hsq : (|D|/2)^2 ≤ |D - e|^2 := by
    apply sq_le_sq' _ hhalf
    linarith [abs_nonneg (D - e)]
  calc D^2 / 4 = (|D|/2)^2 := by rw [div_pow, sq_abs]; ring
    _ ≤ |D - e|^2 := hsq
    _ = (D - e)^2 := sq_abs _

/-- **Per-term bound.** For `k ≠ m`, the lattice-Gaussian term is `≤ gaussTailW α |k-m|`. -/
theorem latticeTerm_le_gaussTailW (α c : ℝ) (hα : 0 < α) (k : ℕ) (m : ℤ)
    (hm : m = round (c / Real.log 2)) (hkm : (k : ℤ) ≠ m) :
    Real.exp (-((k : ℝ) * Real.log 2 - c)^2 / (2 * α))
      ≤ gaussTailW α ((k : ℤ) - m).natAbs := by
  unfold gaussTailW
  apply Real.exp_le_exp.mpr
  have hcast : (((((k : ℤ) - m).natAbs : ℕ) : ℝ))^2 = (((k : ℤ) - m : ℝ))^2 := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]
    push_cast; ring
  rw [hcast]
  have hkey := latticeDist_sq_ge c k m hm hkm
  have hgoal : Real.log 2 ^ 2 * (((k:ℤ) - m : ℝ))^2 / (8 * α)
      ≤ ((k:ℝ) * Real.log 2 - c)^2 / (2 * α) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hkey, hα]
  calc -((k : ℝ) * Real.log 2 - c)^2 / (2 * α)
      = -(((k : ℝ) * Real.log 2 - c)^2 / (2 * α)) := by ring
    _ ≤ -(Real.log 2 ^ 2 * (((k:ℤ) - m : ℝ))^2 / (8 * α)) := by linarith [hgoal]
    _ = -Real.log 2 ^ 2 * (((k:ℤ) - m : ℝ))^2 / (8 * α) := by ring

#print axioms latticeDist_sq_ge
#print axioms latticeTerm_le_gaussTailW

end RHFormalization
