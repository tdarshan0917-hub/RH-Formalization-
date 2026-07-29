import RHFormalization.CanonicalPrimePowerHeatKernelNatValueMajorantSummability

namespace RHFormalization

lemma geom_numerator_bound_natValue_probe
    (q : PrimePowerPair)
    (hp : 2 ≤ q.p)
    (hm : 0 < q.m) :
    (q.p : ℝ) * ((q.p : ℝ) + 1)^2 * (2 : ℝ)^q.m
      ≤ 8 * (q.natValue : ℝ)^3 := by
  have h :=
    geom_numerator_bound (p := q.p) (m := q.m) hp hm
  unfold PrimePowerPair.natValue

  have hpow :
      (q.p : ℝ) ^ (3 * q.m) =
        ((q.p : ℝ) ^ q.m) ^ 3 := by
    rw [Nat.mul_comm 3 q.m]
    rw [← pow_mul]

  rw [hpow] at h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

end RHFormalization
