import RHFormalization.PrimeGraphResolventLimit
import Mathlib

/-!
# PrimeGraphContraction — PG-4: the prime-graph trace formula, unconditionally

For the quantum map `U(k) = diag(p^{ik}) · σ` with `σ` unitary and `Im k > 0`:
* each phase has `‖p^{ik}‖ = p^{-Im k} < 1`;
* in the L2 operator norm `‖U‖ ≤ ‖diag‖·‖σ‖ = max_p p^{-Im k} < 1`;
* hence `U^M → 0` and `1 - U` is invertible, so PG-3 applies with no hypothesis:
  `Tr(Λ Σ_{m<M} U^m) → Tr(Λ (1 - U)⁻¹)` — the smoothed level-density formula at `k = T + iε`.
-/

set_option autoImplicit false

namespace RHFormalization

open Matrix Filter Topology
open scoped BigOperators Matrix.Norms.L2Operator

/-- A diagonal contraction times a unitary is a strict contraction (L2 operator norm). -/
theorem graphMap_norm_lt_one {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (z : n → ℂ) (σ : Matrix n n ℂ) (hσ : σ ∈ unitary (Matrix n n ℂ))
    (hz : ∀ b, ‖z b‖ < 1) :
    ‖Matrix.diagonal z * σ‖ < 1 := by
  have hz' : ‖z‖ < 1 := (pi_norm_lt_iff one_pos).2 hz
  have hσ1 : ‖σ‖ = 1 := CStarRing.norm_of_mem_unitary hσ
  have hmul : ‖Matrix.diagonal z * σ‖ ≤ ‖Matrix.diagonal z‖ * ‖σ‖ := Matrix.l2_opNorm_mul _ _
  have hd : ‖Matrix.diagonal z‖ = ‖z‖ := Matrix.l2_opNorm_diagonal z
  rw [hd] at hmul
  first
    | (rw [hσ1, mul_one] at hmul; exact lt_of_le_of_lt hmul hz')
    | (simp only [hσ1, mul_one] at hmul; exact lt_of_le_of_lt hmul hz')
    | nlinarith [hmul, hz', hσ1, norm_nonneg z]

theorem graphMap_pow_tendsto_zero {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (z : n → ℂ) (σ : Matrix n n ℂ) (hσ : σ ∈ unitary (Matrix n n ℂ))
    (hz : ∀ b, ‖z b‖ < 1) :
    Tendsto (fun M : ℕ => (Matrix.diagonal z * σ) ^ M) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one (graphMap_norm_lt_one z σ hσ hz)

theorem graphMap_one_sub_isUnit_det {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (z : n → ℂ) (σ : Matrix n n ℂ) (hσ : σ ∈ unitary (Matrix n n ℂ))
    (hz : ∀ b, ‖z b‖ < 1) :
    IsUnit (1 - Matrix.diagonal z * σ).det := by
  have h := graphMap_norm_lt_one z σ hσ hz
  have hu : IsUnit (1 - Matrix.diagonal z * σ) := by
    first
      | exact (Units.oneSub _ h).isUnit
      | simpa using (Units.oneSub _ h).isUnit
  exact (Matrix.isUnit_iff_isUnit_det _).mp hu

/-- `‖p^{ik}‖ < 1` for a prime `p` when `Im k > 0`. -/
theorem primePhase_norm_lt_one {p : ℕ} (hp : p.Prime) {k : ℂ} (hk : 0 < k.im) :
    ‖(p : ℂ) ^ (Complex.I * k)‖ < 1 := by
  have hre : (Complex.I * k).re = -k.im := by simp [Complex.mul_re]
  first
    | rw [Complex.norm_natCast_cpow_of_pos hp.pos, hre]
    | rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (by rw [hre]; linarith), hre]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

/-- **PG-4 — the prime-graph trace formula, no extra hypothesis.** For bonds indexed by primes,
any unitary central scattering `σ`, and `Im k > 0`, the weighted orbit sums of
`U(k) = diag(p^{ik})·σ` converge to the resolvent trace `Tr(Λ (1 - U(k))⁻¹)`. -/
theorem primeGraph_trace_formula {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (pr : ι → ℕ) (hpr : ∀ b, (pr b).Prime) (σ : Matrix ι ι ℂ)
    (hσ : σ ∈ unitary (Matrix ι ι ℂ)) (Λ : Matrix ι ι ℂ) {k : ℂ} (hk : 0 < k.im) :
    Tendsto (fun M : ℕ => Matrix.trace (Λ * ∑ m ∈ Finset.range M,
        (Matrix.diagonal (fun b => ((pr b : ℕ) : ℂ) ^ (Complex.I * k)) * σ) ^ m)) atTop
      (𝓝 (Matrix.trace (Λ * (1 - Matrix.diagonal
        (fun b => ((pr b : ℕ) : ℂ) ^ (Complex.I * k)) * σ)⁻¹))) := by
  have hz : ∀ b, ‖((pr b : ℕ) : ℂ) ^ (Complex.I * k)‖ < 1 :=
    fun b => primePhase_norm_lt_one (hpr b) hk
  exact trace_orbit_sum_tendsto_resolvent Λ _
    (graphMap_one_sub_isUnit_det _ σ hσ hz) (graphMap_pow_tendsto_zero _ σ hσ hz)

#print axioms graphMap_norm_lt_one
#print axioms graphMap_one_sub_isUnit_det
#print axioms primePhase_norm_lt_one
#print axioms primeGraph_trace_formula

end RHFormalization
