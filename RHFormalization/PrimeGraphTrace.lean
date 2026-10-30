import Mathlib

/-!
# PrimeGraphTrace — PG-1: exact trace identities for the prime quantum graph

Prime star graph: one bond per prime p, length ½·log p; quantum map `U(k) = diag(p^{ik})·σ`;
level density `L/π + (1/π) Re Σ_{m≥1} Tr(Λ U^m)`, `Λ = diag(log p)`.
* `trace_diag_mul_pow_diag`: decoupled orbit trace = sum over single bonds;
* `primeGraph_trace_decoupled`: with `U = diag(p^s)` (self-amplitude p^{-1/2} at s = ik − ½) the m-th
  orbit trace is `Σ_p Λ(p^m)·(p^s)^m` — the m-th prime-power layer of the explicit formula;
* `cpow_ik_mul_cpow_neg_half`: `p^{ik}·p^{−1/2} = p^{ik−1/2}`;
* `trace_orbit_sum_truncated`: `Tr(Λ (Σ_{m<M} U^m)(1−U)) = Tr Λ − Tr(Λ U^M)`.
-/

set_option autoImplicit false

namespace RHFormalization

open Matrix
open scoped BigOperators

theorem trace_diag_mul_pow_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Λ z : ι → ℂ) (m : ℕ) :
    Matrix.trace (Matrix.diagonal Λ * (Matrix.diagonal z) ^ m)
      = ∑ b, Λ b * (z b) ^ m := by
  simp [Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Pi.pow_apply]

theorem cpow_ik_mul_cpow_neg_half {p : ℕ} (hp : p.Prime) (k : ℂ) :
    (p : ℂ) ^ (Complex.I * k) * (p : ℂ) ^ (-(1/2 : ℂ))
      = (p : ℂ) ^ (Complex.I * k - 1/2) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rw [← Complex.cpow_add _ _ hp0]
  all_goals (try congr 1)
  all_goals ring

/-- **PG-1**: decoupled prime graph: m-th orbit trace = `Σ_p Λ(p^m) (p^s)^m`. -/
theorem primeGraph_trace_decoupled {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pr : ι → ℕ) (hpr : ∀ b, (pr b).Prime) (s : ℂ) {m : ℕ} (hm : m ≠ 0) :
    Matrix.trace (Matrix.diagonal (fun b => ((Real.log (pr b) : ℝ) : ℂ)) *
        (Matrix.diagonal (fun b => ((pr b : ℕ) : ℂ) ^ s)) ^ m)
      = ∑ b, ((ArithmeticFunction.vonMangoldt ((pr b) ^ m) : ℝ) : ℂ)
          * (((pr b : ℕ) : ℂ) ^ s) ^ m := by
  rw [trace_diag_mul_pow_diag]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [ArithmeticFunction.vonMangoldt_apply_pow hm,
    ArithmeticFunction.vonMangoldt_apply_prime (hpr b)]

/-- **Finite orbit sum telescopes exactly** (resolvent identity behind the trace formula). -/
theorem trace_orbit_sum_truncated {n : Type*} [Fintype n] [DecidableEq n]
    (Λ U : Matrix n n ℂ) (M : ℕ) :
    Matrix.trace (Λ * (∑ m ∈ Finset.range M, U ^ m) * (1 - U))
      = Matrix.trace Λ - Matrix.trace (Λ * U ^ M) := by
  rw [mul_assoc, geom_sum_mul_neg, mul_sub, mul_one, Matrix.trace_sub]

#print axioms trace_diag_mul_pow_diag
#print axioms primeGraph_trace_decoupled
#print axioms trace_orbit_sum_truncated

end RHFormalization
