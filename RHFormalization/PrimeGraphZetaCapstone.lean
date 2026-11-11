import RHFormalization.PrimeGraphZetaLimit
import Mathlib

/-!
# PrimeGraphZetaCapstone — PG-10: graph log-derivative → −ζ'/ζ when composite orbits vanish

Bonds = primes `≤ P` (`primeIdx P`), any scattering family `σ P`, `s = 1/2 - ix`, `Im x > 1/2`.
If `graphLogDeriv σ x P − (Euler part) → 0` (by PG-8: the composite-orbit term vanishes), then
`graphLogDeriv σ x P → −ζ'(s)/ζ(s)` (PG-9c).
-/

set_option autoImplicit false

namespace RHFormalization

open Filter Topology
open scoped BigOperators

abbrev primeIdx (P : ℕ) := {p : ℕ // p ∈ (Finset.range (P + 1)).filter Nat.Prime}

/-- `i · (log det(1 - U_P))'(x)` for the graph on the primes `≤ P`. -/
noncomputable def graphLogDeriv (σ : (P : ℕ) → Matrix (primeIdx P) (primeIdx P) ℂ)
    (x : ℂ) (P : ℕ) : ℂ :=
  Complex.I * (deriv (fun k => (1 - graphU (fun b : primeIdx P => (b : ℕ)) (σ P) k).det) x
    / (1 - graphU (fun b : primeIdx P => (b : ℕ)) (σ P) x).det)

/-- **PG-10 — capstone.** -/
theorem graph_logDeriv_tendsto_zeta (σ : (P : ℕ) → Matrix (primeIdx P) (primeIdx P) ℂ)
    (x : ℂ) (hx : 1/2 < x.im)
    (hcomp : Tendsto (fun P : ℕ => graphLogDeriv σ x P
        - ∑ b : primeIdx P, Complex.log ((b : ℕ) : ℂ) *
            (((b : ℕ) : ℂ) ^ (Complex.I * x - 1/2) /
              (1 - ((b : ℕ) : ℂ) ^ (Complex.I * x - 1/2)))) atTop (𝓝 0)) :
    Tendsto (graphLogDeriv σ x) atTop
      (𝓝 (-deriv riemannZeta (1/2 - Complex.I * x) / riemannZeta (1/2 - Complex.I * x))) := by
  have hre : (1/2 - Complex.I * x).re = 1/2 + x.im := by
    have h12 : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by
      first
        | (norm_num; done)
        | (push_cast; ring)
        | (simp; done)
    rw [h12, Complex.sub_re, Complex.ofReal_re]
    simp [Complex.mul_re]
    all_goals ring
  have hs : 1 < (1/2 - Complex.I * x).re := by rw [hre]; linarith
  have hE := graphEuler_tendsto_logDeriv_zeta hs
  have hlog : ∀ p : ℕ, Complex.log (p : ℂ) = (Real.log p : ℂ) := by
    intro p
    first
      | (rw [Complex.ofReal_log (Nat.cast_nonneg p), Complex.ofReal_natCast]; done)
      | (rw [Complex.ofReal_log (Nat.cast_nonneg p)]; norm_cast; done)
      | (simp [Complex.ofReal_log]; done)
      | exact (Complex.natCast_log).symm
  have heq : ∀ P : ℕ, (∑ b : primeIdx P, Complex.log ((b : ℕ) : ℂ) *
        (((b : ℕ) : ℂ) ^ (Complex.I * x - 1/2) / (1 - ((b : ℕ) : ℂ) ^ (Complex.I * x - 1/2))))
      = ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, (Real.log p : ℂ) *
          ((p : ℂ) ^ (-(1/2 - Complex.I * x)) / (1 - (p : ℂ) ^ (-(1/2 - Complex.I * x)))) := by
    intro P
    refine (Finset.sum_coe_sort ((Finset.range (P + 1)).filter Nat.Prime)
      (fun p : ℕ => Complex.log (p : ℂ) *
        ((p : ℂ) ^ (Complex.I * x - 1/2) / (1 - (p : ℂ) ^ (Complex.I * x - 1/2))))).trans ?_
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [neg_sub, hlog p]
  have hsum := hcomp.add hE
  rw [zero_add] at hsum
  refine hsum.congr (fun P => ?_)
  try beta_reduce
  rw [heq P]
  ring

#print axioms graph_logDeriv_tendsto_zeta

end RHFormalization
