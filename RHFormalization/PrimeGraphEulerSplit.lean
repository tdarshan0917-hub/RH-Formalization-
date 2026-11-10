import RHFormalization.PrimeGraphTraceFormula
import Mathlib

/-!
# PrimeGraphEulerSplit — PG-8: graph log-derivative = truncated Euler log-derivative + composite orbits

With `σ_bb = p_b^{-1/2}` the graph map's diagonal is `U_bb = p_b^{ix-1/2} = p_b^{-s}`, `s = 1/2 - ix`
(`graphU_diag_entry`). Single-bond orbits then sum to `log p · p^{-s}/(1-p^{-s})`, the p-th term of
the truncated `-ζ'/ζ(s)`. `primeGraph_composite_orbit_limit`: the composite-orbit sum converges, and
`i·(log det(1-U))' = Σ_p log p · p^{-s}/(1-p^{-s}) + lim (composite orbits)`.
-/

set_option autoImplicit false

namespace RHFormalization

open Matrix Filter Topology
open scoped BigOperators

/-- `‖p^{ix-1/2}‖ < 1` for a prime `p` when `Im x > 0`. -/
theorem primePhaseHalf_norm_lt_one {p : ℕ} (hp : p.Prime) {x : ℂ} (hx : 0 < x.im) :
    ‖(p : ℂ) ^ (Complex.I * x - 1/2)‖ < 1 := by
  have h12 : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by
    first
      | (norm_num; done)
      | (push_cast; ring)
      | (simp; done)
  have hre : (Complex.I * x - 1/2).re = -x.im - 1/2 := by
    rw [h12, Complex.sub_re, Complex.ofReal_re]
    simp [Complex.mul_re]
  first
    | rw [Complex.norm_natCast_cpow_of_pos hp.pos, hre]
    | rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (by rw [hre]; linarith), hre]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

/-- With self-scattering `σ_bb = p^{-1/2}`, the graph map's diagonal entry is `p^{ix-1/2}`. -/
theorem graphU_diag_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pr : ι → ℕ) (hpr : ∀ b, (pr b).Prime) (σ : Matrix ι ι ℂ)
    (hdiag : ∀ b, σ b b = ((pr b : ℕ) : ℂ) ^ (-(1/2 : ℂ))) (x : ℂ) (b : ι) :
    graphU pr σ x b b = ((pr b : ℕ) : ℂ) ^ (Complex.I * x - 1/2) := by
  rw [graphU, Matrix.diagonal_mul, hdiag]
  exact cpow_ik_mul_cpow_neg_half (hpr b) x

/-- **PG-8 — Euler split.** The composite-orbit sum
`Σ_{m<M} [Tr(Λ U^{m+1}) - Σ_p log p · (p^{-s})^{m+1}]` converges to
`i·(log det(1-U))' - Σ_p log p · p^{-s}/(1-p^{-s})`, `s = 1/2 - ix`. -/
theorem primeGraph_composite_orbit_limit {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (pr : ι → ℕ) (hpr : ∀ b, (pr b).Prime) (σ : Matrix ι ι ℂ)
    (hσ : σ ∈ unitary (Matrix ι ι ℂ)) (x : ℂ) (hx : 0 < x.im) :
    Tendsto (fun M : ℕ => ∑ m ∈ Finset.range M,
        ((Matrix.diagonal (fun b => Complex.log ((pr b : ℕ) : ℂ)) * graphU pr σ x ^ (m + 1)).trace
          - ∑ b, Complex.log ((pr b : ℕ) : ℂ) *
              (((pr b : ℕ) : ℂ) ^ (Complex.I * x - 1/2)) ^ (m + 1)))
      atTop
      (𝓝 (Complex.I * (deriv (fun k => (1 - graphU pr σ k).det) x / (1 - graphU pr σ x).det)
        - ∑ b, Complex.log ((pr b : ℕ) : ℂ) *
            (((pr b : ℕ) : ℂ) ^ (Complex.I * x - 1/2) /
              (1 - ((pr b : ℕ) : ℂ) ^ (Complex.I * x - 1/2))))) := by
  have h1 := primeGraph_logDeriv_eq_orbit_sum pr hpr σ hσ x hx
  have h2 : Tendsto (fun M : ℕ => ∑ m ∈ Finset.range M, ∑ b, Complex.log ((pr b : ℕ) : ℂ) *
        (((pr b : ℕ) : ℂ) ^ (Complex.I * x - 1/2)) ^ (m + 1)) atTop
      (𝓝 (∑ b, Complex.log ((pr b : ℕ) : ℂ) *
        (((pr b : ℕ) : ℂ) ^ (Complex.I * x - 1/2) /
          (1 - ((pr b : ℕ) : ℂ) ^ (Complex.I * x - 1/2))))) := by
    have hswap : (fun M : ℕ => ∑ m ∈ Finset.range M, ∑ b, Complex.log ((pr b : ℕ) : ℂ) *
          (((pr b : ℕ) : ℂ) ^ (Complex.I * x - 1/2)) ^ (m + 1))
        = fun M : ℕ => ∑ b, Complex.log ((pr b : ℕ) : ℂ) *
            (((pr b : ℕ) : ℂ) ^ (Complex.I * x - 1/2) *
              ∑ m ∈ Finset.range M, (((pr b : ℕ) : ℂ) ^ (Complex.I * x - 1/2)) ^ m) := by
      funext M
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [pow_succ']
    rw [hswap]
    refine tendsto_finset_sum _ (fun b _ => ?_)
    have hw := primePhaseHalf_norm_lt_one (hpr b) hx
    have hg := (hasSum_geometric_of_norm_lt_one hw).tendsto_sum_nat
    have hc := (hg.const_mul (((pr b : ℕ) : ℂ) ^ (Complex.I * x - 1/2))).const_mul
      (Complex.log ((pr b : ℕ) : ℂ))
    rw [div_eq_mul_inv]
    exact hc
  refine (h1.sub h2).congr (fun M => ?_)
  rw [Finset.sum_sub_distrib]

#print axioms primePhaseHalf_norm_lt_one
#print axioms graphU_diag_entry
#print axioms primeGraph_composite_orbit_limit

end RHFormalization
