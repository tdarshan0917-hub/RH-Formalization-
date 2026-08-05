import RHFormalization.PerturbedFStageM2Split
import RHFormalization.PrimePotentialBumpSplit
import RHFormalization.GalerkinMatrices
import Mathlib

/-!
# SpikeSumPrimeReindex — the diagonal spike sum over prime centers

ROUTE CARD
1. Target: EXACT reindexing of the M2-split's one-letter term:
   `Σ_m V_mm·(s+λ_m)⁻² = Σ_{q∈qs} w(q)·primeSpikeResolventSq δ q L s`,
   where `primeSpikeResolventSq δ q L s :=
     (2/L)·Σ_m bumpMatrixElement δ q L (m+1)(m+1)·(s+λ_m)⁻²`
   — the per-prime squared-resolvent transform, THE profile shape that the
   D.SPIKE-TRANSFER layer must reconcile with seamArithmeticSum's kernel.
   Pure finite double-sum swap over VmatrixElement_eq_sum_bumps.
2. Raw B on Ω? NO. B−M bare Prop? NO — finite algebra, no bound.
3. Consumer: the D.SPIKE-TRANSFER reconciliation (per-prime transform vs
   e^{−a√(s+1/4)} kernel, window corrections into Bcorr) → h_expansion →
   hSC → HtailExists. This brick EXPOSES the profile shape; the fail-fast
   test happens at its consumer.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

variable {N : ℕ}

/-- **The per-prime squared-resolvent spike transform** — the J-class
profile shape produced by the operator one-letter extraction at center
`log q`. -/
def primeSpikeResolventSq (δ : ℝ) (q : ℕ) (L : ℝ) (s : ℂ) : ℂ :=
  ((2 / L : ℝ) : ℂ) *
    ∑ m : Fin N,
      ((bumpMatrixElement δ q L ((m : ℕ) + 1) ((m : ℕ) + 1) : ℝ) : ℂ) *
        ((s + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)) ^ 2)⁻¹

/-- **THE REINDEXING**: the M2-split one-letter term is the prime-indexed
sum of per-prime spike transforms (exact, every s). -/
theorem spikeSum_eq_prime_sum
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (s : ℂ) :
    (∑ m : Fin N,
        ((galerkinV (N := N) δ qs w L m m : ℝ) : ℂ)
          * ((s + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)) ^ 2)⁻¹)
      = ∑ q ∈ qs, ((w q : ℝ) : ℂ) *
          primeSpikeResolventSq (N := N) δ q L s := by
  unfold primeSpikeResolventSq
  -- expand V_mm over bumps
  have hV : ∀ m : Fin N,
      ((galerkinV (N := N) δ qs w L m m : ℝ) : ℂ)
        = ((2 / L : ℝ) : ℂ) * ∑ q ∈ qs, ((w q : ℝ) : ℂ) *
            ((bumpMatrixElement δ q L ((m : ℕ) + 1) ((m : ℕ) + 1) : ℝ) : ℂ) := by
    intro m
    rw [galerkinV_apply, VmatrixElement_eq_sum_bumps]
    push_cast
    rfl
  calc (∑ m : Fin N,
        ((galerkinV (N := N) δ qs w L m m : ℝ) : ℂ)
          * ((s + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)) ^ 2)⁻¹)
      = ∑ m : Fin N, ∑ q ∈ qs,
          ((2 / L : ℝ) : ℂ) * (((w q : ℝ) : ℂ) *
            ((bumpMatrixElement δ q L ((m : ℕ) + 1) ((m : ℕ) + 1) : ℝ) : ℂ))
            * ((s + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)) ^ 2)⁻¹ := by
        apply Finset.sum_congr rfl
        intro m _
        rw [hV m, Finset.mul_sum, Finset.sum_mul]
    _ = ∑ q ∈ qs, ∑ m : Fin N,
          ((2 / L : ℝ) : ℂ) * (((w q : ℝ) : ℂ) *
            ((bumpMatrixElement δ q L ((m : ℕ) + 1) ((m : ℕ) + 1) : ℝ) : ℂ))
            * ((s + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)) ^ 2)⁻¹ := by
        rw [Finset.sum_comm]
    _ = ∑ q ∈ qs, ((w q : ℝ) : ℂ) *
          (((2 / L : ℝ) : ℂ) *
            ∑ m : Fin N,
              ((bumpMatrixElement δ q L ((m : ℕ) + 1) ((m : ℕ) + 1) : ℝ) : ℂ) *
                ((s + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)) ^ 2)⁻¹) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring

/-- **The M2 split, prime-indexed** (composition with the banked split). -/
theorem perturbedFStage_M2_split_prime
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (s : ℂ) (hs : 0 < s.re)
    (hpos : ∀ i, 0 ≤ perturbedEigenvalues (galerkinFreeMu N L)
        (galerkinVC_isHermitian (N := N) δ qs w L) i)
    (hlam : ∀ m : Fin N, 0 ≤ galerkinLam L (m : ℕ)) :
    perturbedFStage (galerkinFreeMu N L)
        (galerkinVC_isHermitian (N := N) δ qs w L) s
      = FstageFinite (fun m : Fin N => galerkinLam L (m : ℕ)) s
        - (∑ q ∈ qs, ((w q : ℝ) : ℂ) *
            primeSpikeResolventSq (N := N) δ q L s)
        + spikeE2Transform (N := N) δ qs w L s := by
  rw [perturbedFStage_M2_split δ qs w L s hs hpos hlam,
    spikeSum_eq_prime_sum]

#print axioms primeSpikeResolventSq
#print axioms spikeSum_eq_prime_sum
#print axioms perturbedFStage_M2_split_prime

end

end RHFormalization
