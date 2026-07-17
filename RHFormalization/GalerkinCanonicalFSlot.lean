import RHFormalization.GalerkinSpikeLaplaceBridge
import RHFormalization.FinitePerturbedSpectrum
import RHFormalization.GalerkinFStageForwardGate
import Mathlib

/-!
# Canonical F-slot objects — BRICK 5 of the canonical-F route
SENTINEL: canonical-fslot-v1

ROUTE CARD
1. Target: the displacement-paired PERTURBED transform — the finite analogue
   of the manuscript's Θ^can one-letter channel on the genuine operator
   `H = K + V`. Eigen-sum form: `Σᵢ ⟨eᵢ, T_a eᵢ⟩ / (s + 1/4 + λᵢ)` in the
   perturbed eigenbasis (= Tr((H+s+1/4)⁻¹·T_a), basis-free, later brick).
2. DESIGN DECISION (on record): the canonical B-package on the F-side is
   `decodedOneLetterTransform` — the FINITE object — so `R_can := F^can −
   one-letter` is the Duhamel remainder by construction; all contact with
   `B_stage` goes through the banked lock (`(1/2)·B_stage − BcorrWin`) and
   the explicit finite-N defect. No hidden normalization.
3. This brick: definitions + N-free entry bound transfer only. Holomorphy
   (poles ⊂ (−∞,−1/4], Ω-clean) and the V=0 free-agreement identity are the
   next two bricks, written against exact names.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- Complexified compressed translation matrix. -/
def galerkinTC (L a : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ((galerkinT (N := N) L a i j : ℝ) : ℂ)

/-- Entry bound transfers: `‖galerkinTC‖ ≤ 2` entrywise, N-free. -/
theorem galerkinTC_entry_norm_le (L a : ℝ) (hL : 0 < L) (i j : Fin N) :
    ‖galerkinTC (N := N) L a i j‖ ≤ 2 := by
  unfold galerkinTC
  first
    | (rw [Complex.norm_ofReal]; exact galerkinT_entry_abs_le L a hL i j)
    | (rw [Complex.norm_real]; exact galerkinT_entry_abs_le L a hL i j)
    | (simpa using galerkinT_entry_abs_le L a hL i j)

/-- **Paired eigen-coefficient**: the diagonal matrix element of the paired
observable `T` in the perturbed eigenbasis of `H = diagonal μ + V`. -/
def pairedEigenCoeff (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (T : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : ℂ :=
  inner ℂ
    (((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank) i)
    ((Matrix.toEuclideanLin T)
      (((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank) i))

/-- **Paired perturbed spike transform**: the displacement-paired resolvent
trace in eigen-sum form — `Σᵢ ⟨eᵢ, T eᵢ⟩ / (s + 1/4 + λᵢ)`. At `V = 0` and
`μ = galerkinLam` this agrees with `galerkinSpikeTransform` (next-brick
identity, via basis-independence of `Tr(f(H)·T)`). -/
def pairedPerturbedSpikeTransform (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (T : Matrix (Fin N) (Fin N) ℂ) (s : ℂ) : ℂ :=
  ∑ i : Fin N,
    pairedEigenCoeff μ hV T i *
      (1 / (s + (1 / 4 : ℂ) + ((perturbedEigenvalues μ hV i : ℝ) : ℂ)))

/-- **The canonical one-letter F-side object at the genuine Galerkin stage**:
density-normalized, decoded physical centers, paired against the compressed
translation at each active prime-power displacement. This is the finite
analogue of the manuscript's `P^can_{L,R}` transform ON the perturbed
operator. -/
def galerkinCanonicalOneLetterF
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (R : ℝ) (s : ℂ) : ℂ :=
  ((1 / (2 * L) : ℝ) : ℂ) *
    ∑ q ∈ activePrimePowerPairsCenterBelow R,
      q.weightC *
        pairedPerturbedSpikeTransform (N := N)
          (galerkinFreeMu N L)
          (galerkinVC_isHermitian (N := N) δ qs w L)
          (galerkinTC (N := N) L q.center) s

/-- Unfold lemma. -/
theorem galerkinCanonicalOneLetterF_eq
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L R : ℝ) (s : ℂ) :
    galerkinCanonicalOneLetterF (N := N) δ qs w L R s
      = ((1 / (2 * L) : ℝ) : ℂ) *
          ∑ q ∈ activePrimePowerPairsCenterBelow R,
            q.weightC *
              pairedPerturbedSpikeTransform (N := N)
                (galerkinFreeMu N L)
                (galerkinVC_isHermitian (N := N) δ qs w L)
                (galerkinTC (N := N) L q.center) s := rfl

/-- **The canonical remainder ON the F-side** (per the design decision): the
paired perturbed one-letter object minus the FREE decoded one-letter
transform — the Duhamel remainder of the displacement channel, by
construction. All arithmetic contact goes through the banked lock. -/
def galerkinCanonicalRemainder
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L R : ℝ) (s : ℂ) : ℂ :=
  galerkinCanonicalOneLetterF (N := N) δ qs w L R s
    - decodedOneLetterTransform (N := N)
        (fun m => galerkinLam L (m : ℕ))
        (activePrimePowerPairsCenterBelow R) L s

theorem galerkinCanonicalRemainder_def
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L R : ℝ) (s : ℂ) :
    galerkinCanonicalOneLetterF (N := N) δ qs w L R s
      = decodedOneLetterTransform (N := N)
          (fun m => galerkinLam L (m : ℕ))
          (activePrimePowerPairsCenterBelow R) L s
        + galerkinCanonicalRemainder (N := N) δ qs w L R s := by
  unfold galerkinCanonicalRemainder
  ring

#print axioms galerkinTC
#print axioms galerkinTC_entry_norm_le
#print axioms pairedEigenCoeff
#print axioms pairedPerturbedSpikeTransform
#print axioms galerkinCanonicalOneLetterF
#print axioms galerkinCanonicalOneLetterF_eq
#print axioms galerkinCanonicalRemainder
#print axioms galerkinCanonicalRemainder_def

end

end RHFormalization
