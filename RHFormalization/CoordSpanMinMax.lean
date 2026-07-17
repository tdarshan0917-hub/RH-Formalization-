/-
CoordSpanMinMax.lean

THE DIAGONAL IDENTIFICATION: Mathlib's sorted (decreasing) spectral
enumeration of a diagonal operator with monotone-increasing entries is the
reversed entry sequence: freeEigenvalues mu k = mu (Fin.rev k).

Route: two generic Courant-Fischer halves (a (k+1)-dim subspace where the
Rayleigh form is >= c forces lambda_k >= c; an (n-k)-dim subspace where it
is <= c forces lambda_k <= c), mirrored from the banked MinMaxBrick7
intersection argument, applied to coordinate spans where the diagonal form
is explicit. Consumed by Front F: converts Weyl-at-SupVConst into concrete
per-index growth of the genuine galerkin spectrum.
-/
import RHFormalization.MinMaxBrick7
import RHFormalization.PerturbedEigenvalueWeyl
import RHFormalization.GalerkinOpNonnegDischarge
import RHFormalization.GalerkinStageSequence

namespace RHFormalization

noncomputable section

open Complex

section Generic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {n : ℕ} {T : E →ₗ[𝕜] E}

/-- **Lower Courant-Fischer via a test subspace.** If some subspace of
dimension at least k+1 has Rayleigh form bounded below by c, then the k-th
sorted eigenvalue is at least c. -/
theorem eigenvalues_ge_of_rayleigh_on_subspace (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (k : Fin n) (U : Submodule 𝕜 E) (c : ℝ)
    (hdim : (k : ℕ) + 1 ≤ Module.finrank 𝕜 U)
    (hc : ∀ x ∈ U, c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 x (T x))) :
    c ≤ hT.eigenvalues hn k := by
  set W := eigenSpan hT hn (Finset.univ.filter (fun i : Fin n => k ≤ i)) with hW
  have hdimW : Module.finrank 𝕜 W = n - (k : ℕ) := by
    rw [hW, finrank_eigenSpan, card_filter_ge]
  have hkn : (k : ℕ) < n := k.2
  have hgt : Module.finrank 𝕜 E < Module.finrank 𝕜 U + Module.finrank 𝕜 W := by
    rw [hn, hdimW]; omega
  have hne := inf_ne_bot_of_finrank_add_gt U W hgt
  obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Submodule.mem_inf] at hxmem
  obtain ⟨hxU, hxW⟩ := hxmem
  have hxnorm : (0:ℝ) < ‖x‖ ^ 2 := by positivity
  have hup : RCLike.re (inner 𝕜 x (T x)) ≤ (hT.eigenvalues hn k) * ‖x‖ ^ 2 := by
    apply rayleigh_le_on_bot_eigenspace hT hn k
    intro j hj
    apply inner_eq_zero_of_mem_eigenSpan hT hn hxW
    simp; omega
  have hchain : c * ‖x‖ ^ 2 ≤ (hT.eigenvalues hn k) * ‖x‖ ^ 2 :=
    le_trans (hc x hxU) hup
  exact le_of_mul_le_mul_right hchain hxnorm

/-- **Upper Courant-Fischer via a test subspace.** If some subspace of
dimension at least n-k has Rayleigh form bounded above by c, then the k-th
sorted eigenvalue is at most c. -/
theorem eigenvalues_le_of_rayleigh_on_subspace (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (k : Fin n) (W : Submodule 𝕜 E) (c : ℝ)
    (hdim : n - (k : ℕ) ≤ Module.finrank 𝕜 W)
    (hc : ∀ x ∈ W, RCLike.re (inner 𝕜 x (T x)) ≤ c * ‖x‖ ^ 2) :
    hT.eigenvalues hn k ≤ c := by
  set U := eigenSpan hT hn (Finset.univ.filter (fun i : Fin n => i ≤ k)) with hU
  have hdimU : Module.finrank 𝕜 U = (k : ℕ) + 1 := by
    rw [hU, finrank_eigenSpan, card_filter_le]
  have hkn : (k : ℕ) < n := k.2
  have hgt : Module.finrank 𝕜 E < Module.finrank 𝕜 U + Module.finrank 𝕜 W := by
    rw [hn, hdimU]; omega
  have hne := inf_ne_bot_of_finrank_add_gt U W hgt
  obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Submodule.mem_inf] at hxmem
  obtain ⟨hxU, hxW⟩ := hxmem
  have hxnorm : (0:ℝ) < ‖x‖ ^ 2 := by positivity
  have hlow : (hT.eigenvalues hn k) * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 x (T x)) := by
    apply rayleigh_ge_on_top_eigenspace hT hn k
    intro j hj
    apply inner_eq_zero_of_mem_eigenSpan hT hn hxU
    simp; omega
  have hchain : (hT.eigenvalues hn k) * ‖x‖ ^ 2 ≤ c * ‖x‖ ^ 2 :=
    le_trans hlow (hc x hxW)
  exact le_of_mul_le_mul_right hchain hxnorm

end Generic

section Coord

variable {N : ℕ}

/-- The coordinate subspace spanned by the standard basis vectors indexed
by a finset of coordinates. -/
def coordSpan (s : Finset (Fin N)) : Submodule ℂ (EuclideanSpace ℂ (Fin N)) :=
  Submodule.span ℂ (Set.range (fun i : s => EuclideanSpace.single (i : Fin N) (1:ℂ)))

/-- The coordinate span over `s` has dimension exactly `s.card`. -/
theorem finrank_coordSpan (s : Finset (Fin N)) :
    Module.finrank ℂ (coordSpan (N := N) s) = s.card := by
  have hON : Orthonormal ℂ (fun i : Fin N => EuclideanSpace.single i (1:ℂ)) := by
    first
      | exact EuclideanSpace.orthonormal_single
      | simpa using (EuclideanSpace.basisFun (Fin N) ℂ).orthonormal
  rw [coordSpan, finrank_span_eq_card]
  · simp
  · exact hON.linearIndependent.comp _ Subtype.val_injective

/-- A vector in `coordSpan s` is orthogonal to every standard basis vector
with index outside `s`. -/
theorem inner_single_eq_zero_of_mem_coordSpan {s : Finset (Fin N)}
    {x : EuclideanSpace ℂ (Fin N)} (hx : x ∈ coordSpan s)
    {j : Fin N} (hj : j ∉ s) :
    inner ℂ (EuclideanSpace.single j (1:ℂ)) x = 0 := by
  rw [coordSpan] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [EuclideanSpace.inner_single_left, map_one, one_mul,
        EuclideanSpace.single_apply]
      have hne : j ≠ (i : Fin N) := by rintro rfl; exact hj i.2
      rw [if_neg hne]
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_right, hy, hz, add_zero]
  | smul c y _ hy => rw [inner_smul_right, hy, mul_zero]

/-- Coordinates outside `s` vanish on `coordSpan s`. -/
theorem coord_eq_zero_of_mem_coordSpan {s : Finset (Fin N)}
    {x : EuclideanSpace ℂ (Fin N)} (hx : x ∈ coordSpan s)
    {j : Fin N} (hj : j ∉ s) :
    x j = 0 := by
  have h := inner_single_eq_zero_of_mem_coordSpan hx hj
  rwa [EuclideanSpace.inner_single_left, map_one, one_mul] at h

/-- On `coordSpan s`, the diagonal Rayleigh form is at least `c` when every
active entry is. -/
theorem freeDiag_rayleigh_ge_on_coordSpan (μ : Fin N → ℝ) (s : Finset (Fin N))
    (c : ℝ) (hc : ∀ j ∈ s, c ≤ μ j)
    {x : EuclideanSpace ℂ (Fin N)} (hx : x ∈ coordSpan s) :
    c * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ x (freeDiagOp μ x)) := by
  rw [freeDiagOp_form_eq_sum]
  have hnorm : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [hnorm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k ∈ s
  · exact mul_le_mul_of_nonneg_right (hc k hk) (sq_nonneg _)
  · rw [coord_eq_zero_of_mem_coordSpan hx hk]; simp

/-- On `coordSpan s`, the diagonal Rayleigh form is at most `c` when every
active entry is. -/
theorem freeDiag_rayleigh_le_on_coordSpan (μ : Fin N → ℝ) (s : Finset (Fin N))
    (c : ℝ) (hc : ∀ j ∈ s, μ j ≤ c)
    {x : EuclideanSpace ℂ (Fin N)} (hx : x ∈ coordSpan s) :
    RCLike.re (inner ℂ x (freeDiagOp μ x)) ≤ c * ‖x‖ ^ 2 := by
  rw [freeDiagOp_form_eq_sum]
  have hnorm : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [hnorm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k ∈ s
  · exact mul_le_mul_of_nonneg_right (hc k hk) (sq_nonneg _)
  · rw [coord_eq_zero_of_mem_coordSpan hx hk]; simp

/-- **THE DIAGONAL IDENTIFICATION.** For a monotone-increasing entry vector,
Mathlib's sorted (decreasing) spectral enumeration of the diagonal operator
is the reversed entry sequence. -/
theorem freeEigenvalues_eq_rev_of_monotone (μ : Fin N → ℝ) (hmono : Monotone μ)
    (k : Fin N) :
    freeEigenvalues μ k = μ (Fin.rev k) := by
  have hkN : (k : ℕ) < N := k.2
  have hrev : (Fin.rev k : ℕ) = N - 1 - (k : ℕ) := by
    first
      | (rw [Fin.val_rev]; omega)
      | simp [Fin.rev]
  unfold freeEigenvalues
  refine le_antisymm ?_ ?_
  · refine eigenvalues_le_of_rayleigh_on_subspace (freeDiagOp_isSymmetric μ)
      perturbedOp_finrank k
      (coordSpan (Finset.univ.filter (fun j : Fin N => j ≤ Fin.rev k)))
      (μ (Fin.rev k)) ?_ ?_
    · rw [finrank_coordSpan, card_filter_le]
      omega
    · intro x hx
      exact freeDiag_rayleigh_le_on_coordSpan μ _ _
        (fun j hj => hmono (Finset.mem_filter.mp hj).2) hx
  · refine eigenvalues_ge_of_rayleigh_on_subspace (freeDiagOp_isSymmetric μ)
      perturbedOp_finrank k
      (coordSpan (Finset.univ.filter (fun j : Fin N => Fin.rev k ≤ j)))
      (μ (Fin.rev k)) ?_ ?_
    · rw [finrank_coordSpan, card_filter_ge]
      omega
    · intro x hx
      exact freeDiag_rayleigh_ge_on_coordSpan μ _ _
        (fun j hj => hmono (Finset.mem_filter.mp hj).2) hx

/-- The free Dirichlet entry vector is monotone increasing. -/
theorem galerkinFreeMu_mono (L : ℝ) (hL : 0 < L) :
    Monotone (galerkinFreeMu N L) := by
  intro a b hab
  simp only [galerkinFreeMu]
  have hab0 : (a : ℕ) ≤ (b : ℕ) := by
    first
      | exact hab
      | exact Fin.le_def.mp hab
  have hab' : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := Nat.cast_le.mpr hab0
  have hbase : ((a : ℝ) + 1) * Real.pi / L ≤ ((b : ℝ) + 1) * Real.pi / L := by
    first
      | (gcongr; linarith [hab'])
      | (gcongr <;> linarith [hab', hL.le, Real.pi_pos.le])
  have h0 : (0:ℝ) ≤ ((a : ℝ) + 1) * Real.pi / L := by positivity
  first
    | exact pow_le_pow_left h0 hbase 2
    | exact pow_le_pow_left₀ h0 hbase 2
    | nlinarith [hbase, h0, mul_le_mul hbase hbase h0 (h0.trans hbase)]

/-- **Free Dirichlet spectrum, identified.** The k-th sorted eigenvalue of
the free diagonal is the (N-1-k)-th Dirichlet level. -/
theorem freeEigenvalues_galerkinFreeMu_eq (L : ℝ) (hL : 0 < L) (k : Fin N) :
    freeEigenvalues (galerkinFreeMu N L) k = galerkinFreeMu N L (Fin.rev k) :=
  freeEigenvalues_eq_rev_of_monotone _ (galerkinFreeMu_mono L hL) k

#print axioms eigenvalues_ge_of_rayleigh_on_subspace
#print axioms eigenvalues_le_of_rayleigh_on_subspace
#print axioms finrank_coordSpan
#print axioms coord_eq_zero_of_mem_coordSpan
#print axioms freeEigenvalues_eq_rev_of_monotone
#print axioms freeEigenvalues_galerkinFreeMu_eq

end Coord

end

end RHFormalization
