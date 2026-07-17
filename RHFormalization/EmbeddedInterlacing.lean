/-
EmbeddedInterlacing.lean

ONE-SIDED CAUCHY INTERLACING, generic form: if J embeds a small inner
product space isometrically into a big one and the big operator's Rayleigh
form restricted through J agrees with the small operator's form (the
compression relation -- e.g. a principal minor), then the k-th SMALLEST
eigenvalue of the big operator is at most the k-th smallest of the small
one. In Mathlib's sorted-decreasing enumeration, "k-th smallest" is index
Fin.rev k.

Consumed by Front F: at fixed potential code set, growing the Galerkin
dimension moves each (increasing-orientation) eigenvalue monotonically
DOWN; with the banked pi^2 floor this gives per-index limits.
-/
import RHFormalization.CoordSpanMinMax

namespace RHFormalization

noncomputable section

open RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {m n : ℕ} {T : E →ₗ[𝕜] E} {S : F →ₗ[𝕜] F}

/-- An inner-product-preserving map sends an orthonormal family to an
orthonormal family. -/
theorem orthonormal_comp_of_inner_preserving
    (J : F →ₗ[𝕜] E)
    (hJinner : ∀ x y : F, inner 𝕜 (J x) (J y) = inner 𝕜 x y)
    {ι : Type*} {v : ι → F} (hv : Orthonormal 𝕜 v) :
    Orthonormal 𝕜 (fun i => J (v i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [hJinner]
  rw [orthonormal_iff_ite] at hv
  exact hv i j

/-- **One-sided Cauchy interlacing through an isometric compression.**
If `J : F -> E` preserves inner products and `re <Jx, T(Jx)> = re <x, Sx>`
(the compression relation), then for every index `k` the k-th smallest
eigenvalue of `T` is at most the k-th smallest eigenvalue of `S`
(smallest = Fin.rev in Mathlib's decreasing enumeration). -/
theorem eigenvalues_rev_le_of_isometric_compression
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hm : Module.finrank 𝕜 E = m) (hn : Module.finrank 𝕜 F = n)
    (J : F →ₗ[𝕜] E)
    (hJinner : ∀ x y : F, inner 𝕜 (J x) (J y) = inner 𝕜 x y)
    (hJform : ∀ x : F,
      RCLike.re (inner 𝕜 (J x) (T (J x))) = RCLike.re (inner 𝕜 x (S x)))
    (h : n ≤ m) (k : Fin n) :
    hT.eigenvalues hm (Fin.rev (Fin.castLE h k))
      ≤ hS.eigenvalues hn (Fin.rev k) := by
  have hkn : (k : ℕ) < n := k.2
  have hrevk : ((Fin.rev k : Fin n) : ℕ) = n - 1 - (k : ℕ) := by
    first
      | (rw [Fin.val_rev]; omega)
      | simp [Fin.rev]
  have hcast : ((Fin.castLE h k : Fin m) : ℕ) = (k : ℕ) := by
    first
      | rw [Fin.coe_castLE]
      | simp [Fin.castLE]
  have hrevcast : ((Fin.rev (Fin.castLE h k) : Fin m) : ℕ) = m - 1 - (k : ℕ) := by
    first
      | (rw [Fin.val_rev, hcast]; omega)
      | (rw [Fin.val_rev]; omega)
      | (simp [Fin.rev]; omega)
  set c := hS.eigenvalues hn (Fin.rev k) with hcdef
  set s : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => Fin.rev k ≤ i) with hs
  have hONJ : Orthonormal 𝕜
      (fun i : Fin n => J ((hS.eigenvectorBasis hn) i)) :=
    orthonormal_comp_of_inner_preserving J hJinner
      (hS.eigenvectorBasis hn).orthonormal
  set W : Submodule 𝕜 E :=
    Submodule.span 𝕜
      (Set.range (fun i : s => J ((hS.eigenvectorBasis hn) i))) with hW
  have hfinW : Module.finrank 𝕜 W = s.card := by
    rw [hW, finrank_span_eq_card]
    · simp
    · exact hONJ.linearIndependent.comp _ Subtype.val_injective
  have hcards : s.card = n - ((Fin.rev k : Fin n) : ℕ) := by
    rw [hs]
    exact card_filter_ge (Fin.rev k)
  have hWmap : W = Submodule.map J (eigenSpan hS hn s) := by
    rw [hW]
    unfold eigenSpan
    rw [Submodule.map_span]
    congr 1
    first
      | exact Set.range_comp _ _
      | rw [Set.range_comp]
      | (ext x
         constructor
         · rintro ⟨i, rfl⟩
           exact ⟨_, ⟨i, rfl⟩, rfl⟩
         · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
           exact ⟨i, rfl⟩)
  have hnormsq : ∀ y : F, ‖J y‖ ^ 2 = ‖y‖ ^ 2 := by
    intro y
    have h1 : inner 𝕜 (J y) (J y) = inner 𝕜 y y := hJinner y y
    calc ‖J y‖ ^ 2
        = RCLike.re (inner 𝕜 (J y) (J y)) := (inner_self_eq_norm_sq _).symm
      _ = RCLike.re (inner 𝕜 y y) := by rw [h1]
      _ = ‖y‖ ^ 2 := inner_self_eq_norm_sq _
  have hcW : ∀ x ∈ W, RCLike.re (inner 𝕜 x (T x)) ≤ c * ‖x‖ ^ 2 := by
    intro x hx
    rw [hWmap] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hray : RCLike.re (inner 𝕜 y (S y)) ≤ c * ‖y‖ ^ 2 := by
      apply rayleigh_le_on_bot_eigenspace hS hn (Fin.rev k)
      intro j hj
      apply inner_eq_zero_of_mem_eigenSpan hS hn hy
      rw [hs]
      simp
      omega
    calc RCLike.re (inner 𝕜 (J y) (T (J y)))
        = RCLike.re (inner 𝕜 y (S y)) := hJform y
      _ ≤ c * ‖y‖ ^ 2 := hray
      _ = c * ‖J y‖ ^ 2 := by rw [hnormsq]
  refine eigenvalues_le_of_rayleigh_on_subspace hT hm
    (Fin.rev (Fin.castLE h k)) W c ?_ hcW
  rw [hfinW, hcards]
  first
    | omega
    | (rw [hrevcast, hrevk]; omega)

#print axioms orthonormal_comp_of_inner_preserving
#print axioms eigenvalues_rev_le_of_isometric_compression

end

end RHFormalization
