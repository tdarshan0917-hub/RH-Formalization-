import RHFormalization.MinMaxBrick7
import RHFormalization.MinMaxBrick8
import RHFormalization.MinMaxBrick9
import RHFormalization.MinMaxBrick10

/-!
# Courant–Fischer Min-Max and Weyl Perturbation in Lean — Capstone

A self-contained formalization of indexed Courant–Fischer eigenvalue monotonicity AND
Weyl's eigenvalue perturbation inequality for symmetric operators on finite-dimensional
inner product spaces. Mathlib provides only the top/bottom Rayleigh extremes
(`hasEigenvalue_iSup/iInf_of_finiteDimensional`); the indexed min-max comparison and the
Weyl bound are built here from the spectral theorem upward.

All theorems are axiom-clean: [propext, Classical.choice, Quot.sound], no sorryAx.

## Spectral computation
* `reInner_eigenvectorBasis`      — Rayleigh on an eigenvector equals its eigenvalue
* `inner_eigenvectorBasis_apply`  — diagonal action ⟨e_i, T x⟩ = λ_i ⟨e_i, x⟩
* `inner_self_eq_sum_eigenvalues` — spectral expansion of ⟨x, T x⟩
* `reInner_eq_sum`                — Rayleigh as a real eigenvalue-weighted sum
* `sum_norm_sq_inner`             — Parseval in the eigenbasis

## Variational halves (Courant–Fischer)
* `rayleigh_ge_on_top_eigenspace` — top (k+1) eigenspace ⇒ Rayleigh ≥ λ_k‖x‖²
* `rayleigh_le_on_bot_eigenspace` — bottom (n−k) eigenspace ⇒ Rayleigh ≤ λ_k‖x‖²

## Dimension machinery
* `inf_ne_bot_of_finrank_add_gt`  — dims summing > n ⇒ nontrivial intersection
* `eigenSpan`, `finrank_eigenSpan`— eigenvector spans and their dimension
* `inner_eq_zero_of_mem_eigenSpan`— membership ⇒ orthogonality to outside eigenvectors

## Eigenvalue monotonicity (THE CENTERPIECE)
* `eigenvalues_mono` — A ⪯ B (form order) ⟹ λ_k(A) ≤ λ_k(B), every index k.

## Shift toolkit + Weyl
* `shiftOp`, `shiftOp_apply`, `shiftOp_symm`, `shiftOp_rayleigh`
* `shiftOp_apply_eigenvectorBasis` — shiftOp has eigenvector e_i, eigenvalue λ_i + c
* `charpoly_shiftOp`              — charpoly(B + c·I) = ∏ᵢ (X − C(λᵢ + c))
* `eigenvalues_shiftOp`          — λ_k(B + c·I) = λ_k(B) + c   [via the charpoly
                                    product form, sidestepping roots-under-composition]
* `eigenvalues_dist_le`          — WEYL: |re⟨x,Ax⟩−re⟨x,Bx⟩| ≤ M‖x‖² ⟹ |λ_k(A)−λ_k(B)| ≤ M

The Weyl bound is the per-eigenvalue perturbation control required by the operator-side
residual argument; it connects directly to `perturbedOp_formLowerBound`.
-/

namespace RHFormalization
-- Documentation capstone; all results live in MinMaxBrick1–10.
end RHFormalization
