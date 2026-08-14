# Reusable Mathematics Inventory (draft, 2026-08-08)

## Operator/perturbation theory
RHFormalization/SplitRemainderZWiring.lean:33:theorem norm_split_remainder_trace_le
RHFormalization/FreeResolventMassBound.lean:31:theorem inv_norm_resolvent_le
RHFormalization/FreeResolventMassBound.lean:81:theorem free_resolvent_mass_le
RHFormalization/DiagTracePairingBound.lean:36:theorem abs_diag_entry_le_linfty_norm
RHFormalization/DiagTracePairingBound.lean:59:theorem abs_trace_diagonal_mul_le
RHFormalization/SymmetricRayleighOpBound.lean:28:theorem abs_eigenvalue_le_of_rayleigh
RHFormalization/SymmetricRayleighOpBound.lean:53:theorem norm_le_of_rayleigh_bound
RHFormalization/CompactSpectralGap.lean:29:theorem compact_spectral_gap
RHFormalization/CompactSpectralGap.lean:40:theorem compact_norm_bound
RHFormalization/HeatContractionBound.lean:33:theorem diagonal_linfty_norm_le {d : Fin N → ℝ} {C : ℝ} (hC : 0 ≤ C)
RHFormalization/HeatContractionBound.lean:69:theorem heat_diagonal_contraction (L t : ℝ) (ht : 0 ≤ t) :

## Duhamel/semigroup trace machinery
RHFormalization/AdaptivePairedFStage.lean
RHFormalization/AdaptivePairedResolventSplit.lean
RHFormalization/AdaptiveSectorObjects.lean
RHFormalization/AdmissibleFreeFH.lean
RHFormalization/AdmissiblePrimeStageIdentity.lean
RHFormalization/AlongNetBoundFromQRes.lean
RHFormalization/AppendixDFiniteSpikeExtractionWitness.lean
RHFormalization/AppendixDStructuralStageWitness.lean
RHFormalization/BetaConvBound.lean
RHFormalization/CorrectedResolventDirectCancellationTarget.lean
RHFormalization/DA2LaplaceResolvent.lean
RHFormalization/DBFFGate2WindowError.lean

## Normal families / Montel
RHFormalization/MontelSubsequenceAssembly.lean:34:theorem holomorphicMontelConvergence_from_ascoli
RHFormalization/AscoliLocBddBridge.lean:32:theorem dist_lt_of_locbdd_holo
RHFormalization/AscoliLocBddBridge.lean:94:theorem ascoliExtractionHyp_of_loc_bdd
RHFormalization/AscoliLocBddBridge.lean:147:theorem ascoliExtraction_of_loc_bdd
RHFormalization/AscoliLocBddBridge.lean:156:theorem RH_from_admissible_B_locbdd

## Integral identities
RHFormalization/CosResolventKernelIdentityOmega.lean:32:theorem cosResolventIntegrand_hasDerivAt (a : ℝ) (ξ : ℝ) {z : ℂ}
RHFormalization/CosResolventKernelIdentityOmega.lean:51:theorem cosResolventIntegrand_aesm (a : ℝ) (z : ℂ) :
RHFormalization/CosResolventKernelIdentityOmega.lean:62:theorem cosResolventDeriv_aesm (a : ℝ) (z : ℂ) :
RHFormalization/CosResolventKernelIdentityOmega.lean:73:theorem cosResolventLHS_differentiableAt_Omega (a : ℝ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
RHFormalization/CosResolventKernelIdentityOmega.lean:161:theorem cosResolventLHS_analytic_Omega (a : ℝ) :
RHFormalization/CosResolventKernelIdentityOmega.lean:169:theorem cosResolventRHS_analytic_Omega (a : ℝ) :
RHFormalization/CosResolventKernelIdentityOmega.lean:175:theorem one_mem_Omega : (1:ℂ) ∈ Ω := by
RHFormalization/CosResolventKernelIdentityOmega.lean:183:theorem cosResolvent_eqOn_Omega (a : ℝ) (ha : 0 ≤ a) :
