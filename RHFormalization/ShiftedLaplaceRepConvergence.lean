import RHFormalization.ShiftedLaplaceRepEnvelope
import RHFormalization.ConvergenceInfrastructure

namespace RHFormalization
noncomputable section
open Complex Filter Topology

def repSubtypeStage (n : ℕ) : Finset RepZeroIndex :=
  (subtypeStage n).filterMap
    (fun ρ => if h : ρ.1.re < 1/2 then some ⟨ρ.1, ρ.2, h⟩ else none)
    (by
      intro a b c ha hb
      simp only [Option.mem_def] at ha hb
      split_ifs at ha hb with h1 h2
      · have hac : (⟨a.1, a.2, h1⟩ : RepZeroIndex) = c := Option.some.inj ha
        have hbc : (⟨b.1, b.2, h2⟩ : RepZeroIndex) = c := Option.some.inj hb
        have e : (⟨a.1, a.2, h1⟩ : RepZeroIndex) = (⟨b.1, b.2, h2⟩ : RepZeroIndex) :=
          hac.trans hbc.symm
        apply Subtype.ext
        have : a.1 = b.1 := congrArg (fun x : RepZeroIndex => x.1) e
        exact this)

theorem repSubtypeStage_tendsto :
    Tendsto repSubtypeStage atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.mp subtypeStage_tendsto)
    (b.map ⟨repToFull, repToFull_injective⟩)
  refine ⟨N, fun m hm => ?_⟩
  intro ρ hρ
  have hmem : repToFull ρ ∈ b.map ⟨repToFull, repToFull_injective⟩ :=
    Finset.mem_map_of_mem _ hρ
  have hsub := hN m hm hmem
  rw [repSubtypeStage, Finset.mem_filterMap]
  refine ⟨repToFull ρ, hsub, ?_⟩
  simp only [repToFull]
  rw [dif_pos ρ.2.2]

#print axioms repSubtypeStage_tendsto

end
end RHFormalization
