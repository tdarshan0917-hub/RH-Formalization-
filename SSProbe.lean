import RHFormalization.MeromorphyAssembly
open Classical RHFormalization
example (s : Finset ℂ) (p : ℂ → Prop) (hp : ∀ x ∈ s, p x) (f : ℂ → ℂ) :
    Finset.sum (s.subtype p) (fun x => f x.1) = Finset.sum s f := by
  first
    | exact Finset.sum_subtype_of_mem f hp
    | (rw [Finset.sum_subtype_map_embedding (fun _ _ => rfl)]; simp)
    | (rw [← Finset.sum_attach s f]
       refine Finset.sum_nbij' (fun x => ⟨x.1, hp x.1 x.2⟩) (fun x => ⟨x.1, by
         have := x.2; simpa [Finset.mem_subtype] using this⟩) ?_ ?_ ?_ ?_ ?_ <;>
         (intros; simp_all [Finset.mem_subtype, Finset.mem_attach]))
    | sorry
