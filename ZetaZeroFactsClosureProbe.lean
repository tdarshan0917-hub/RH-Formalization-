import RHFormalization

namespace RHFormalization

noncomputable section

#print IsNontrivialZetaZero
#print ZetaZeroFacts
#check ZetaZeroFacts.mk
#check RH_follows_from_packaged_spine

/--
First package-closure probe.

Goal: determine whether `ZetaZeroFacts` is already derivable from the current
definition of `IsNontrivialZetaZero`, or whether it is a genuine remaining
zeta-facts payload.
-/
theorem zetaZeroFacts_probe : ZetaZeroFacts := by
  refine ⟨?_⟩
  intro ρ hρ
  simp [IsNontrivialZetaZero] at hρ ⊢
  tauto

#print axioms zetaZeroFacts_probe

end

end RHFormalization
