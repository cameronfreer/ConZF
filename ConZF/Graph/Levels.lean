import ConZF.Graph.Hier
/-!
Properties of the levels: monotonicity along the stage relation (`L_mono`), transitivity of every
level (`trans_L`), and presentation invariance (`L_congr`): a bisimulation between two ordinal
presentations relating two stages gives equivalent levels. All three follow from the recurrence
`mem_L_iff_Def`, `Def_congr`, and induction along the transitive closure; no name is
transported. Finite-name transport is needed only for the minimization of names across
presentations, which is a separate interface.
-/
universe u

namespace GSet

section
variable (α : GSet.{u})

/-- Levels increase along the stage relation. -/
theorem L_mono {b a : α.A} (h : Stage α b a) : Subset (L α b) (L α a) := fun _ hK =>
  (mem_L_iff_Def α).2 (nn_map (fun ⟨b', hb', hK⟩ => ⟨b', hb'.trans h, hK⟩) ((mem_L_iff_Def α).1 hK))

/-- Every level is transitive. -/
theorem trans_L (a : α.A) : Trans (L α a) := fun _ hK K' hK' =>
  Stable.of_nn ((mem_L_iff_Def α).1 hK) fun ⟨b, hb, hK⟩ =>
    L_mono α hb K' (subset_of_mem_Def (L α b) hK K' hK')

end

/-- **Presentation invariance.** A bisimulation between two presentations relating two stages
gives equivalent levels. -/
theorem L_congr_of_bisim {α α' : GSet.{u}} {Z} (hZ : IsBisim α α' Z) :
    ∀ a a', Z a a' → Equiv (L α a) (L α' a') := by
  refine swf_tc α.swf (fun a => ∀ a', Z a a' → Equiv (L α a) (L α' a')) (fun _ => inferInstance) ?_
  intro a ih a' haa'
  refine ext fun K => ⟨fun hK => ?_, fun hK => ?_⟩
  · refine (mem_L_iff_Def α').2 (nn_bind ((mem_L_iff_Def α).1 hK) fun ⟨b, hb, hK⟩ => ?_)
    refine Stable.of_nn hb fun p => ?_
    refine nn_map (fun ⟨b', hp, hbb'⟩ => ⟨b', nn_intro hp, ?_⟩) (hZ.path p a' haa')
    exact mem_Def_of_equiv (ih b (nn_intro p) b' hbb') hK
  · refine (mem_L_iff_Def α).2 (nn_bind ((mem_L_iff_Def α').1 hK) fun ⟨b', hb', hK⟩ => ?_)
    refine Stable.of_nn hb' fun p => ?_
    refine nn_map (fun ⟨b, hp, hbb'⟩ => ⟨b, nn_intro hp, ?_⟩) (hZ.symm.path p a haa')
    exact mem_Def_of_equiv (ih b (nn_intro hp) b' hbb').symm hK

/-- Equivalent presentations, at their roots, give equivalent levels. -/
theorem L_congr {α α' : GSet.{u}} (e : Equiv α α') : Equiv (L α α.r) (L α' α'.r) :=
  Stable.of_nn e fun ⟨_, hZ, hr⟩ => L_congr_of_bisim hZ _ _ hr

/-- info: 'GSet.trans_L' does not depend on any axioms -/
#guard_msgs in #print axioms trans_L
/-- info: 'GSet.L_congr' does not depend on any axioms -/
#guard_msgs in #print axioms L_congr

end GSet
