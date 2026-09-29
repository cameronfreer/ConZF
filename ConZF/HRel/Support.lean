import ConZF.HRel.Core

/-!
Weak transitive support and its exact set (conzf30, second stage).

`Support U y` holds when, negatively, `y ⊆ T` for some transitive `T` with a relational injection
into `U`. This is the **weak, root-free** convention: `y` is a subset of `T`, not a member, so at
`U = ∅` it admits `y = ∅`. It is kept distinct from the usual hereditary-cardinality class.

Support respects equivalence and is monotone in the base; a supported set is included in `raw U`
(`support_subset_raw`). `hereditary U` is the exact support set, cut from `powerset (raw U)` by
Separation (`mem_hereditary`), and is transitive. `raw U` itself is only an envelope on the literal
carrier and is not the exact support set. The auxiliary witnesses `T` and `r` fit boxes built from
`U` before any support witness is opened (`support_boxed`).
-/
universe u
namespace GSet.HRel

theorem RInj.mono {r T U V : GSet.{u}} (h : RInj r T U) (s : Subset U V) :
    RInj r T V := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    exact nn_map (fun ⟨t, v, ht, hv, eqv⟩ => ⟨t, v, ht, s v hv, eqv⟩) (h.1 q hq)
  · intro t ht
    exact nn_map (fun ⟨v, hv, hp⟩ => ⟨v, s v hv, hp⟩) (h.2.1 t ht)
  · intro t t' v ht ht' _ hp hp'
    exact h.2.2 t t' v ht ht' (Consumer.edge_typed h.1 hp).2 hp hp'

/-- Weak hereditary-support convention: y is a SUBSET of T, not a MEMBER of T. -/
def Support (U y : GSet.{u}) : Prop :=
  ¬¬∃ T r, Trans T ∧ Subset y T ∧ RInj r T U

instance {U y : GSet.{u}} : Stable (Support U y) := inferInstanceAs (Stable (¬_))

theorem support_resp {U y y' : GSet.{u}} (e : Equiv y y') (h : Support U y) :
    Support U y' :=
  nn_map (fun ⟨T, r, hT, sy, hr⟩ =>
    ⟨T, r, hT, (fun z hz => sy z (Mem.congr_right e.symm hz)), hr⟩) h

theorem support_mono {U V y : GSet.{u}} (s : Subset U V) (h : Support U y) :
    Support V y :=
  nn_map (fun ⟨T, r, hT, hy, hr⟩ => ⟨T, r, hT, hy, hr.mono s⟩) h

theorem support_subset_raw {U y : GSet.{u}} (h : Support U y) : Subset y (raw U) := by
  intro z hz
  refine Stable.of_nn h fun ⟨T, r, hT, hy, hr⟩ => ?_
  exact subset_raw_of_rInj hT hr z (hy z hz)

/-- Exact support set; the first endpoint does not need its exactness theorem. -/
def hereditary (U : GSet.{u}) : GSet.{u} := sep (Support U) (powerset (raw U))

theorem mem_hereditary {U y : GSet.{u}} : Mem y (hereditary U) ↔ Support U y := by
  refine (mem_sep (Support U) (powerset (raw U))
    (fun _ _ e h => support_resp e h)).trans ?_
  exact ⟨And.right, fun h => ⟨(mem_powerset _).2 (support_subset_raw h), h⟩⟩

theorem trans_hereditary (U : GSet.{u}) : Trans (hereditary U) := by
  intro y hy z hz
  apply mem_hereditary.2
  refine nn_map (fun ⟨T, r, hT, sy, hr⟩ => ?_) (mem_hereditary.1 hy)
  exact ⟨T, r, hT, (fun w hw => hT z (sy z hz) w hw), hr⟩

/-- A fixed box for the relation witness, not dependent on a selected T. -/
theorem relation_in_box {r T U : GSet.{u}} (hT : Trans T) (hr : RInj r T U) :
    Mem r (powerset (prod (raw U) U)) := by
  apply (mem_powerset _).2
  intro q hq
  refine Stable.of_nn (hr.1 q hq) fun ⟨t, v, ht, hv, e⟩ => ?_
  exact Mem.congr_left e.symm
    (opair_mem_prod _ _ (subset_raw_of_rInj hT hr t ht) hv)

/-- All auxiliary witnesses fit boxes constructed from U before opening Support. -/
theorem support_boxed {U y : GSet.{u}} : Support U y ↔
    ¬¬∃ T r, Mem T (powerset (raw U)) ∧
      Mem r (powerset (prod (raw U) U)) ∧
      Trans T ∧ Subset y T ∧ RInj r T U := by
  constructor
  · exact nn_map fun ⟨T, r, hT, hy, hr⟩ =>
      ⟨T, r, (mem_powerset _).2 (subset_raw_of_rInj hT hr),
        relation_in_box hT hr, hT, hy, hr⟩
  · exact nn_map fun ⟨T, r, _, _, hT, hy, hr⟩ => ⟨T, r, hT, hy, hr⟩

/-- info: 'GSet.HRel.mem_hereditary' does not depend on any axioms -/
#guard_msgs in #print axioms mem_hereditary
/-- info: 'GSet.HRel.support_boxed' does not depend on any axioms -/
#guard_msgs in #print axioms support_boxed

end GSet.HRel
