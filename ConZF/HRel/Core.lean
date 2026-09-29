import ConZF.GraphConsumer

/-!
The raw transitive envelope (conzf30, con74), over the full ambient `GSet.{u}`. `NegCore`, the
source syntax and the existing theories are unchanged.

* `RInj r T U`: `r` is a pure, negatively total, inverse-unique relation from `T` to `U`. Forward
  functionality is not required. Only the forward adapter `RInj → InjRel` is needed
  (`injRel_of_rInj`).
* `raw U`: the range of the pointed **non-top** nodes of all stably well-founded codes on the literal
  carrier `U.A`, a small family with total graph-valued readback. It is not the range of their ranks.
  It is transitive (`trans_raw`), since a member of a pointed node is another pointed node of the
  same code, and it contains every transitive `T` with an injection relation into `U`
  (`subset_raw`), by the checked `Pullback.V_cover` and `Pullback.exact`, which need transitivity
  only. Ordinalhood matters only for rank comparisons, which are not made here.
* `raw U` uses the whole literal carrier, disconnected vertices included, so it is
  presentation-dependent and is **not** identified with an exact hereditary-support set; only its
  specification `axiomHrel` is used.
* `span X`: a transitive set containing `X` as a member, for transitive containment.
-/
universe u
namespace GSet.HRel

/-- A pure, total, inverse-unique relation. Forward functionality is not required. -/
def RInj (r T U : GSet.{u}) : Prop :=
  Consumer.TypedG r T U ∧ Consumer.TotalG r T U ∧
  ∀ t t' v, Mem t T → Mem t' T → Mem v U →
    Mem (opair t v) r → Mem (opair t' v) r → Equiv t t'

instance {r T U : GSet.{u}} : Stable (RInj r T U) :=
  ⟨fun h => ⟨fun q hq => Stable.dne fun hn => h fun z => hn (z.1 q hq),
    fun i hi => Stable.dne fun hn => h fun z => hn (z.2.1 i hi),
    fun t t' v ht ht' hv hp hp' => Stable.dne fun hn => h fun z => hn (z.2.2 t t' v ht ht' hv hp hp')⟩⟩

/-- The only relation bridge needed for the first consistency endpoint. -/
theorem injRel_of_rInj {r T U : GSet.{u}} (h : RInj r T U) : InjRel T U := by
  refine nn_intro ⟨fun t v => Mem (opair t (U.at' v)) r, ?_⟩
  refine ⟨fun _ _ => inferInstance, ?_, ?_, ?_, ?_⟩
  · intro t t' v e hp
    exact Mem.congr_left (opair_congr _ _ e (Equiv.refl _)) hp
  · intro t v v' e hp
    exact Mem.congr_left (opair_congr _ _ (Equiv.refl _) e) hp
  · intro t ht
    refine nn_bind (h.2.1 t ht) fun ⟨v, hv, hp⟩ => ?_
    exact nn_map (fun ⟨i, hi, ei⟩ =>
      ⟨i, hi, Mem.congr_left (opair_congr _ _ (Equiv.refl _) ei) hp⟩) hv
  · intro t t' v ht ht' hp hp'
    exact h.2.2 t t' (U.at' v) ht ht' (Consumer.edge_typed h.1 hp).2 hp hp'

/-- A small carrier; it contains code data, never an arbitrary GSet as data. -/
def Carrier (U : GSet.{u}) : Type u :=
  Σ c : SCode U.A, {v : U.A // c.S v}

/-- Total graph readback, before any supplied target is considered. -/
def readback (U : GSet.{u}) (q : Carrier U) : GSet.{u} :=
  q.1.graph.at' (some q.2)

/-- The raw, presentation-dependent transitive envelope. -/
def raw (U : GSet.{u}) : GSet.{u} := range (readback U)

theorem readback_mem (U : GSet.{u}) (q : Carrier U) : Mem (readback U q) (raw U) :=
  (mem_range _).2 (nn_intro ⟨q, Equiv.refl _⟩)

theorem trans_raw (U : GSet.{u}) : Trans (raw U) := by
  intro X hX Y hY
  refine Stable.of_nn ((mem_range _).1 hX) fun ⟨q, eqX⟩ => ?_
  have hy : Mem Y (q.1.graph.at' (some q.2)) := Mem.congr_right eqX hY
  refine Stable.of_nn hy fun ⟨z, hz, ez⟩ => ?_
  obtain ⟨v, _, rfl⟩ := SCode.rootRel_some q.1 hz
  exact Mem.congr_left ez.symm (readback_mem U ⟨q.1, v⟩)

/-- Original-value coverage, reusing checked Pullback.exact rather than graph rank. -/
theorem subset_raw {T U : GSet.{u}} (hT : Trans T) (h : InjRel T U) :
    Subset T (raw U) := by
  intro X hX
  refine Stable.of_nn h fun ⟨F, hF⟩ => ?_
  refine Stable.of_nn (Pullback.V_cover hF hX) fun ⟨p, hp⟩ => ?_
  exact Mem.congr_left (Pullback.exact hF hT X p hp)
    (readback_mem U ⟨Pullback.code hF, p⟩)

theorem subset_raw_of_rInj {r T U : GSet.{u}} (hT : Trans T) (h : RInj r T U) :
    Subset T (raw U) := subset_raw hT (injRel_of_rInj h)

/-- Do not demand that raw itself be congruent in U; only its specification is used. -/
theorem axiomHrel (U : GSet.{u}) :
    Trans (raw U) ∧ ∀ T r, Trans T → RInj r T U → Subset T (raw U) :=
  ⟨trans_raw U, fun _ _ hT h => subset_raw_of_rInj hT h⟩

/-- A transitive set containing X as a member; disconnected vertices are harmless. -/
def span (X : GSet.{u}) : GSet.{u} := range fun v : X.A => X.at' v

theorem mem_span (X : GSet.{u}) : Mem X (span X) :=
  (mem_range _).2 (nn_intro ⟨X.r, Equiv.refl _⟩)

theorem trans_span (X : GSet.{u}) : Trans (span X) := by
  intro Y hY Z hZ
  refine Stable.of_nn ((mem_range _).1 hY) fun ⟨v, ev⟩ => ?_
  refine Stable.of_nn (Mem.congr_right ev hZ) fun ⟨w, _, ew⟩ => ?_
  exact (mem_range _).2 (nn_intro ⟨w, ew⟩)

/-- info: 'GSet.HRel.injRel_of_rInj' does not depend on any axioms -/
#guard_msgs in #print axioms injRel_of_rInj
/-- info: 'GSet.HRel.trans_raw' does not depend on any axioms -/
#guard_msgs in #print axioms trans_raw
/-- info: 'GSet.HRel.subset_raw' does not depend on any axioms -/
#guard_msgs in #print axioms subset_raw
/-- info: 'GSet.HRel.axiomHrel' does not depend on any axioms -/
#guard_msgs in #print axioms axiomHrel
/-- info: 'GSet.HRel.trans_span' does not depend on any axioms -/
#guard_msgs in #print axioms trans_span

end GSet.HRel
