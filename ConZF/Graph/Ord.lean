import ConZF.Graph.Rank
/-!
Ordinals among graph sets, in the stable reading: no self-membership, members of ordinals are
ordinals, negative trichotomy (`IsOrd.trichotomy`), and the previously deferred normalization
fact that an ordinal is equivalent to its rank (`rank_equiv_of_isOrd`), so that the transitive
closure of an ordinal presentation is a stable, transitive presentation of the same ordinal.

The semantic order on the vertices of a graph, `Mem (G.at' a) (G.at' b)`, is distinct from the
raw edge relation: a presentation may contain two vertices for the same ordinal with only one of
them connected below another. Comparisons of labels must use this semantic order, with
bisimulation for ties; it has stable well-founded induction (`swf_semMem`) for every graph, and
is transitive on the vertices of an ordinal presentation (`semMem_trans`).
-/
universe u

namespace GSet

theorem mem_asymm (G : GSet.{u}) : ∀ {K}, Mem K G → ¬ Mem G K :=
  mem_induction (F := fun G => ∀ {K}, Mem K G → ¬ Mem G K) (fun _ ih _ hK hG => ih _ hK hG hK) G

theorem not_mem_self (G : GSet.{u}) : ¬ Mem G G := fun h => mem_asymm G h h

theorem IsOrd.congr {G G' : GSet.{u}} (e : Equiv G G') (h : IsOrd G) : IsOrd G' :=
  ⟨fun K hK K' hK' => Mem.congr_right e (h.1 K (Mem.congr_right e.symm hK) K' hK'),
   fun K hK => h.2 K (Mem.congr_right e.symm hK)⟩

instance {G : GSet.{u}} : Stable (IsOrd G) := inferInstanceAs (Stable (_ ∧ ∀ K, _ → Trans K))

theorem IsOrd.mem {G K : GSet.{u}} (h : IsOrd G) (hK : Mem K G) : IsOrd K :=
  ⟨h.2 K hK, fun K' hK' => h.2 K' (h.1 K hK K' hK')⟩

/-- Negative trichotomy for graph ordinals. -/
theorem IsOrd.trichotomy : ∀ {a b : GSet.{u}}, IsOrd a → IsOrd b →
    ¬¬(Mem a b ∨ Equiv a b ∨ Mem b a) := by
  intro a
  refine mem_induction (F := fun a => ∀ {b}, IsOrd a → IsOrd b → ¬¬(Mem a b ∨ Equiv a b ∨ Mem b a))
    (fun a iha => ?_) a
  intro b
  refine mem_induction (F := fun b => IsOrd a → IsOrd b → ¬¬(Mem a b ∨ Equiv a b ∨ Mem b a))
    (fun b ihb => ?_) b
  intro ha hb
  refine Stable.by_cases (Mem a b) (fun h => nn_intro (.inl h)) fun h1 => ?_
  refine Stable.by_cases (Mem b a) (fun h => nn_intro (.inr (.inr h))) fun h2 => ?_
  refine nn_intro (.inr (.inl (ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)))
  · refine Stable.of_nn (iha z hz (ha.mem hz) hb) fun h => ?_
    rcases h with h | h | h
    · exact h
    · exact (h2 (Mem.congr_left h hz)).elim
    · exact (h2 (ha.1 z hz b h)).elim
  · refine Stable.of_nn (ihb z hz ha (hb.mem hz)) fun h => ?_
    rcases h with h | h | h
    · exact (h1 (hb.1 z hz a h)).elim
    · exact (h1 (Mem.congr_left h.symm hz)).elim
    · exact h

/-! ### Normalization -/

/-- At every vertex denoting an ordinal, the rank agrees with the graph. -/
theorem rank_at'_equiv_of_isOrd (G : GSet.{u}) :
    ∀ a : G.A, IsOrd (G.at' a) → Equiv ((rank G).at' a) (G.at' a) := by
  refine G.swf (fun a => IsOrd (G.at' a) → Equiv ((rank G).at' a) (G.at' a))
    (fun _ => inferInstance) fun a ih ha => ?_
  refine ext fun K => ⟨fun hK => ?_, fun hK => ?_⟩
  · refine Stable.of_nn (mem_rank_at'.1 hK) fun ⟨b, hb, h⟩ => ?_
    have e := ih b hb (ha.mem (at'_mem hb))
    rcases h with h | h
    · exact Mem.congr_left (h.trans e).symm (at'_mem hb)
    · exact ha.1 _ (at'_mem hb) K (Mem.congr_right e h)
  · refine Stable.of_nn hK fun ⟨b, hb, e⟩ => ?_
    exact nn_intro ⟨b, TC.of_rel hb, e.trans (ih b hb (ha.mem (at'_mem hb))).symm⟩

/-- **Normalization.** An ordinal is equivalent to its rank. -/
theorem rank_equiv_of_isOrd {G : GSet.{u}} (h : IsOrd G) : Equiv (rank G) G :=
  rank_at'_equiv_of_isOrd G G.r h

/-! ### The semantic order on vertices -/

/-- The semantic order on the vertices of `G`. -/
def SemMem (G : GSet.{u}) (a b : G.A) : Prop := Mem (G.at' a) (G.at' b)

instance {G : GSet.{u}} {a b : G.A} : Stable (SemMem G a b) := inferInstanceAs (Stable (Mem _ _))

/-- The semantic order has stable well-founded induction, for every graph. -/
theorem swf_semMem (G : GSet.{u}) : Graph.SWF (SemMem G) := by
  intro P hs H
  have key : ∀ b, ∀ a, Equiv (G.at' a) (G.at' b) → P a := by
    refine G.swf (fun b => ∀ a, Equiv (G.at' a) (G.at' b) → P a) (fun _ => inferInstance) ?_
    intro b ih a e
    refine H a fun a' ha' => ?_
    exact Stable.of_nn (Mem.congr_right e ha') fun ⟨b', hb', e'⟩ => ih b' hb' a' e'
  exact fun a => key a a (Equiv.refl _)

/-- On the vertices of an ordinal presentation, the semantic order is transitive. -/
theorem semMem_trans {G : GSet.{u}} (hG : IsOrd G) {a b c : G.A} (hc : SemMem G c G.r)
    (hab : SemMem G a b) (hbc : SemMem G b c) : SemMem G a c :=
  (hG.mem hc).1 _ hbc _ hab

/-- info: 'GSet.IsOrd.trichotomy' does not depend on any axioms -/
#guard_msgs in #print axioms IsOrd.trichotomy
/-- info: 'GSet.rank_equiv_of_isOrd' does not depend on any axioms -/
#guard_msgs in #print axioms rank_equiv_of_isOrd
/-- info: 'GSet.swf_semMem' does not depend on any axioms -/
#guard_msgs in #print axioms swf_semMem

end GSet
