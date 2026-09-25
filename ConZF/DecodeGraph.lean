import ConZF.DecoderCap
import ConZF.Graph.Ops
import ConZF.Graph.Rank
/-!
The graph checkpoint for the decoder: a fixed small carrier whose graph rank has exactly the
original decoded ordinals as members. What it is and is not:

* `embed x` is the graph set of a pre-set, by structural recursion on the tree (never on a
  well-foundedness proof); it is fully faithful (`embed_equiv_iff`, `embed_mem_iff`).
* `assignment U` glues the rule assignments of the successful outputs of the decoder at the
  source `diagrams U` (with the `HG` guard on the output, `Success`). It is coherent, all its
  targets embed in `U`, and all their least controllers are below `λ U`
  (`assignment_controller_le`): so the labels of the fixed type `SmallLabel U (diagrams U)`
  cover every child (`assignment_cofinal`).
* `decoderGraph U` is the graph on the small carrier `List (SmallLabel U (diagrams U))` whose
  edges prepend a small label with an assigned target. Its well-foundedness field is `SWF`,
  obtained from `Desc` by stable membership induction on the original targets; it is not
  `Acc`, and no `Acc` is constructed.
* **Graph rank is essential and exact.** The raw pruned graph need not denote the original
  ordinal, since only cofinally many children are kept; its *rank* does (`graphNode_exact`):
  every targeted node of `GSet.rank (decoderGraph U)` denotes the embedding of its original
  target. Hence every original successful output, and its rank, is a member of the graph
  ordinal `decoderGraphHeight U` (`original_mem_graphHeight`). This is a graph-valued majorant
  of the decoder's spectrum, not a pre-set.
* `collecting_of_acc` records exactly what native accessibility of the glued relation would
  add: the collecting set of Replacement for this instance. That hypothesis is not discharged.
-/
universe u

namespace PSet.OrdDecode

/-! ### Embedding pre-sets into graph sets -/

/-- The graph of a pre-set: the range of the graphs of its children. -/
def embed : PSet.{u} → GSet.{u}
  | ⟨A, f⟩ => GSet.range fun a : A => embed (f a)

theorem mem_embed {x : PSet.{u}} {G : GSet.{u}} :
    GSet.Mem G (embed x) ↔ ¬¬∃ i : x.Idx, GSet.Equiv G (embed (x.Func i)) := by
  cases x with
  | mk A f => exact GSet.mem_range fun i : A => embed (f i)

/-- Full faithfulness of the embedding for bisimulation. -/
theorem embed_equiv_iff : ∀ x y : PSet.{u}, GSet.Equiv (embed x) (embed y) ↔ x ≈ y
  | ⟨A, f⟩, ⟨B, g⟩ => by
    constructor
    · intro h
      constructor
      · intro a
        have hm : GSet.Mem (embed (f a)) (embed ⟨A, f⟩) := mem_embed.2 (nn_intro ⟨a, GSet.Equiv.refl _⟩)
        exact nn_map (fun ⟨b, hb⟩ => ⟨b, (embed_equiv_iff (f a) (g b)).1 hb⟩)
          (mem_embed.1 (GSet.Mem.congr_right h hm))
      · intro b
        have hm : GSet.Mem (embed (g b)) (embed ⟨B, g⟩) := mem_embed.2 (nn_intro ⟨b, GSet.Equiv.refl _⟩)
        exact nn_map (fun ⟨a, ha⟩ => ⟨a, (embed_equiv_iff (f a) (g b)).1 ha.symm⟩)
          (mem_embed.1 (GSet.Mem.congr_right h.symm hm))
    · intro h
      refine GSet.ext fun G => ⟨fun hm => ?_, fun hm => ?_⟩
      · refine nn_bind (mem_embed.1 hm) fun ⟨a, ha⟩ => ?_
        exact mem_embed.2 (nn_map (fun ⟨b, hab⟩ =>
          ⟨b, ha.trans ((embed_equiv_iff (f a) (g b)).2 hab)⟩) (h.1 a))
      · refine nn_bind (mem_embed.1 hm) fun ⟨b, hb⟩ => ?_
        exact mem_embed.2 (nn_map (fun ⟨a, hab⟩ =>
          ⟨a, hb.trans ((embed_equiv_iff (f a) (g b)).2 hab).symm⟩) (h.2 b))

theorem embed_congr {x y : PSet.{u}} (h : x ≈ y) : GSet.Equiv (embed x) (embed y) :=
  (embed_equiv_iff x y).2 h

theorem embed_mem_iff {x y : PSet.{u}} : GSet.Mem (embed x) (embed y) ↔ x ∈ y :=
  mem_embed.trans (nn_congr ⟨fun ⟨i, hi⟩ => ⟨i, (embed_equiv_iff x (y.Func i)).1 hi⟩,
    fun ⟨i, hi⟩ => ⟨i, (embed_equiv_iff x (y.Func i)).2 hi⟩⟩)

/-- Every member of an embedded pre-set is, negatively, the embedding of an element. -/
theorem embed_readback {x : PSet.{u}} {G : GSet.{u}} (h : GSet.Mem G (embed x)) :
    ¬¬∃ z : PSet.{u}, z ∈ x ∧ GSet.Equiv G (embed z) :=
  nn_map (fun ⟨i, hi⟩ => ⟨x.Func i, func_mem x i, hi⟩) (mem_embed.1 h)

/-! ### The assignment of the decoder -/

section
variable [Budget.{u}]

/-- The successful original outputs, with the `HG` guard. -/
def Success (d a : PSet.{u}) : Prop := HG a ∧ Decoded d a

instance {d a : PSet.{u}} : Stable (Success d a) := inferInstanceAs (Stable (_ ∧ _))

theorem success_resp {d d' a a' : PSet.{u}} (ed : d ≈ d') (ea : a ≈ a') (h : Success d a) :
    Success d' a' :=
  ⟨HG.resp ea h.1, decoded_congr ed ea h.2⟩

theorem success_cls {d a : PSet.{u}} (h : Success d a) : Cls ISat a :=
  Cls.resp h.2.1.rank_equiv h.1

/-- The rule assignments of the successful outputs, glued below the children `c d`,
`d ∈ diagrams U`. -/
def assignment (U : PSet.{u}) : Path.{u} → PSet.{u} → Prop :=
  Glue (Tr (rule ISat)) (diagrams U) Success

theorem assignment_coherent (U : PSet.{u}) : Coherent D (diagrams U) (assignment U) :=
  glue_coherent (fun _ ha => (reach_rule ISat_resp (diagrams U)).coherent ha)
    (fun e h => Rule.tr_resp_root e h) (fun ed ea h => success_resp ed ea h)
    (fun _ h h' => decoded_unique h.2 h'.2) (fun _ h => success_cls h)

/-- Every rule descendant of an embeddable target embeds. -/
theorem trace_emb {a t U : PSet.{u}} {p : Path.{u}} (ha : Cls ISat a) (hi : Emb a U)
    (h : Tr (rule ISat) a p t) : Emb t U := by
  induction h with
  | nil e => exact hi.congr e
  | cons ht hr ih =>
    have hv := (reach_rule ISat_resp empty).tr_C ha ht
    exact Emb.down hv.1 (rule_mem ISat_resp hv hr).1 ih

theorem assignment_emb {U t : PSet.{u}} {p : Path.{u}} (h : assignment U p t) : Emb t U := by
  obtain ⟨_, d, _, _, hd, hs, ht⟩ := h
  exact trace_emb (success_cls hs) (emb_of_decoded hd hs.2) ht

theorem assignment_cls {U t : PSet.{u}} {p : Path.{u}} (h : assignment U p t) : Cls ISat t := by
  obtain ⟨_, _, _, _, _, hs, ht⟩ := h
  exact (reach_rule ISat_resp (diagrams U)).tr_C (success_cls hs) ht

/-- One library controls every target of the assignment. -/
theorem assignment_controller_le {U t : PSet.{u}} {p : Path.{u}} (h : assignment U p t) :
    Gν ISat t ∈ succ (lambda U) :=
  controller_le (assignment_cls h).1 (assignment_emb h)

/-- At an assigned node, a rule label has its original meaning. -/
theorem assignment_child_iff {U t t' : PSet.{u}} {p : Path.{u}} (hp : assignment U p t)
    (l : Label.{u}) : assignment U (l :: p) t' ↔ rule ISat t l t' := by
  obtain ⟨r, d, a, rfl, hd, hs, ht⟩ := hp
  exact (glue_iff (T := Tr (rule ISat)) (φ := Success) (fun e h => Rule.tr_resp_root e h)
    (fun _ h h' => decoded_unique h.2 h'.2) (r := l :: r) hd hs).trans
    ((reach_rule ISat_resp (diagrams U)).tr_cons_iff ht)

/-- The small-labelled children are cofinal in every assigned target. -/
theorem assignment_cofinal {U t : PSet.{u}} {p : List (SmallLabel U (diagrams U))}
    (hp : assignment U (SmallLabel.path p) t) (z : PSet.{u}) :
    z ∈ t ↔ ¬¬∃ (a : SmallLabel U (diagrams U)) (t' : PSet.{u}),
      assignment U (SmallLabel.path (a :: p)) t' ∧ z ∈ succ t' :=
  (cofinal_small_children (S := diagrams U) (assignment_cls hp) (assignment_emb hp) z).trans
    (nn_congr ⟨fun ⟨a, t', ht, hz⟩ => ⟨a, t', (assignment_child_iff hp a.label).2 ht, hz⟩,
      fun ⟨a, t', ht, hz⟩ => ⟨a, t', (assignment_child_iff hp a.label).1 ht, hz⟩⟩)

/-! ### The fixed small graph -/

/-- The edges: prepend a small label whose path has an assigned target. Existence is in `Prop`;
no valuation of paths is constructed. -/
def SmallRel {U S : PSet.{u}} (τ : Path.{u} → PSet.{u} → Prop)
    (p q : List (SmallLabel U S)) : Prop :=
  ∃ l : SmallLabel U S, p = l :: q ∧ ∃ t, τ (SmallLabel.path p) t

/-- `Desc` gives `SWF` of the small relation, by stable membership induction on the targets. -/
theorem smallRel_swf {U S : PSet.{u}} {τ : Path.{u} → PSet.{u} → Prop} (hd : Desc τ) :
    Graph.SWF fun p q : List (SmallLabel U S) => SmallRel τ p q := by
  intro P hs H
  haveI : ∀ p, Stable (P p) := hs
  have key : ∀ t : PSet.{u}, ∀ p : List (SmallLabel U S), τ (SmallLabel.path p) t → P p := by
    refine mem_induction (P := fun t => ∀ p : List (SmallLabel U S), τ (SmallLabel.path p) t → P p) ?_
    intro t ih p hp
    refine H p fun q hq => ?_
    obtain ⟨l, rfl, t', ht'⟩ := hq
    exact ih t' (hd ht' hp) (l :: p) ht'
  intro p
  refine H p fun q hq => ?_
  obtain ⟨l, rfl, t, ht⟩ := hq
  exact key t (l :: p) ht

/-- The graph of the decoder's assignment on the fixed small carrier. Its well-foundedness
field is `SWF`, not `Acc`. -/
def decoderGraph (U : PSet.{u}) : GSet.{u} where
  A := List (SmallLabel U (diagrams U))
  R := SmallRel (assignment U)
  r := []
  swf := smallRel_swf (assignment_coherent U).desc

/-- The graph ordinal of the decoder at `U`. -/
def decoderGraphHeight (U : PSet.{u}) : GSet.{u} := GSet.rank (decoderGraph U)

def graphNode (U : PSet.{u}) (p : List (SmallLabel U (diagrams U))) : GSet.{u} :=
  (decoderGraphHeight U).at' p

/-- **Exactness after graph rank.** Every targeted node of the rank of the pruned graph denotes
its original target. -/
theorem graphNode_exact (U : PSet.{u}) : ∀ t : PSet.{u}, ∀ p : List (SmallLabel U (diagrams U)),
    assignment U (SmallLabel.path p) t → GSet.Equiv (graphNode U p) (embed t) := by
  refine mem_induction (P := fun t => ∀ p : List (SmallLabel U (diagrams U)),
    assignment U (SmallLabel.path p) t → GSet.Equiv (graphNode U p) (embed t)) ?_
  intro t ih p hp
  have hto : IsOrd t := (assignment_cls hp).1
  refine GSet.ext fun Q => ⟨fun hQ => ?_, fun hQ => ?_⟩
  · refine Stable.of_nn (GSet.mem_rank_at'.1 hQ) fun ⟨q, hqp, hread⟩ => ?_
    obtain ⟨a, rfl, t', ht'⟩ := hqp
    have htt : t' ∈ t := (assignment_coherent U).desc ht' hp
    have ee := ih t' htt (a :: p) ht'
    rcases hread with eq | hm
    · exact GSet.Mem.congr_left (eq.trans ee).symm (embed_mem_iff.2 htt)
    · refine Stable.of_nn (embed_readback (GSet.Mem.congr_right ee hm)) fun ⟨z, hz, ez⟩ => ?_
      exact GSet.Mem.congr_left ez.symm (embed_mem_iff.2 (hto.trans t' htt z hz))
  · refine Stable.of_nn (embed_readback hQ) fun ⟨z, hzt, ez⟩ => ?_
    refine Stable.of_nn ((assignment_cofinal hp z).1 hzt) fun ⟨a, t', ht', hzt'⟩ => ?_
    have htt : t' ∈ t := (assignment_coherent U).desc ht' hp
    have ee := ih t' htt (a :: p) ht'
    refine GSet.mem_rank_at'.2 (Stable.of_nn (mem_succ.1 hzt') fun
      | .inl hm => nn_intro ⟨a :: p, ⟨a, rfl, t', ht'⟩, Or.inr ?_⟩
      | .inr eq => nn_intro ⟨a :: p, ⟨a, rfl, t', ht'⟩, Or.inl (ez.trans ((embed_congr eq).trans ee.symm))⟩)
    exact GSet.Mem.congr_right ee.symm (GSet.Mem.congr_left ez.symm (embed_mem_iff.2 hm))

/-- Every original successful output is a member of the graph ordinal. -/
theorem original_mem_graphHeight {U d a : PSet.{u}} (hd : d ∈ diagrams U) (hs : Success d a) :
    GSet.Mem (embed a) (decoderGraphHeight U) := by
  refine Stable.of_nn hd fun ⟨i, ed⟩ => ?_
  let p : List (SmallLabel U (diagrams U)) := [.source i]
  have hp : assignment U (SmallLabel.path p) a :=
    ⟨[], (diagrams U).Func i, a, rfl, func_mem _ i, success_resp ed (Equiv.refl _) hs,
      Tr.nil (Equiv.refl _)⟩
  have edge : (decoderGraph U).R p [] := ⟨.source i, rfl, a, hp⟩
  exact GSet.Mem.congr_left (graphNode_exact U a _ hp) (GSet.rank_mem (GSet.at'_mem edge))

/-- The rank of every original output is a member too: values are kept, not replaced. -/
theorem original_rank_mem_graphHeight {U d a : PSet.{u}} (hd : d ∈ diagrams U) (hs : Success d a) :
    GSet.Mem (embed (rank a)) (decoderGraphHeight U) :=
  GSet.Mem.congr_left (embed_congr hs.2.1.rank_equiv).symm (original_mem_graphHeight hd hs)

/-- At an `HG` base the `HG` guard is automatic. -/
theorem all_decoded_mem_graphHeight {U d a : PSet.{u}} (hU : HG U) (hd : d ∈ diagrams U)
    (h : Decoded d a) : GSet.Mem (embed a) (decoderGraphHeight U) :=
  original_mem_graphHeight hd ⟨decoded_hg hU hd h, h⟩

/-- What native accessibility would add, and what `SWF` does not: with `¬¬Acc` of the glued
relation at the root, the unchanged Replacement lemma returns the collecting set of the
decoder's successful outputs. This hypothesis is not discharged here. -/
theorem collecting_of_acc (U : PSet.{u}) (hacc : ¬¬Acc (Rel (assignment U)) []) :
    ¬¬∃ img : PSet.{u}, ∀ y, y ∈ img ↔ ¬¬∃ d, d ∈ diagrams U ∧ Success d y :=
  (reach_rule ISat_resp (diagrams U)).replacement (diagrams U) rfl Success
    (fun ed ea h => success_resp ed ea h) (fun _ h h' => decoded_unique h.2 h'.2)
    (fun _ h => success_cls h) fun _ => hacc

end

/-- info: 'PSet.OrdDecode.embed_equiv_iff' does not depend on any axioms -/
#guard_msgs in #print axioms embed_equiv_iff
/-- info: 'PSet.OrdDecode.assignment_controller_le' does not depend on any axioms -/
#guard_msgs in #print axioms assignment_controller_le
/-- info: 'PSet.OrdDecode.graphNode_exact' does not depend on any axioms -/
#guard_msgs in #print axioms graphNode_exact
/-- info: 'PSet.OrdDecode.original_rank_mem_graphHeight' does not depend on any axioms -/
#guard_msgs in #print axioms original_rank_mem_graphHeight
/-- info: 'PSet.OrdDecode.collecting_of_acc' does not depend on any axioms -/
#guard_msgs in #print axioms collecting_of_acc

end PSet.OrdDecode
