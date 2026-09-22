import ConZF.Graph.Ops
/-!
Graph rank is transitive closure. For a graph `G`, `GSet.rank G` is the same carrier and root
with the edge relation replaced by negative existence of a nonempty finite path (`TC`); stable
well-founded induction transfers (`swf_tc`). Rank is idempotent (`rank_rank`), respects
equivalence (`rank_congr`), is transitive at every vertex, and satisfies the recurrence in
membership form (`mem_rank_at'`): the members of the rank at `a` are, negatively, the ranks at
predecessors of `a` and their members. No recursion produces the value; a relation on a
supplied carrier is changed.

The universal bound: for a small type `T`, a code is a subset of `T` with a relation and a proof
of stable well-founded induction (`SCode`), a root above all its vertices gives a graph, and the
rank of the range of the ranks of all codes (`univBound T`) contains the rank of every code
(`code_rank_mem`). This is the fixed-carrier bound the condensation argument consumes; the
proof field is `SWF`, not `WellFounded`.
-/
universe u

namespace GSet

/-! ### Paths -/

section paths
variable {A : Type u} (R : A → A → Prop)

/-- Nonempty finite paths. -/
inductive Path : A → A → Prop
  | single {a b} : R a b → Path a b
  | cons {a b c} : R a b → Path b c → Path a c

/-- Negative existence of a nonempty path. -/
def TC (a b : A) : Prop := ¬¬Path R a b

instance {a b : A} : Stable (TC R a b) := inferInstanceAs (Stable (¬_))

variable {R}

theorem Path.append {a b c : A} : Path R a b → Path R b c → Path R a c
  | .single h, p => .cons h p
  | .cons h p, q => .cons h (p.append q)

/-- A path decomposes at its last edge. -/
theorem Path.last {b a : A} : Path R b a → ∃ c, R c a ∧ (b = c ∨ Path R b c)
  | .single h => ⟨_, h, .inl rfl⟩
  | .cons h p =>
    have ⟨c, hc, hp⟩ := Path.last p
    ⟨c, hc, .inr (hp.elim (fun e => e ▸ .single h) fun q => .cons h q)⟩

theorem TC.trans {a b c : A} (h : TC R a b) (h' : TC R b c) : TC R a c :=
  Stable.of_nn h fun p => Stable.of_nn h' fun q => nn_intro (p.append q)

theorem TC.of_rel {a b : A} (h : R a b) : TC R a b := nn_intro (.single h)

/-- A path of `TC`-edges flattens to a `TC`-edge. -/
theorem TC.of_path_tc {a b : A} : Path (TC R) a b → TC R a b
  | .single h => h
  | .cons h p => h.trans (TC.of_path_tc p)

/-- Stable well-founded induction transfers to the transitive closure. -/
theorem swf_tc (h : Graph.SWF R) : Graph.SWF (TC R) := by
  intro P hs H
  have key : ∀ a, ∀ b, (b = a ∨ Path R b a) → P b := by
    refine h (fun a => ∀ b, (b = a ∨ Path R b a) → P b) (fun _ => inferInstance) ?_
    intro a ih b hb
    rcases hb with rfl | p
    · refine H b fun b' hb' => ?_
      refine Stable.of_nn hb' fun p => ?_
      obtain ⟨c, hc, hp⟩ := p.last
      exact ih c hc b' hp
    · obtain ⟨c, hc, hp⟩ := p.last
      exact ih c hc b hp
  exact fun a => key a a (.inl rfl)

end paths

/-! ### Rank -/

/-- The rank of a graph: the transitive closure of its edges on the same carrier. -/
def rank (G : GSet.{u}) : GSet.{u} := ⟨G.A, TC G.R, G.r, swf_tc G.swf⟩

theorem rank_at' (G : GSet.{u}) (a : G.A) : rank (G.at' a) = (rank G).at' a := rfl

/-- Membership in the rank at a vertex: the ranks at predecessors, and their members. -/
theorem mem_rank_at' {G : GSet.{u}} {a : G.A} {K : GSet.{u}} :
    Mem K ((rank G).at' a) ↔
      ¬¬∃ b, G.R b a ∧ (Equiv K ((rank G).at' b) ∨ Mem K ((rank G).at' b)) := by
  constructor
  · intro h
    refine nn_bind h fun ⟨c, hc, e⟩ => ?_
    refine nn_map (fun p => ?_) hc
    obtain ⟨b, hb, hp⟩ := Path.last p
    rcases hp with rfl | p
    · exact ⟨_, hb, .inl e⟩
    · exact ⟨b, hb, .inr (nn_intro ⟨c, nn_intro p, e⟩)⟩
  · intro h
    refine nn_bind h fun ⟨b, hb, hbe⟩ => ?_
    rcases hbe with e | h
    · exact nn_intro ⟨b, TC.of_rel hb, e⟩
    · exact nn_map (fun ⟨c, hc, e⟩ => ⟨c, hc.trans (TC.of_rel hb), e⟩) h

/-- Rank is idempotent. -/
theorem rank_rank (G : GSet.{u}) : Equiv (rank (rank G)) (rank G) := by
  refine nn_intro ⟨fun a b => ¬¬(a = b), ⟨fun _ _ => inferInstance, ?_, ?_⟩, nn_intro rfl⟩
  · intro a b hab a' ha'
    refine Stable.of_nn hab fun e => ?_
    subst e
    refine nn_intro ⟨a', fun hn => ha' fun p => TC.of_path_tc p hn, nn_intro rfl⟩
  · intro a b hab b' hb'
    refine Stable.of_nn hab fun e => ?_
    subst e
    exact nn_intro ⟨b', TC.of_rel hb', nn_intro rfl⟩

/-- A bisimulation matches paths. -/
theorem IsBisim.path {G H : GSet.{u}} {Z} (h : IsBisim G H Z) :
    ∀ {x y : G.A}, Path G.R x y → ∀ b, Z y b → ¬¬∃ b', Path H.R b' b ∧ Z x b'
  | _, _, .single ha', b, hab =>
    nn_map (fun ⟨b', hb', hz⟩ => ⟨b', .single hb', hz⟩) (h.forth _ b hab _ ha')
  | _, _, .cons ha' p, b, hab =>
    Stable.of_nn (IsBisim.path h p b hab) fun ⟨d', hd', hz⟩ =>
      nn_map (fun ⟨b', hb', hz'⟩ => ⟨b', .cons hb' hd', hz'⟩) (h.forth _ d' hz _ ha')

theorem IsBisim.rank {G H : GSet.{u}} {Z} (h : IsBisim G H Z) : IsBisim (rank G) (rank H) Z :=
  ⟨h.stable,
   fun _ b hab _ ha' => Stable.of_nn ha' fun p =>
     nn_map (fun ⟨b', hp, hz⟩ => ⟨b', nn_intro hp, hz⟩) (h.path p b hab),
   fun a _ hab _ hb' => Stable.of_nn hb' fun p =>
     nn_map (fun ⟨a', hp, hz⟩ => ⟨a', nn_intro hp, hz⟩) (h.symm.path p a hab)⟩

theorem rank_congr {G H : GSet.{u}} (e : Equiv G H) : Equiv (rank G) (rank H) :=
  nn_map (fun ⟨Z, hZ, hr⟩ => ⟨Z, hZ.rank, hr⟩) e

/-- Rank respects membership. -/
theorem rank_mem {K G : GSet.{u}} (h : Mem K G) : Mem (rank K) (rank G) :=
  nn_map (fun ⟨a, ha, e⟩ => ⟨a, TC.of_rel ha, rank_congr e⟩) h

/-! ### Transitivity and ordinals -/

/-- Transitive graph sets. -/
def Trans (G : GSet.{u}) : Prop := ∀ K, Mem K G → ∀ K', Mem K' K → Mem K' G

instance {G : GSet.{u}} : Stable (Trans G) :=
  inferInstanceAs (Stable (∀ K, Mem K G → ∀ K', Mem K' K → Mem K' G))

/-- Ordinals: transitive sets of transitive sets. -/
def IsOrd (G : GSet.{u}) : Prop := Trans G ∧ ∀ K, Mem K G → Trans K

theorem trans_rank_at' (G : GSet.{u}) (a : G.A) : Trans ((rank G).at' a) := by
  intro K hK K' hK'
  refine Stable.of_nn hK fun ⟨b, hb, e⟩ => ?_
  refine Stable.of_nn (Mem.congr_right e hK') fun ⟨c, hc, e'⟩ => ?_
  exact nn_intro ⟨c, hc.trans hb, e'⟩

theorem isOrd_rank (G : GSet.{u}) : IsOrd (rank G) :=
  ⟨trans_rank_at' G G.r, fun _ hK => Stable.of_nn hK fun ⟨b, _, e⟩ =>
    fun K' hK' K'' hK'' => Mem.congr_right e.symm
      (trans_rank_at' G b K' (Mem.congr_right e hK') K'' hK'')⟩

/-! ### The universal bound on a fixed carrier -/

/-- A code: a subset of `T` with a relation and stable well-founded induction. -/
structure SCode (T : Type u) : Type u where
  S : T → Prop
  R : {t : T // S t} → {t : T // S t} → Prop
  swf : Graph.SWF R

namespace SCode
variable {T : Type u} (c : SCode T)

/-- The code's relation with a root above every vertex. -/
inductive RootRel : Option {t : T // S c t} → Option {t : T // S c t} → Prop
  | comp {a b} : c.R a b → RootRel (some a) (some b)
  | top (a) : RootRel (some a) none

theorem rootRel_some {b} {x} (h : RootRel c x (some b)) : ∃ a, c.R a b ∧ x = some a := by
  cases h with
  | comp h => exact ⟨_, h, rfl⟩

theorem swf_rootRel : Graph.SWF (RootRel c) := by
  intro P hs H
  have comp : ∀ a, P (some a) := by
    refine c.swf (fun a => P (some a)) (fun _ => hs _) fun a ih => H _ fun x hx => ?_
    obtain ⟨a', ha', rfl⟩ := rootRel_some c hx
    exact ih a' ha'
  intro x
  cases x with
  | some a => exact comp a
  | none => exact H _ fun x hx => by cases hx with | top a => exact comp a

/-- The rooted graph of a code. -/
def graph : GSet.{u} := ⟨Option {t : T // S c t}, RootRel c, none, swf_rootRel c⟩

/-- The height of a code: the rank of its rooted graph. -/
def height : GSet.{u} := rank c.graph

end SCode

/-- The universal bound of a carrier: the rank of the range of the heights of all codes. -/
def univBound (T : Type u) : GSet.{u} := rank (range fun c : SCode T => c.height)

theorem isOrd_univBound (T : Type u) : IsOrd (univBound T) := isOrd_rank _

/-- **The bound.** Every code's height is a member of the universal bound. -/
theorem code_height_mem {T : Type u} (c : SCode T) : Mem c.height (univBound T) :=
  Mem.congr_left (rank_rank c.graph)
    (rank_mem ((mem_range fun c : SCode T => c.height).2 (nn_intro ⟨c, Equiv.refl _⟩)))

/-- info: 'GSet.mem_rank_at'' does not depend on any axioms -/
#guard_msgs in #print axioms mem_rank_at'
/-- info: 'GSet.code_height_mem' does not depend on any axioms -/
#guard_msgs in #print axioms code_height_mem

end GSet
