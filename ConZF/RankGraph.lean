import ConZF.ModelBase
/-!
Rank as a graph. For the first-order characterization of rank over `HG` (`RankFml.lean`), the
witnesses are constructed natively: the transitive closure `tcl x` of `x` by iterated union,
the domain `tclDom x = succ (tcl x)`, a transitive set containing `x`, and the graph
`rankGraph x` of `z ↦ (z, rank z)` over the literal indices of the domain. Their ranks are
bounded by the rank of `x` plus a fixed finite amount, so they are in `HG` when `x` is
(`hg_tclDom`, `hg_rankGraph`). No Replacement is used.

Conversely any graph on a transitive domain that is total, functional and satisfies the rank
recursion assigns the rank (`rank_unique`), by membership induction on a stable predicate. The
statement carries the `HG` guards of the readback of the formula.
-/
universe u

namespace PSet

/-! ### Transitive closure -/

/-- Iterated union. -/
def sUnionN : Nat → PSet.{u} → PSet.{u}
  | 0, x => x
  | n+1, x => sUnion (sUnionN n x)

theorem rank_mem_of_mem_sUnionN {x : PSet.{u}} :
    ∀ {n : Nat} {z : PSet.{u}}, z ∈ sUnionN n x → rank z ∈ rank x
  | 0, _, hz => rank_mem hz
  | _+1, _, hz => Stable.of_nn (mem_sUnion.1 hz) fun ⟨_, hw, hz⟩ =>
      (isOrd_rank x).trans _ (rank_mem_of_mem_sUnionN hw) _ (rank_mem hz)

/-- The transitive closure of `x`: the union of the iterated unions. -/
def tcl (x : PSet.{u}) : PSet.{u} := iUnion (ι := ULift.{u} Nat) fun n => sUnionN n.down x

theorem mem_tcl {x z : PSet.{u}} : z ∈ tcl x ↔ ¬¬∃ n, z ∈ sUnionN n x :=
  mem_iUnion.trans ⟨nn_map fun ⟨n, h⟩ => ⟨n.down, h⟩, nn_map fun ⟨n, h⟩ => ⟨⟨n⟩, h⟩⟩

theorem mem_tcl_of_mem {x z : PSet.{u}} (h : z ∈ x) : z ∈ tcl x :=
  mem_tcl.2 (nn_intro ⟨0, h⟩)

theorem tcl_trans {x z w : PSet.{u}} (hz : z ∈ tcl x) (hw : w ∈ z) : w ∈ tcl x :=
  Stable.of_nn (mem_tcl.1 hz) fun ⟨n, hz⟩ =>
    mem_tcl.2 (nn_intro ⟨n+1, mem_sUnion.2 (nn_intro ⟨z, hz, hw⟩)⟩)

theorem rank_mem_of_mem_tcl {x z : PSet.{u}} (hz : z ∈ tcl x) : rank z ∈ rank x :=
  Stable.of_nn (mem_tcl.1 hz) fun ⟨_, hz⟩ => rank_mem_of_mem_sUnionN hz

/-- The domain of the rank graph: the transitive closure together with `x` itself, a
transitive set containing `x`. -/
def tclDom (x : PSet.{u}) : PSet.{u} := union (tcl x) (singleton x)

theorem mem_tclDom {x z : PSet.{u}} : z ∈ tclDom x ↔ ¬¬(z ∈ tcl x ∨ z ≈ x) :=
  mem_union.trans (nn_congr (or_congr Iff.rfl mem_singleton))

theorem self_mem_tclDom (x : PSet.{u}) : x ∈ tclDom x := mem_tclDom.2 (nn_intro (.inr (Equiv.refl _)))

theorem mem_tclDom_of_mem_tcl {x z : PSet.{u}} (h : z ∈ tcl x) : z ∈ tclDom x :=
  mem_tclDom.2 (nn_intro (.inl h))

theorem tclDom_trans {x z w : PSet.{u}} (hz : z ∈ tclDom x) (hw : w ∈ z) : w ∈ tclDom x :=
  Stable.of_nn (mem_tclDom.1 hz) fun
    | .inl hz => mem_tclDom_of_mem_tcl (tcl_trans hz hw)
    | .inr e => mem_tclDom_of_mem_tcl (mem_tcl_of_mem ((mem_congr_right e).1 hw))

theorem rank_mem_of_mem_tclDom {x z : PSet.{u}} (hz : z ∈ tclDom x) : rank z ∈ succ (rank x) :=
  Stable.of_nn (mem_tclDom.1 hz) fun
    | .inl hz => mem_succ_of_mem (rank_mem_of_mem_tcl hz)
    | .inr e => mem_succ_of_equiv (rank_congr e)

theorem hg_tclDom {x : PSet.{u}} (hx : HG x) : HG (tclDom x) :=
  HG.of_bound (Cls.succ hx) fun _ hz => rank_mem_of_mem_tclDom hz

/-! ### Ranks of pairs -/

theorem rank_singleton_mem {a R : PSet.{u}} (hR : IsOrd R) (ha : rank a ∈ R) :
    rank (singleton a) ∈ succ R :=
  rank_mem_succ hR fun _ hz => (mem_congr_left (rank_congr (mem_singleton.1 hz))).2 ha

theorem rank_upair_mem {a b R : PSet.{u}} (hR : IsOrd R) (ha : rank a ∈ R) (hb : rank b ∈ R) :
    rank (upair a b) ∈ succ R :=
  rank_mem_succ hR fun _ hz => Stable.of_nn (mem_upair.1 hz) fun
    | .inl e => (mem_congr_left (rank_congr e)).2 ha
    | .inr e => (mem_congr_left (rank_congr e)).2 hb

theorem rank_pair_mem {a b R : PSet.{u}} (hR : IsOrd R) (ha : rank a ∈ R) (hb : rank b ∈ R) :
    rank (pair a b) ∈ succ (succ R) :=
  rank_upair_mem hR.succ (rank_singleton_mem hR ha) (rank_upair_mem hR ha hb)

/-! ### The rank graph -/

/-- The graph of `z ↦ (z, rank z)` over the domain. -/
def rankGraph (x : PSet.{u}) : PSet.{u} :=
  range fun i : (tclDom x).Idx => pair ((tclDom x).Func i) (rank ((tclDom x).Func i))

theorem mem_rankGraph {x p : PSet.{u}} :
    p ∈ rankGraph x ↔ ¬¬∃ z, z ∈ tclDom x ∧ p ≈ pair z (rank z) :=
  ⟨nn_map fun ⟨i, e⟩ => ⟨_, func_mem (tclDom x) i, e⟩,
   fun h => nn_bind h fun ⟨_, hz, e⟩ => nn_map (fun ⟨i, e'⟩ =>
    ⟨i, e.trans (pair_congr e' (rank_congr e'))⟩) hz⟩

theorem pair_rank_mem_rankGraph {x z : PSet.{u}} (hz : z ∈ tclDom x) :
    pair z (rank z) ∈ rankGraph x :=
  mem_rankGraph.2 (nn_intro ⟨z, hz, Equiv.refl _⟩)

/-- The graph assigns the rank. -/
theorem rankGraph_func {x z α : PSet.{u}} (h : pair z α ∈ rankGraph x) : α ≈ rank z :=
  Stable.of_nn (mem_rankGraph.1 h) fun ⟨_, _, e⟩ =>
    have ⟨e1, e2⟩ := pair_inj e
    e2.trans (rank_congr e1.symm)

theorem hg_rankGraph {x : PSet.{u}} (hx : HG x) : HG (rankGraph x) := by
  refine HG.of_bound hx.succ.succ.succ fun p hp => ?_
  refine Stable.of_nn (mem_rankGraph.1 hp) fun ⟨z, hz, e⟩ => ?_
  have hr : rank z ∈ succ (rank x) := rank_mem_of_mem_tclDom hz
  have hr' : rank (rank z) ∈ succ (rank x) := (mem_congr_left (isOrd_rank z).rank_equiv).2 hr
  exact (mem_congr_left (rank_congr e)).2 (rank_pair_mem (isOrd_rank x).succ hr hr')

/-! ### Uniqueness of rank assignments -/

/-- A graph on a transitive domain that is total, functional, and satisfies the rank recursion,
all with `HG` guards, assigns the rank. -/
theorem rank_unique {T g : PSet.{u}} (hT : ∀ z, z ∈ T → ∀ w, w ∈ z → w ∈ T)
    (hTg : HG T)
    (tot : ∀ z, z ∈ T → ¬¬∃ α, HG α ∧ pair z α ∈ g)
    (rec : ∀ z, z ∈ T → ∀ α, HG α → pair z α ∈ g → ∀ γ, HG γ →
      (γ ∈ α ↔ ¬¬∃ w, HG w ∧ w ∈ z ∧ ¬¬∃ δ, HG δ ∧ pair w δ ∈ g ∧ γ ∈ succ δ)) :
    ∀ z, z ∈ T → ∀ α, HG α → pair z α ∈ g → α ≈ rank z := by
  intro z
  refine mem_induction (P := fun z => z ∈ T → ∀ α, HG α → pair z α ∈ g → α ≈ rank z)
    (fun z ih hz α hα hzα => ?_) z
  refine ext fun γ => ?_
  constructor
  · intro hγ
    have hγH : HG γ := hα.mem hγ
    refine Stable.of_nn ((rec z hz α hα hzα γ hγH).1 hγ) fun ⟨w, _, hw, h⟩ => ?_
    refine Stable.of_nn h fun ⟨δ, hδ, hwδ, hγδ⟩ => ?_
    have e := ih w hw (hT z hz w hw) δ hδ hwδ
    exact mem_rank'.2 (nn_intro ⟨w, hw, (mem_congr_right (succ_congr e)).1 hγδ⟩)
  · intro hγ
    have hγH : HG γ := hTg.mem hz |>.rank.mem hγ
    refine (rec z hz α hα hzα γ hγH).2 ?_
    refine Stable.of_nn (mem_rank'.1 hγ) fun ⟨w, hw, hγw⟩ => ?_
    have hwT := hT z hz w hw
    refine nn_intro ⟨w, hTg.mem hwT, hw, ?_⟩
    refine Stable.of_nn (tot w hwT) fun ⟨δ, hδ, hwδ⟩ => ?_
    have e := ih w hw hwT δ hδ hwδ
    exact nn_intro ⟨δ, hδ, hwδ, (mem_congr_right (succ_congr e)).2 hγw⟩

/-- info: 'PSet.hg_rankGraph' does not depend on any axioms -/
#guard_msgs in #print axioms hg_rankGraph
/-- info: 'PSet.rank_unique' does not depend on any axioms -/
#guard_msgs in #print axioms rank_unique

end PSet
