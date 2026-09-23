import ConZF.Graph.Ord
/-!
Relational pullback and the native graph Hartogs operator, from the graph layer alone: no `Def`,
no hierarchy, no hull.

An *injection relation* from a graph set `T` into a graph `X` (`InjRel`) is a stable relation
between members of `T` and root predecessors of `X`, respecting equivalence in both arguments,
total on the members of `T`, and inverse-unique: two members related to the same vertex are
equivalent. A graph-set injection given as a set of pairs would supply one; pairs are not yet
built for graph sets, so the relational form is the current interface.

**Pullback** (`Pullback`). Given such a relation, the subtype of vertices of `X` that
represent some member of `T` carries the pulled-back membership relation, stably well-founded by
ambient membership induction with the induction predicate quantified over all representatives
(`swf_rel`); no inverse image is selected. The rooted graph of this code, pointed at a
representative, is equivalent to the represented member (`exact`), by membership induction on
the member: full predecessor coverage is what makes this collapse exact, in contrast to an
elementary hull. Hence the rooted graph is equivalent to `T` when `T` is transitive
(`graph_equiv`), and its height is `T` when `T` is an ordinal (`height_equiv`).

**The relational Hartogs bound**. The code lives on the carrier of `X`, so the universal bound of
that carrier contains every ordinal with an injection relation into `X`
(`mem_univBound_of_injRel`), and the Separation cut `relHartogs X` is an ordinal with the exact
membership specification (`mem_relHartogs`), transitive, extensional in `X`
(`relHartogs_congr`), and with no injection relation into `X` (`not_injRel_relHartogs`). The
bound is built before any injection witness is opened.

What this cutoff is: an injection relation lets one member of `T` relate to several inequivalent
targets, so classically it is a surjection from a subset of `X` onto `T`, and `relHartogs X` is
the least ordinal that is not such a surjective image, a Lindenbaum-type number rather than the
ordinary Hartogs number; without choice the two can differ. An ordinary injection gives an
injection relation, so `not_injRel_relHartogs` excludes ordinary injections once set-coded
injections are bridged; the exact ordinary Hartogs cut would add a functionality condition to the
predicate and reuse the same bound theorem. The source-wide menu `menu a` collects these bounds
over the literal members of a supplied domain (`mem_menu`): every member of `a` has, negatively,
an ordinal in the menu with no injection relation into it.
-/
universe u

namespace GSet

/-- An injection relation from the members of `T` to the root predecessors of `X`. -/
structure IsInjRel (T X : GSet.{u}) (F : GSet.{u} → X.A → Prop) : Prop where
  stable : ∀ ξ a, Stable (F ξ a)
  resp_left : ∀ {ξ ξ' a}, Equiv ξ ξ' → F ξ a → F ξ' a
  resp_right : ∀ {ξ a b}, Equiv (X.at' a) (X.at' b) → F ξ a → F ξ b
  total : ∀ ξ, Mem ξ T → ¬¬∃ a, X.R a X.r ∧ F ξ a
  inv_unique : ∀ {ξ ξ' a}, Mem ξ T → Mem ξ' T → F ξ a → F ξ' a → Equiv ξ ξ'

/-- Negative existence of an injection relation. -/
def InjRel (T X : GSet.{u}) : Prop := ¬¬∃ F, IsInjRel T X F

instance {T X : GSet.{u}} : Stable (InjRel T X) := inferInstanceAs (Stable (¬_))

theorem InjRel.congr_left {T T' X : GSet.{u}} (e : Equiv T T') (h : InjRel T X) : InjRel T' X :=
  nn_map (fun ⟨F, hF⟩ => ⟨F, ⟨hF.stable, hF.resp_left, hF.resp_right,
    fun ξ hξ => hF.total ξ (Mem.congr_right e.symm hξ),
    fun hξ hξ' => hF.inv_unique (Mem.congr_right e.symm hξ) (Mem.congr_right e.symm hξ')⟩⟩) h

/-- Injection relations transport along equivalence of the codomain: relate to the
representatives of the same target value, with no choice. -/
theorem InjRel.congr_right {T X X' : GSet.{u}} (e : Equiv X X') (h : InjRel T X) : InjRel T X' := by
  refine Stable.of_nn e fun ⟨Z, hZ, hr⟩ => Stable.of_nn h fun ⟨F, hF⟩ => ?_
  let F' : GSet.{u} → X'.A → Prop := fun ξ b =>
    ¬¬∃ a, X.R a X.r ∧ F ξ a ∧ Equiv (X.at' a) (X'.at' b)
  refine nn_intro ⟨F', ⟨fun _ _ => inferInstance, ?_, ?_, ?_, ?_⟩⟩
  · exact fun e' h => nn_map (fun ⟨a, ha, hFa, e''⟩ => ⟨a, ha, hF.resp_left e' hFa, e''⟩) h
  · exact fun e' h => nn_map (fun ⟨a, ha, hFa, e''⟩ => ⟨a, ha, hFa, e''.trans e'⟩) h
  · intro ξ hξ
    refine Stable.of_nn (hF.total ξ hξ) fun ⟨a, ha, hFa⟩ => ?_
    refine nn_map (fun ⟨b, hb, hab⟩ => ⟨b, hb, nn_intro ⟨a, ha, hFa, hZ.at' hab⟩⟩)
      (hZ.forth X.r X'.r hr a ha)
  · intro ξ ξ' b hξ hξ' h1 h2
    refine Stable.of_nn h1 fun ⟨a, _, hFa, ea⟩ => Stable.of_nn h2 fun ⟨a', _, hFa', ea'⟩ => ?_
    exact hF.inv_unique hξ hξ' hFa (hF.resp_right (ea'.trans ea.symm) hFa')

/-- An injection relation restricts to a member of a transitive domain. -/
theorem IsInjRel.restrict {T X : GSet.{u}} {F} (h : IsInjRel T X F) (hT : Trans T) {S : GSet.{u}}
    (hS : Mem S T) : IsInjRel S X F :=
  ⟨h.stable, h.resp_left, h.resp_right, fun ξ hξ => h.total ξ (hT S hS ξ hξ),
   fun hξ hξ' => h.inv_unique (hT S hS _ hξ) (hT S hS _ hξ')⟩

/-! ### The pullback -/

namespace Pullback
variable {T X : GSet.{u}} {F : GSet.{u} → X.A → Prop} (h : IsInjRel T X F)

/-- The vertices of `X` that represent some member of `T`. -/
def S (a : X.A) : Prop := X.R a X.r ∧ ¬¬∃ ξ, Mem ξ T ∧ F ξ a

/-- The relational inverse value of a representative. -/
def V (p : {a : X.A // S (T := T) (F := F) a}) (ξ : GSet.{u}) : Prop := Mem ξ T ∧ F ξ p.1

/-- The pulled-back membership relation on representatives. -/
def rel (q p : {a : X.A // S (T := T) (F := F) a}) : Prop :=
  ¬¬∃ ξ η, V (T := T) (F := F) q ξ ∧ V (T := T) (F := F) p η ∧ Mem ξ η

omit h in
theorem V_total (p : {a : X.A // S (T := T) (F := F) a}) : ¬¬∃ ξ, V (T := T) (F := F) p ξ :=
  nn_map (fun ⟨ξ, hξ, hF⟩ => ⟨ξ, hξ, hF⟩) p.2.2

include h

theorem V_func {p : {a : X.A // S (T := T) (F := F) a}} {ξ ξ' : GSet.{u}}
    (h1 : V (T := T) (F := F) p ξ) (h2 : V (T := T) (F := F) p ξ') : Equiv ξ ξ' :=
  h.inv_unique h1.1 h2.1 h1.2 h2.2

theorem V_cover {ξ : GSet.{u}} (hξ : Mem ξ T) :
    ¬¬∃ p : {a : X.A // S (T := T) (F := F) a}, V (T := T) (F := F) p ξ :=
  nn_map (fun ⟨a, ha, hF⟩ => ⟨⟨a, ha, nn_intro ⟨ξ, hξ, hF⟩⟩, hξ, hF⟩) (h.total ξ hξ)

/-- The row equation: with the value of `p` supplied, an edge into `p` is a value below it. -/
theorem rel_iff {q p : {a : X.A // S (T := T) (F := F) a}} {η : GSet.{u}}
    (hp : V (T := T) (F := F) p η) :
    rel (T := T) (F := F) q p ↔ ¬¬∃ ξ, V (T := T) (F := F) q ξ ∧ Mem ξ η :=
  ⟨nn_map fun ⟨ξ, _, hq, hp', hm⟩ => ⟨ξ, hq, Mem.congr_right (V_func h hp' hp) hm⟩,
   nn_map fun ⟨ξ, hq, hm⟩ => ⟨ξ, η, hq, hp, hm⟩⟩

/-- Stable well-founded induction for the pulled-back relation, with no inverse selected. -/
theorem swf_rel : Graph.SWF (rel (T := T) (F := F)) := by
  intro P hs H
  have key : ∀ η : GSet.{u}, ∀ p, V (T := T) (F := F) p η → P p := by
    refine mem_induction (F := fun η => ∀ p, V (T := T) (F := F) p η → P p) fun η ih p hp => ?_
    refine H p fun q hq => ?_
    exact Stable.of_nn ((rel_iff h hp).1 hq) fun ⟨ξ, hqξ, hm⟩ => ih ξ hm q hqξ
  exact fun p => Stable.of_nn (V_total p) fun ⟨η, hp⟩ => key η p hp

/-- The pullback code on the carrier of `X`. -/
def code : SCode X.A := ⟨S (T := T) (F := F), rel (T := T) (F := F), swf_rel h⟩

/-- **Exactness.** The rooted graph at a representative is the represented member. -/
theorem exact (hT : Trans T) :
    ∀ η : GSet.{u}, ∀ p, V (T := T) (F := F) p η → Equiv ((code h).graph.at' (some p)) η := by
  refine mem_induction (F := fun η => ∀ p, V (T := T) (F := F) p η →
    Equiv ((code h).graph.at' (some p)) η) fun η ih p hp => ?_
  refine ext fun K => ⟨fun hK => ?_, fun hK => ?_⟩
  · refine Stable.of_nn hK fun ⟨x, hx, e⟩ => ?_
    obtain ⟨q, hq, rfl⟩ := SCode.rootRel_some (code h) hx
    refine Stable.of_nn ((rel_iff h hp).1 hq) fun ⟨ξ, hqξ, hm⟩ => ?_
    exact Mem.congr_left (e.trans (ih ξ hm q hqξ)).symm hm
  · have hKT : Mem K T := hT η hp.1 K hK
    refine Stable.of_nn (V_cover h hKT) fun ⟨q, hq⟩ => ?_
    have hqp : rel (T := T) (F := F) q p := (rel_iff h hp).2 (nn_intro ⟨K, hq, hK⟩)
    exact nn_intro ⟨some q, SCode.RootRel.comp hqp, (ih K hK q hq).symm⟩

/-- The rooted graph of the pullback is the domain. -/
theorem graph_equiv (hT : Trans T) : Equiv (code h).graph T := by
  refine ext fun K => ⟨fun hK => ?_, fun hK => ?_⟩
  · refine Stable.of_nn hK fun ⟨x, hx, e⟩ => ?_
    cases hx with
    | top p => exact Stable.of_nn (V_total p) fun ⟨η, hp⟩ =>
        Mem.congr_left (e.trans (exact h hT η p hp)).symm hp.1
  · refine Stable.of_nn (V_cover h hK) fun ⟨p, hp⟩ => ?_
    exact nn_intro ⟨some p, @SCode.RootRel.top X.A (code h) p, (exact h hT K p hp).symm⟩

/-- The height of the pullback code is the domain, for an ordinal domain. -/
theorem height_equiv (hT : IsOrd T) : Equiv (code h).height T :=
  (rank_congr (graph_equiv h hT.1)).trans (rank_equiv_of_isOrd hT)

end Pullback

/-! ### Hartogs -/

/-- Every ordinal with an injection relation into `X` is below the universal bound of the carrier
of `X`. The bound is constructed before the injection is opened. -/
theorem mem_univBound_of_injRel {α X : GSet.{u}} (hα : IsOrd α) (h : InjRel α X) :
    Mem α (univBound X.A) :=
  Stable.of_nn h fun ⟨_, hF⟩ =>
    Mem.congr_left (Pullback.height_equiv hF hα) (code_height_mem (Pullback.code hF))

/-- The relational Hartogs bound of `X`: the ordinals with an injection relation into `X`, cut
inside the universal bound. -/
def relHartogs (X : GSet.{u}) : GSet.{u} :=
  sep (fun β => IsOrd β ∧ InjRel β X) (univBound X.A)

theorem mem_relHartogs {X β : GSet.{u}} : Mem β (relHartogs X) ↔ IsOrd β ∧ InjRel β X :=
  (mem_sep (fun β => IsOrd β ∧ InjRel β X) (univBound X.A)
    fun _ _ e h => ⟨h.1.congr e, h.2.congr_left e⟩).trans
    ⟨And.right, fun h => ⟨mem_univBound_of_injRel h.1 h.2, h⟩⟩

theorem isOrd_relHartogs (X : GSet.{u}) : IsOrd (relHartogs X) := by
  refine ⟨fun β hβ γ hγ => ?_, fun β hβ => (mem_relHartogs.1 hβ).1.1⟩
  have ⟨hβo, hβi⟩ := mem_relHartogs.1 hβ
  refine mem_relHartogs.2 ⟨hβo.mem hγ, nn_map (fun ⟨F, hF⟩ => ⟨F, hF.restrict hβo.1 hγ⟩) hβi⟩

/-- **The bound has no injection relation into `X`.** -/
theorem not_injRel_relHartogs (X : GSet.{u}) : ¬ InjRel (relHartogs X) X := fun h =>
  not_mem_self (relHartogs X) (mem_relHartogs.2 ⟨isOrd_relHartogs X, h⟩)

/-- The bound is extensional in `X`: its membership law does not mention the presentation. -/
theorem relHartogs_congr {X X' : GSet.{u}} (e : Equiv X X') : Equiv (relHartogs X) (relHartogs X') :=
  ext fun _ => mem_relHartogs.trans (Iff.trans (and_congr Iff.rfl
    ⟨InjRel.congr_right e, InjRel.congr_right e.symm⟩) mem_relHartogs.symm)

/-! ### The source-wide menu -/

/-- The bounds over the literal members of a domain. -/
def menu (a : GSet.{u}) : GSet.{u} := range fun i : {x : a.A // a.R x a.r} => relHartogs (a.at' i.1)

/-- **The menu.** Every member of `a` has, negatively, an ordinal in the menu with no injection
relation into it. -/
theorem mem_menu {a x : GSet.{u}} (hx : Mem x a) :
    ¬¬∃ y, Mem y (menu a) ∧ IsOrd y ∧ ¬ InjRel y x := by
  refine Stable.of_nn hx fun ⟨i, hi, e⟩ => ?_
  refine nn_intro ⟨relHartogs (a.at' i), (mem_range _).2 (nn_intro ⟨⟨i, hi⟩, Equiv.refl _⟩),
    isOrd_relHartogs _, fun h => not_injRel_relHartogs (a.at' i) (h.congr_right e)⟩

/-- info: 'GSet.Pullback.height_equiv' does not depend on any axioms -/
#guard_msgs in #print axioms Pullback.height_equiv
/-- info: 'GSet.not_injRel_relHartogs' does not depend on any axioms -/
#guard_msgs in #print axioms not_injRel_relHartogs
/-- info: 'GSet.relHartogs_congr' does not depend on any axioms -/
#guard_msgs in #print axioms relHartogs_congr
/-- info: 'GSet.mem_menu' does not depend on any axioms -/
#guard_msgs in #print axioms mem_menu

end GSet
