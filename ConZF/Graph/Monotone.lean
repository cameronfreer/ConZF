import ConZF.Graph.Hartogs
import ConZF.Graph.Names
import ConZF.Graph.Ordinals
/-!
Bounded monotone induction. A subset of a graph set `X` is a stable, extensional predicate on
the points of `X`, the vertices `Pt X` below the root; the operator laws are stated only on
such predicates, so nothing forces a vertex above or beside the root into a subset (the earlier
version demanded that on every vertex predicate, which was contradictory).
For a monotone, inflationary, extensional operator `Φ` on such
subsets and a seed `S`, the history along an ordinal presentation `κ` is the table
`hist Φ S κ : κ.A → Pt X → Prop` solving the uniform recurrence
`A_β = S ∪ ⋃_{ξ<β} Φ(A_ξ)` (`hist_eq`), obtained by predicate recursion on the transitive
closure of `κ`: the history is constructed first, and its laws are proved afterwards. The stages
increase, are extensional, respect equivalent stage vertices (`hist_congr`), stay below every
closed superset of the seed (`hist_sub_closed`), and once a stage is stationary every later
stage equals it (`persist`).

**Convergence.** With `κ := relHartogs (powerset X)`, if no stage below `κ` were stationary the
map from stages to their subset states would be an injection relation from `κ` into the
powerset of `X`, contradicting `not_injRel_relHartogs`; so some stage below `κ` is stationary
(`exists_stationary`). The stopping ordinal is the Separation cut of the nonstationary members
of `κ` (`stopCut`): it is a member of `κ`, stationary, with every earlier stage nonstationary
(`stopCut_spec`). The endpoint `endpoint` is closed under `Φ` and contained in every closed
superset of the seed (`endpoint_closed`, `endpoint_least`). No stationary witness is extracted;
its negative existence proves properties of the already defined cut.

**Instances.** `addOp C` (adjoin a fixed subset) has endpoint `S ∪ C` (`endpoint_addOp`). The
transfinite benchmark is `predOp` on an ordinal `η`: a point is admitted once all its
predecessors are. Its stage `β` is `{x ∈ η : x < β}` (`hist_predOp`), a stage is stationary
exactly when it is not below `η` (`stat_predOp`), so the stopping cut is `η` itself
(`stopCut_predOp`); as a byproduct every ordinal lies in the relational Hartogs bound of its
powerset (`mem_relHartogs_powerset`).
-/
universe u

namespace GSet

section
variable (X : GSet.{u})

/-- The points of `X`: the root predecessors. -/
abbrev Pt : Type u := {a : X.A // X.R a X.r}

/-- A subset of `X`: a predicate on points. -/
abbrev Sub := Pt X → Prop

/-- Extensional predicates: invariant under equivalence of points. -/
def Ext (B : Sub X) : Prop := ∀ a b : Pt X, Equiv (X.at' a.1) (X.at' b.1) → B a → B b

/-- The vertex predicate of a subset, for the powerset presentation. -/
def toPred (B : Sub X) (a : X.A) : Prop := ∃ h : X.R a X.r, B ⟨a, h⟩

instance {B : Sub X} [∀ a, Stable (B a)] : Stable (Ext X B) :=
  inferInstanceAs (Stable (∀ a b, _ → B a → B b))

/-- The hypotheses on the operator. -/
structure IsMono (Φ : Sub X → Sub X) : Prop where
  stable : ∀ B a, Stable (Φ B a)
  ext_iff : ∀ B B', (∀ a, B a ↔ B' a) → ∀ a, Φ B a ↔ Φ B' a
  mono : ∀ B B', (∀ a, B a → B' a) → ∀ a, Φ B a → Φ B' a
  infl : ∀ B a, B a → Φ B a
  ext : ∀ B, Ext X B → Ext X (Φ B)

/-- The hypotheses on the seed. -/
structure IsSeed (S : Sub X) : Prop where
  stable : ∀ a, Stable (S a)
  ext : Ext X S

end

section
variable {X : GSet.{u}} {Φ : Sub X → Sub X} {S : Sub X} (hΦ : IsMono X Φ) (hS : IsSeed X S)
  (κ : GSet.{u})

/-- The step of the recurrence: the seed, or the operator applied to an earlier row. -/
def monoStep (T : κ.A → Sub X) (β : κ.A) (a : Pt X) : Prop :=
  ¬¬(S a ∨ ∃ ξ, Stage κ ξ β ∧ Φ (T ξ) a)

instance {T : κ.A → Sub X} {β : κ.A} {a : Pt X} : Stable (monoStep (Φ := Φ) (S := S) κ T β a) :=
  inferInstanceAs (Stable (¬_))

include hΦ in
theorem monoStep_local (T U : κ.A → Sub X) (β : κ.A)
    (h : ∀ ξ, Stage κ ξ β → ∀ a, T ξ a ↔ U ξ a) (a : Pt X) :
    monoStep (Φ := Φ) (S := S) κ T β a ↔ monoStep (Φ := Φ) (S := S) κ U β a :=
  nn_congr (or_congr Iff.rfl (exists_congr fun ξ => and_congr_right fun hξ =>
    hΦ.ext_iff _ _ (h ξ hξ) a))

/-- **The history**, by predicate recursion along the transitive closure of `κ`. -/
def hist : κ.A → Sub X := Graph.joinedTable (Stage κ) (monoStep (Φ := Φ) (S := S) κ)

instance {β : κ.A} {a : Pt X} : Stable (hist (Φ := Φ) (S := S) κ β a) := inferInstanceAs (Stable (¬_))

/-- A stage is stationary when the operator adds nothing to it. -/
def Stat (β : κ.A) : Prop := ∀ a, Φ (hist (Φ := Φ) (S := S) κ β) a → hist (Φ := Φ) (S := S) κ β a

instance {β : κ.A} : Stable (Stat (Φ := Φ) (S := S) κ β) :=
  inferInstanceAs (Stable (∀ a, _ → hist (Φ := Φ) (S := S) κ β a))

include hΦ

theorem hist_eq (β : κ.A) (a : Pt X) :
    hist (Φ := Φ) (S := S) κ β a ↔ ¬¬(S a ∨ ∃ ξ, Stage κ ξ β ∧ Φ (hist (Φ := Φ) (S := S) κ ξ) a) :=
  Graph.predicate_recursion (Stage κ) (monoStep (Φ := Φ) (S := S) κ) (monoStep_local hΦ κ)
    (fun _ _ _ => inferInstance) (swf_tc κ.swf) (fun h h' => TC.trans h h') (fun _ _ => inferInstance)
    β a

theorem seed_sub_hist (β : κ.A) (a : Pt X) (h : S a) : hist (Φ := Φ) (S := S) κ β a :=
  (hist_eq hΦ κ β a).2 (nn_intro (.inl h))

/-- Stages increase along the stage relation, by inflation. -/
theorem hist_mono {ξ β : κ.A} (h : Stage κ ξ β) (a : Pt X) (ha : hist (Φ := Φ) (S := S) κ ξ a) :
    hist (Φ := Φ) (S := S) κ β a :=
  (hist_eq hΦ κ β a).2 (nn_intro (.inr ⟨ξ, h, hΦ.infl _ a ha⟩))

include hS

/-- Every stage is extensional. -/
theorem hist_ext : ∀ β : κ.A, Ext X (hist (Φ := Φ) (S := S) κ β) := by
  refine swf_tc κ.swf (fun β => Ext X (hist (Φ := Φ) (S := S) κ β)) (fun _ => inferInstance) ?_
  intro β ih a b e ha
  refine (hist_eq hΦ κ β b).2 (nn_map (fun h => ?_) ((hist_eq hΦ κ β a).1 ha))
  rcases h with h | ⟨ξ, hξ, h⟩
  · exact .inl (hS.ext a b e h)
  · exact .inr ⟨ξ, hξ, hΦ.ext _ (ih ξ hξ) a b e h⟩

omit hS in
/-- Every stage is below every closed superset of the seed. -/
theorem hist_sub_closed (Z : Sub X) [∀ a, Stable (Z a)] (hSZ : ∀ a, S a → Z a)
    (hZ : ∀ a, Φ Z a → Z a) : ∀ β : κ.A, ∀ a, hist (Φ := Φ) (S := S) κ β a → Z a := by
  refine swf_tc κ.swf (fun β => ∀ a, hist (Φ := Φ) (S := S) κ β a → Z a) (fun _ => inferInstance) ?_
  intro β ih a ha
  refine Stable.of_nn ((hist_eq hΦ κ β a).1 ha) fun
    | .inl h => hSZ a h
    | .inr ⟨ξ, hξ, h⟩ => hZ a (hΦ.mono _ _ (ih ξ hξ) a h)

omit hS in
/-- Equivalent stage vertices have equal rows: a bisimulation of the rank of `κ` with itself
matches predecessors along the transitive closure. -/
theorem hist_congr_of_bisim {Z : κ.A → κ.A → Prop} (hZ : IsBisim (rank κ) (rank κ) Z) :
    ∀ β β', Z β β' → ∀ a, hist (Φ := Φ) (S := S) κ β a ↔ hist (Φ := Φ) (S := S) κ β' a := by
  refine swf_tc κ.swf (fun β => ∀ β', Z β β' → ∀ a, hist (Φ := Φ) (S := S) κ β a ↔
    hist (Φ := Φ) (S := S) κ β' a) (fun _ => inferInstance) fun β ih β' hββ' a => ?_
  constructor
  · intro ha
    refine (hist_eq hΦ κ β' a).2 (nn_bind ((hist_eq hΦ κ β a).1 ha) fun h => ?_)
    rcases h with h | ⟨ξ, hξ, h⟩
    · exact nn_intro (.inl h)
    · refine nn_map (fun ⟨ξ', hξ', hz⟩ => .inr ⟨ξ', hξ', ?_⟩) (hZ.forth β β' hββ' ξ hξ)
      exact (hΦ.ext_iff _ _ (ih ξ hξ ξ' hz) a).1 h
  · intro ha
    refine (hist_eq hΦ κ β a).2 (nn_bind ((hist_eq hΦ κ β' a).1 ha) fun h => ?_)
    rcases h with h | ⟨ξ', hξ', h⟩
    · exact nn_intro (.inl h)
    · refine nn_map (fun ⟨ξ, hξ, hz⟩ => .inr ⟨ξ, hξ, ?_⟩) (hZ.back β β' hββ' ξ' hξ')
      exact (hΦ.ext_iff _ _ (ih ξ hξ ξ' hz) a).2 h

omit hS in
theorem hist_congr {ξ ξ' : κ.A} (e : Equiv ((rank κ).at' ξ) ((rank κ).at' ξ')) (a : Pt X) :
    hist (Φ := Φ) (S := S) κ ξ a ↔ hist (Φ := Φ) (S := S) κ ξ' a :=
  Stable.of_nn e fun ⟨_, hZ, hr⟩ => hist_congr_of_bisim hΦ κ ⟨hZ.stable, hZ.forth, hZ.back⟩ ξ ξ' hr a

omit hS in
/-- Semantic monotonicity: rows increase along the semantic order of stage vertices. -/
theorem hist_mono_sem {ξ β : κ.A} (h : Mem ((rank κ).at' ξ) ((rank κ).at' β)) (a : Pt X)
    (ha : hist (Φ := Φ) (S := S) κ ξ a) : hist (Φ := Φ) (S := S) κ β a :=
  Stable.of_nn h fun ⟨_, hξ', e⟩ => hist_mono hΦ κ hξ' a ((hist_congr hΦ κ e a).1 ha)

omit hS in
theorem stat_congr {β β' : κ.A} (e : Equiv ((rank κ).at' β) ((rank κ).at' β'))
    (h : Stat (Φ := Φ) (S := S) κ β) : Stat (Φ := Φ) (S := S) κ β' := fun a ha =>
  (hist_congr hΦ κ e a).1 (h a ((hΦ.ext_iff _ _ (fun a => (hist_congr hΦ κ e a).symm) a).1 ha))

omit hS in
/-- **Persistence.** After a stationary stage every later stage is contained in it. -/
theorem persist {β : κ.A} (hst : Stat (Φ := Φ) (S := S) κ β) :
    ∀ δ, Mem ((rank κ).at' β) ((rank κ).at' δ) → ∀ a,
      hist (Φ := Φ) (S := S) κ δ a → hist (Φ := Φ) (S := S) κ β a := by
  refine swf_tc κ.swf (fun δ => Mem ((rank κ).at' β) ((rank κ).at' δ) → ∀ a,
    hist (Φ := Φ) (S := S) κ δ a → hist (Φ := Φ) (S := S) κ β a) (fun _ => inferInstance) ?_
  intro δ ih _ a ha
  refine Stable.of_nn ((hist_eq hΦ κ δ a).1 ha) fun
    | .inl h => seed_sub_hist hΦ κ β a h
    | .inr ⟨ξ, hξ, h⟩ => ?_
  refine Stable.of_nn ((isOrd_rank_at' κ ξ).trichotomy (isOrd_rank_at' κ β)) fun
    | .inl hlt => hst a (hΦ.mono _ _ (hist_mono_sem hΦ κ hlt) a h)
    | .inr (.inl e) => hst a ((hΦ.ext_iff _ _ (fun a => hist_congr hΦ κ e a) a).1 h)
    | .inr (.inr hgt) => hst a (hΦ.mono _ _ (ih ξ hξ hgt) a h)

omit hS in
/-- Stationarity propagates to later stages. -/
theorem stat_of_stat {β δ : κ.A} (hst : Stat (Φ := Φ) (S := S) κ β)
    (h : Mem ((rank κ).at' β) ((rank κ).at' δ)) : Stat (Φ := Φ) (S := S) κ δ := by
  have eq : ∀ a, hist (Φ := Φ) (S := S) κ δ a ↔ hist (Φ := Φ) (S := S) κ β a :=
    fun a => ⟨persist hΦ κ hst δ h a, hist_mono_sem hΦ κ h a⟩
  intro a ha
  exact (eq a).2 (hst a ((hΦ.ext_iff _ _ eq a).1 ha))

end

/-! ### Convergence at the relational Hartogs bound of the powerset -/

section
variable {X : GSet.{u}} {Φ : Sub X → Sub X} {S : Sub X} (hΦ : IsMono X Φ) (hS : IsSeed X S)

/-- The stage presentation: the relational Hartogs bound of the powerset of `X`. -/
abbrev bound : GSet.{u} := relHartogs (powerset X)

include hΦ hS

omit hΦ hS in
/-- A stage vertex denotes an ordinal, so its rank agrees with it. -/
theorem stage_equiv {β : (bound (X := X)).A} (h : (bound (X := X)).R β (bound (X := X)).r) :
    Equiv ((rank (bound (X := X))).at' β) ((bound (X := X)).at' β) :=
  rank_at'_equiv_of_isOrd _ β ((isOrd_relHartogs _).mem (at'_mem h))

/-- **Convergence.** Some stage below the bound is stationary: otherwise the stages would inject
into the powerset. -/
theorem exists_stationary :
    ¬¬∃ β, Stage (bound (X := X)) β (bound (X := X)).r ∧ Stat (Φ := Φ) (S := S) (bound (X := X)) β := by
  intro hn
  have hns : ∀ β, Stage (bound (X := X)) β (bound (X := X)).r →
      ¬ Stat (Φ := Φ) (S := S) (bound (X := X)) β := fun β hβ hst => hn ⟨β, hβ, hst⟩
  refine not_injRel_relHartogs (powerset X) (nn_intro ⟨fun ξ v => ¬¬∃ β : (bound (X := X)).A,
    Stage (bound (X := X)) β (bound (X := X)).r ∧ Equiv ξ ((rank (bound (X := X))).at' β) ∧
    Equiv ((powerset X).at' v)
      ((powerset X).at' (.sub (toPred X (hist (Φ := Φ) (S := S) (bound (X := X)) β)))),
    ⟨fun _ _ => inferInstance, ?_, ?_, ?_, ?_⟩⟩)
  · exact fun e h => nn_map (fun ⟨β, h1, h2, h3⟩ => ⟨β, h1, e.symm.trans h2, h3⟩) h
  · exact fun e h => nn_map (fun ⟨β, h1, h2, h3⟩ => ⟨β, h1, h2, e.symm.trans h3⟩) h
  · intro ξ hξ
    refine Stable.of_nn hξ fun ⟨β, hβ, e⟩ => ?_
    exact nn_intro ⟨.sub (toPred X (hist (Φ := Φ) (S := S) (bound (X := X)) β)), PowRel.top _,
      nn_intro ⟨β, TC.of_rel hβ, e.trans (stage_equiv hβ).symm, Equiv.refl _⟩⟩
  · intro ξ ξ' v _ _ h1 h2
    refine Stable.of_nn h1 fun ⟨β, hβ, e, ev⟩ => Stable.of_nn h2 fun ⟨β', hβ', e', ev'⟩ => ?_
    -- the two rows are equal
    have rows : ∀ a, hist (Φ := Φ) (S := S) (bound (X := X)) β a ↔
        hist (Φ := Φ) (S := S) (bound (X := X)) β' a := by
      intro a
      constructor
      · intro ha
        have hm : Mem (X.at' a.1)
            ((powerset X).at' (.sub (toPred X (hist (Φ := Φ) (S := S) (bound (X := X)) β')))) :=
          Mem.congr_right (ev.symm.trans ev') ((mem_powerset_sub X).2
            (nn_intro ⟨a.1, a.2, ⟨a.2, ha⟩, Equiv.refl _⟩))
        exact Stable.of_nn ((mem_powerset_sub X).1 hm) fun ⟨a'', _, ⟨h'', hB''⟩, e''⟩ =>
          hist_ext hΦ hS (bound (X := X)) β' ⟨a'', h''⟩ a e''.symm hB''
      · intro ha
        have hm : Mem (X.at' a.1)
            ((powerset X).at' (.sub (toPred X (hist (Φ := Φ) (S := S) (bound (X := X)) β)))) :=
          Mem.congr_right (ev'.symm.trans ev) ((mem_powerset_sub X).2
            (nn_intro ⟨a.1, a.2, ⟨a.2, ha⟩, Equiv.refl _⟩))
        exact Stable.of_nn ((mem_powerset_sub X).1 hm) fun ⟨a'', _, ⟨h'', hB''⟩, e''⟩ =>
          hist_ext hΦ hS (bound (X := X)) β ⟨a'', h''⟩ a e''.symm hB''
    -- a strictly earlier stage would be stationary
    have key : ∀ {β β' : (bound (X := X)).A}, Stage (bound (X := X)) β (bound (X := X)).r →
        (∀ a, hist (Φ := Φ) (S := S) (bound (X := X)) β a ↔ hist (Φ := Φ) (S := S) (bound (X := X)) β' a) →
        Mem ((rank (bound (X := X))).at' β) ((rank (bound (X := X))).at' β') → False := fun {β β'} hβ rows hlt =>
      hns β hβ fun a ha => (rows a).2 (Stable.of_nn hlt fun ⟨β'', hβ'', e''⟩ =>
        (hist_eq hΦ (bound (X := X)) β' a).2 (nn_intro (.inr ⟨β'', hβ'',
          (hΦ.ext_iff _ _ (fun a => hist_congr hΦ (bound (X := X)) e'' a) a).1 ha⟩)))
    refine Stable.of_nn ((isOrd_rank_at' (bound (X := X)) β).trichotomy (isOrd_rank_at' (bound (X := X)) β')) fun
      | .inl hlt => (key hβ rows hlt).elim
      | .inr (.inl e'') => e.trans (e''.trans e'.symm)
      | .inr (.inr hgt) => (key hβ' (fun a => (rows a).symm) hgt).elim

/-- Stationarity of a member of the bound, through all its stage vertices. -/
def StatSet (ξ : GSet.{u}) : Prop :=
  ∀ β : (bound (X := X)).A, Equiv ξ ((rank (bound (X := X))).at' β) →
    Stat (Φ := Φ) (S := S) (bound (X := X)) β

instance {ξ : GSet.{u}} : Stable (StatSet (Φ := Φ) (S := S) ξ) :=
  inferInstanceAs (Stable (∀ β : (bound (X := X)).A, _ → Stat (Φ := Φ) (S := S) _ β))

/-- **The stopping cut**: the nonstationary members of the bound. -/
def stopCut : GSet.{u} := sep (fun ξ => ¬ StatSet (Φ := Φ) (S := S) ξ) (bound (X := X))

omit hΦ hS in
theorem mem_stopCut {ξ : GSet.{u}} :
    Mem ξ (stopCut (Φ := Φ) (S := S)) ↔ Mem ξ (bound (X := X)) ∧ ¬ StatSet (Φ := Φ) (S := S) ξ :=
  mem_sep _ _ fun _ _ e h hs => h fun β e' => hs β (e.symm.trans e')

omit hΦ hS in
theorem statSet_congr {ξ ξ' : GSet.{u}} (e : Equiv ξ ξ') (h : StatSet (Φ := Φ) (S := S) ξ) :
    StatSet (Φ := Φ) (S := S) ξ' := fun β e' => h β (e.trans e')

omit hS in
/-- Stationarity of a member propagates to later members. -/
theorem statSet_of_mem {ξ ξ' : GSet.{u}} (h : StatSet (Φ := Φ) (S := S) ξ) (hm : Mem ξ ξ') :
    StatSet (Φ := Φ) (S := S) ξ' := by
  intro β e
  refine Stable.of_nn (Mem.congr_right e hm) fun ⟨β'', hβ'', e''⟩ => ?_
  exact stat_of_stat hΦ _ (h β'' e'') (at'_mem (G := (rank (bound (X := X))).at' β) hβ'')

omit hS in
theorem isOrd_stopCut : IsOrd (stopCut (Φ := Φ) (S := S)) := by
  refine ⟨fun ξ hξ ξ' hξ' => ?_, fun ξ hξ => ((isOrd_relHartogs _).mem (mem_stopCut.1 hξ).1).1⟩
  have ⟨hξb, hns⟩ := mem_stopCut.1 hξ
  exact mem_stopCut.2 ⟨(isOrd_relHartogs _).1 ξ hξb ξ' hξ', fun hs => hns (statSet_of_mem hΦ hs hξ')⟩

/-- The stopping cut is a member of the bound: it lies below any stationary stage. -/
theorem stopCut_mem : Mem (stopCut (Φ := Φ) (S := S)) (bound (X := X)) := by
  refine Stable.of_nn (exists_stationary hΦ hS) fun ⟨β, hβ, hst⟩ => ?_
  have hβm : Mem ((rank (bound (X := X))).at' β) (bound (X := X)) :=
    Mem.congr_right (rank_equiv_of_isOrd (isOrd_relHartogs _)) (at'_mem (G := rank (bound (X := X))) hβ)
  have sub : Subset (stopCut (Φ := Φ) (S := S)) ((rank (bound (X := X))).at' β) := fun ξ hξ => by
    have ⟨hξb, hns⟩ := mem_stopCut.1 hξ
    have hξo : IsOrd ξ := (isOrd_relHartogs _).mem hξb
    refine Stable.of_nn (hξo.trichotomy (isOrd_rank_at' _ β)) fun
      | .inl h => h
      | .inr (.inl e) => (hns fun _ e' => stat_congr hΦ _ (e.symm.trans e') hst).elim
      | .inr (.inr h) => (hns fun _ e₂ => stat_of_stat hΦ _ hst (Mem.congr_right e₂ h)).elim
  refine Stable.of_nn ((isOrd_stopCut hΦ).subset (isOrd_rank_at' _ β) sub) fun
    | .inl h => (isOrd_relHartogs _).1 _ hβm _ h
    | .inr e => Mem.congr_left e.symm hβm

/-- **The stopping cut is stationary**, and every earlier member is not. -/
theorem statSet_stopCut : StatSet (Φ := Φ) (S := S) (stopCut (Φ := Φ) (S := S)) :=
  Stable.dne fun hn => not_mem_self _ (mem_stopCut.2 ⟨stopCut_mem hΦ hS, hn⟩)

omit hΦ hS in
theorem not_statSet_of_mem_stopCut {ξ : GSet.{u}} (h : Mem ξ (stopCut (Φ := Φ) (S := S))) :
    ¬ StatSet (Φ := Φ) (S := S) ξ := (mem_stopCut.1 h).2

/-- **The endpoint**: the row at any stage vertex denoting the stopping cut. -/
def endpoint (a : Pt X) : Prop :=
  ¬¬∃ β, Stage (bound (X := X)) β (bound (X := X)).r ∧
    Equiv (stopCut (Φ := Φ) (S := S)) ((rank (bound (X := X))).at' β) ∧
    hist (Φ := Φ) (S := S) (bound (X := X)) β a

instance {a : Pt X} : Stable (endpoint (Φ := Φ) (S := S) a) := inferInstanceAs (Stable (¬_))

omit hS in
theorem endpoint_row {β : (bound (X := X)).A} (hβ : Stage (bound (X := X)) β (bound (X := X)).r)
    (e : Equiv (stopCut (Φ := Φ) (S := S)) ((rank (bound (X := X))).at' β)) (a : Pt X) :
    endpoint (Φ := Φ) (S := S) a ↔ hist (Φ := Φ) (S := S) (bound (X := X)) β a :=
  ⟨fun h => Stable.of_nn h fun ⟨_, _, e', ha⟩ => (hist_congr hΦ _ (e'.symm.trans e) a).1 ha,
   fun ha => nn_intro ⟨β, hβ, e, ha⟩⟩

/-- The endpoint is closed under the operator. -/
theorem endpoint_closed (a : Pt X) (h : Φ (endpoint (Φ := Φ) (S := S)) a) :
    endpoint (Φ := Φ) (S := S) a := by
  refine Stable.of_nn (stopCut_mem hΦ hS) fun ⟨β, hβ, e⟩ => ?_
  have e' : Equiv (stopCut (Φ := Φ) (S := S)) ((rank (bound (X := X))).at' β) :=
    e.trans (stage_equiv hβ).symm
  have hst := statSet_stopCut hΦ hS β e'
  refine nn_intro ⟨β, TC.of_rel hβ, e', hst a ?_⟩
  exact (hΦ.ext_iff _ _ (fun a => endpoint_row hΦ (TC.of_rel hβ) e' a) a).1 h

omit hS in
/-- The endpoint is contained in every closed superset of the seed. -/
theorem endpoint_least (Z : Sub X) [∀ a, Stable (Z a)] (hSZ : ∀ a, S a → Z a)
    (hZ : ∀ a, Φ Z a → Z a) (a : Pt X) (h : endpoint (Φ := Φ) (S := S) a) : Z a :=
  Stable.of_nn h fun ⟨β, _, _, ha⟩ => hist_sub_closed hΦ _ Z hSZ hZ β a ha

theorem seed_sub_endpoint (a : Pt X) (h : S a) : endpoint (Φ := Φ) (S := S) a :=
  Stable.of_nn (stopCut_mem hΦ hS) fun ⟨β, hβ, e⟩ =>
    nn_intro ⟨β, TC.of_rel hβ, e.trans (stage_equiv hβ).symm, seed_sub_hist hΦ _ β a h⟩

end

/-! ### Instances -/

section
variable {X : GSet.{u}} {S : Sub X} (C : Sub X)

/-- Adjoin a fixed subset: `Φ B = B ∪ C`. -/
def addOp (B : Sub X) (a : Pt X) : Prop := ¬¬(B a ∨ C a)

theorem isMono_addOp (hC : IsSeed X C) : IsMono X (addOp C) where
  stable _ _ := inferInstanceAs (Stable (¬_))
  ext_iff _ _ h a := nn_congr (or_congr (h a) Iff.rfl)
  mono _ _ h a := nn_map fun
    | .inl hb => .inl (h a hb)
    | .inr hc => .inr hc
  infl _ _ h := nn_intro (.inl h)
  ext _ hB a b e := nn_map fun
    | .inl hb => .inl (hB a b e hb)
    | .inr hc => .inr (hC.ext a b e hc)

/-- The endpoint of `addOp C` from seed `S` is `S ∪ C`. -/
theorem endpoint_addOp (hC : IsSeed X C) (hS : IsSeed X S) (a : Pt X) :
    endpoint (Φ := addOp C) (S := S) a ↔ ¬¬(S a ∨ C a) := by
  constructor
  · exact endpoint_least (isMono_addOp C hC) (fun a => ¬¬(S a ∨ C a)) (fun a h => nn_intro (.inl h))
      (fun a h => nn_bind h fun
        | .inl h => h
        | .inr h => nn_intro (.inr h)) a
  · refine fun h => Stable.of_nn h fun
      | .inl h => seed_sub_endpoint (isMono_addOp C hC) hS a h
      | .inr h => endpoint_closed (isMono_addOp C hC) hS a (nn_intro (.inr h))

end

/-! ### The transfinite benchmark: admit a point once all its predecessors are admitted -/

section
variable {η : GSet.{u}}

/-- The empty seed. -/
def emptySeed : Sub η := fun _ => False

theorem isSeed_emptySeed : IsSeed η (emptySeed (η := η)) :=
  ⟨fun _ => inferInstanceAs (Stable False), fun _ _ _ h => h⟩

/-- The predecessor rule: a point is admitted once every point below it is. -/
def predOp (B : Sub η) (x : Pt η) : Prop :=
  ¬¬(B x ∨ ∀ z : Pt η, Mem (η.at' z.1) (η.at' x.1) → B z)

theorem isMono_predOp : IsMono η (predOp (η := η)) where
  stable _ _ := inferInstanceAs (Stable (¬_))
  ext_iff _ _ h x := nn_congr (or_congr (h x) (forall_congr' fun z => imp_congr_right fun _ => h z))
  mono _ _ h x := nn_map fun
    | .inl hb => .inl (h x hb)
    | .inr hp => .inr fun z hz => h z (hp z hz)
  infl _ _ h := nn_intro (.inl h)
  ext _ hB a b e := nn_map fun
    | .inl hb => .inl (hB a b e hb)
    | .inr hp => .inr fun z hz => hp z (Mem.congr_right e.symm hz)

variable (hη : IsOrd η)

include hη

omit hη in
/-- A point of `η` that is a member of another point is, negatively, a point below it. -/
theorem pt_of_mem (hη : IsOrd η) {x : Pt η} {K : GSet.{u}} (hK : Mem K (η.at' x.1)) :
    ¬¬∃ z : Pt η, Equiv K (η.at' z.1) ∧ Mem (η.at' z.1) (η.at' x.1) :=
  nn_map (fun ⟨z, hz, e⟩ => ⟨⟨z, hz⟩, e, Mem.congr_left e hK⟩) (hη.1 _ (at'_mem x.2) K hK)

/-- **The stages of the benchmark:** stage `β` is `{x ∈ η : x < β}`. -/
theorem hist_predOp : ∀ β : (bound (X := η)).A, ∀ x : Pt η,
    hist (Φ := predOp) (S := emptySeed) (bound (X := η)) β x ↔ Mem (η.at' x.1) ((rank (bound (X := η))).at' β) := by
  refine swf_tc (bound (X := η)).swf (fun β => ∀ x : Pt η, hist (Φ := predOp) (S := emptySeed) (bound (X := η)) β x ↔
    Mem (η.at' x.1) ((rank (bound (X := η))).at' β)) (fun _ => inferInstance) fun β ih x => ?_
  have hx : IsOrd (η.at' x.1) := hη.mem (at'_mem x.2)
  constructor
  · intro ha
    refine Stable.of_nn ((hist_eq isMono_predOp (bound (X := η)) β x).1 ha) fun
      | .inl h => h.elim
      | .inr ⟨ξ, hξ, h⟩ => ?_
    have hξm : Mem ((rank (bound (X := η))).at' ξ) ((rank (bound (X := η))).at' β) := at'_mem (G := (rank (bound (X := η))).at' β) hξ
    refine Stable.of_nn h fun
      | .inl h => trans_rank_at' (bound (X := η)) β _ hξm _ ((ih ξ hξ x).1 h)
      | .inr hp => ?_
    refine Stable.of_nn (hx.trichotomy (isOrd_rank_at' (bound (X := η)) ξ)) fun
      | .inl hlt => trans_rank_at' (bound (X := η)) β _ hξm _ hlt
      | .inr (.inl e) => Mem.congr_left e.symm hξm
      | .inr (.inr hgt) => ?_
    refine Stable.of_nn (pt_of_mem hη hgt) fun ⟨z, e, hz⟩ => ?_
    exact (not_mem_self _ (Mem.congr_left e.symm ((ih ξ hξ z).1 (hp z hz)))).elim
  · intro hm
    refine Stable.of_nn hm fun ⟨ξ, hξ, e⟩ => ?_
    exact (hist_eq isMono_predOp (bound (X := η)) β x).2 (nn_intro (.inr ⟨ξ, hξ,
      nn_intro (.inr fun z hz => (ih ξ hξ z).2 (Mem.congr_right e hz))⟩))

/-- **Stationarity in the benchmark:** stage `β` is stationary exactly when `β` is not below
`η`. -/
theorem stat_predOp (β : (bound (X := η)).A) :
    Stat (Φ := predOp (η := η)) (S := emptySeed (η := η)) (bound (X := η)) β ↔ ¬ Mem ((rank (bound (X := η))).at' β) η := by
  constructor
  · intro hst hm
    refine Stable.of_nn hm fun ⟨x, hx, e⟩ => ?_
    have h : predOp (hist (Φ := predOp) (S := emptySeed) (bound (X := η)) β) ⟨x, hx⟩ :=
      nn_intro (.inr fun z hz => (hist_predOp hη β z).2 (Mem.congr_right e.symm hz))
    exact not_mem_self _ (Mem.congr_right e ((hist_predOp hη β ⟨x, hx⟩).1 (hst _ h)))
  · intro hn x h
    refine (hist_predOp hη β x).2 (Stable.of_nn h fun
      | .inl h => (hist_predOp hη β x).1 h
      | .inr hp => ?_)
    have hx : IsOrd (η.at' x.1) := hη.mem (at'_mem x.2)
    refine Stable.of_nn (hx.trichotomy (isOrd_rank_at' (bound (X := η)) β)) fun
      | .inl hlt => hlt
      | .inr (.inl e) => (hn (Mem.congr_left e (at'_mem x.2))).elim
      | .inr (.inr hgt) => (hn (hη.1 _ (at'_mem x.2) _ hgt)).elim

/-- **The benchmark:** the first stationary stage is `η` itself. -/
theorem stopCut_predOp : Equiv (stopCut (Φ := predOp) (S := emptySeed (η := η))) η := by
  have hκ := isOrd_relHartogs (powerset η)
  have hcut := stopCut_mem isMono_predOp isSeed_emptySeed (X := η)
  refine ext fun K => ⟨fun hK => ?_, fun hK => ?_⟩
  · have ⟨hKb, hns⟩ := mem_stopCut.1 hK
    refine Stable.of_nn hKb fun ⟨β, hβ, e⟩ => ?_
    have e' : Equiv K ((rank (bound (X := η))).at' β) := e.trans (stage_equiv hβ).symm
    have hst : ¬ Stat (Φ := predOp (η := η)) (S := emptySeed (η := η)) (bound (X := η)) β :=
      fun hst =>
      hns fun β' e'' => stat_congr isMono_predOp (bound (X := η)) (e'.symm.trans e'') hst
    exact Mem.congr_left e'.symm (Stable.dne fun h => hst ((stat_predOp hη β).2 h))
  · have hKo : IsOrd K := hη.mem hK
    -- every member of `η` is a member of the bound: it lies below the stationary stopping cut
    have hKb : Mem K (bound (X := η)) := by
      refine Stable.of_nn hcut fun ⟨β₀, hβ₀, e₀⟩ => ?_
      have e₀' : Equiv (stopCut (Φ := predOp) (S := emptySeed (η := η)))
          ((rank (bound (X := η))).at' β₀) := e₀.trans (stage_equiv hβ₀).symm
      have hst := (stat_predOp hη β₀).1 (statSet_stopCut isMono_predOp isSeed_emptySeed β₀ e₀')
      have hβm : Mem ((rank (bound (X := η))).at' β₀) (bound (X := η)) :=
        Mem.congr_left (stage_equiv hβ₀).symm (at'_mem hβ₀)
      refine Stable.of_nn (hKo.trichotomy (isOrd_rank_at' (bound (X := η)) β₀)) fun
        | .inl hlt => hκ.1 _ hβm K hlt
        | .inr (.inl e) => (hst (Mem.congr_left e hK)).elim
        | .inr (.inr hgt) => (hst (hη.1 K hK _ hgt)).elim
    refine mem_stopCut.2 ⟨hKb, fun hs => ?_⟩
    refine Stable.of_nn hKb fun ⟨β, hβ, e⟩ => ?_
    have e' : Equiv K ((rank (bound (X := η))).at' β) := e.trans (stage_equiv hβ).symm
    exact (stat_predOp hη β).1 (hs β e') (Mem.congr_left e' hK)

/-- Every ordinal is a member of the relational Hartogs bound of its powerset. -/
theorem mem_relHartogs_powerset : Mem η (relHartogs (powerset η)) :=
  Mem.congr_left (stopCut_predOp hη) (stopCut_mem isMono_predOp isSeed_emptySeed)

/-- The endpoint of the benchmark is all of `η`. -/
theorem endpoint_predOp (x : Pt η) : endpoint (Φ := predOp) (S := emptySeed (η := η)) x :=
  Stable.of_nn (stopCut_mem isMono_predOp isSeed_emptySeed (X := η)) fun ⟨β, hβ, e⟩ =>
    have e' : Equiv (stopCut (Φ := predOp) (S := emptySeed (η := η)))
        ((rank (bound (X := η))).at' β) := e.trans (stage_equiv hβ).symm
    nn_intro ⟨β, TC.of_rel hβ, e', (hist_predOp hη β x).2
      (Mem.congr_right ((stopCut_predOp hη).symm.trans e') (at'_mem x.2))⟩

end

/-- info: 'GSet.exists_stationary' does not depend on any axioms -/
#guard_msgs in #print axioms exists_stationary
/-- info: 'GSet.statSet_stopCut' does not depend on any axioms -/
#guard_msgs in #print axioms statSet_stopCut
/-- info: 'GSet.endpoint_closed' does not depend on any axioms -/
#guard_msgs in #print axioms endpoint_closed
/-- info: 'GSet.endpoint_least' does not depend on any axioms -/
#guard_msgs in #print axioms endpoint_least
/-- info: 'GSet.endpoint_addOp' does not depend on any axioms -/
#guard_msgs in #print axioms endpoint_addOp
/-- info: 'GSet.stopCut_predOp' does not depend on any axioms -/
#guard_msgs in #print axioms stopCut_predOp
/-- info: 'GSet.mem_relHartogs_powerset' does not depend on any axioms -/
#guard_msgs in #print axioms mem_relHartogs_powerset
/-- info: 'GSet.endpoint_predOp' does not depend on any axioms -/
#guard_msgs in #print axioms endpoint_predOp

end GSet
