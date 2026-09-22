import ConZF.Graph.Def
import ConZF.Graph.Ord
/-!
Names for the constructible hierarchy on a fixed carrier. Over an ordinal presentation `α`, with
stage relation the transitive closure `TC α.R` (stable and transitive), a *name* is a finite tree
`def' a φ n args`: a birth stage `a`, a formula, and finitely many earlier names as parameters.
Validity (`Valid`) asks for `Bound (n+1) φ` and, for each argument, validity and birth strictly
below `a`. All names exist before any is interpreted.

For any proposed table `T : Name → Name → Prop` (`T d c`: the name `c` denotes a member of the
set named by `d`), the *earlier-stage graph* `stageGraph α T b` on `Option (Name α.A)` has the
valid names born below `b` under its root, and a name edge `c → d` only when both are valid,
`c` is born below `d`, `d` is born below `b`, and `T d c` holds negatively. Every name edge
decreases the birth stage, so this graph has stable well-founded induction for every table
(`swf_stageRel`). The step operator (`step`) evaluates the formula of `d` over the earlier-stage
graph at the birth of `d`; it is stable and predecessor-local (`step_local`): agreement of two
tables on the rows of names born below `d` gives equivalent earlier-stage graphs at every
vertex, hence equal satisfaction. Predicate recursion then supplies the solved table `table α`
(`table_eq`). The hierarchy graph `hier α` on `Name α.A ⊕ α.A` uses the solved table for name
edges and puts the names born below `a` under the level vertex `inr a`; `L α a` is that graph
at `inr a`.
-/
universe u

namespace GSet
open PSet.Fml

instance {p : Prop} [Decidable p] : Stable p :=
  ⟨fun h => match (inferInstance : Decidable p) with
    | .isTrue hp => hp
    | .isFalse hn => (h hn).elim⟩

theorem bound_stable : ∀ (k : Nat) (φ : PSet.Fml), Stable (Bound k φ)
  | _, .mem _ _ => inferInstanceAs (Stable (_ ∧ _))
  | _, .eq _ _ => inferInstanceAs (Stable (_ ∧ _))
  | _, .fls => inferInstanceAs (Stable True)
  | k, .imp φ ψ =>
    have := bound_stable k φ
    have := bound_stable k ψ
    inferInstanceAs (Stable (Bound k φ ∧ Bound k ψ))
  | k, .all φ => bound_stable (k+1) φ

instance {k : Nat} {φ : PSet.Fml} : Stable (Bound k φ) := bound_stable k φ

/-- Bounds are decidable, so concrete bounds are proved by `decide`. -/
def decBound : ∀ (k : Nat) (φ : PSet.Fml), Decidable (Bound k φ)
  | _, .mem _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | _, .eq _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | _, .fls => inferInstanceAs (Decidable True)
  | k, .imp φ ψ =>
    have := decBound k φ
    have := decBound k ψ
    inferInstanceAs (Decidable (Bound k φ ∧ Bound k ψ))
  | k, .all φ => decBound (k+1) φ

instance {k : Nat} {φ : PSet.Fml} : Decidable (Bound k φ) := decBound k φ

/-- Two graphs on the same carrier with equivalent edge relations are equivalent at every vertex. -/
theorem equiv_of_rel_iff {A : Type u} {R R' : A → A → Prop} {h : Graph.SWF R} {h' : Graph.SWF R'}
    (e : ∀ a b, R a b ↔ R' a b) (x : A) :
    Equiv (⟨A, R, x, h⟩ : GSet.{u}) ⟨A, R', x, h'⟩ :=
  nn_intro ⟨fun a b => ¬¬(a = b), ⟨fun _ _ => inferInstance,
    fun _ _ hab a' ha' => Stable.of_nn hab fun e' => nn_intro ⟨a', e' ▸ (e _ _).1 ha', nn_intro rfl⟩,
    fun _ _ hab b' hb' => Stable.of_nn hab fun e' => nn_intro ⟨b', e' ▸ (e _ _).2 hb', nn_intro rfl⟩⟩,
    nn_intro rfl⟩

/-! ### Names -/

/-- Finite names: a birth stage, a formula, and finitely many earlier names. -/
inductive Name (A : Type u) : Type u
  | def' (a : A) (φ : PSet.Fml) (n : Nat) (args : Fin n → Name A)

namespace Name
variable {A : Type u}

def birth : Name A → A
  | def' a _ _ _ => a

def fml : Name A → PSet.Fml
  | def' _ φ _ _ => φ

def arity : Name A → Nat
  | def' _ _ n _ => n

def args : (t : Name A) → Fin t.arity → Name A
  | def' _ _ _ args => args

end Name

section
variable (α : GSet.{u})

/-- The stage relation: the transitive closure of the presentation's edges. -/
abbrev Stage (a b : α.A) : Prop := TC α.R a b

/-- Validity: bounded free variables, and valid arguments born strictly earlier. -/
def Valid : Name α.A → Prop
  | .def' a φ n args => Bound (n+1) φ ∧ ∀ i, Valid (args i) ∧ Stage α (args i).birth a

theorem valid_stable : ∀ t : Name α.A, Stable (Valid α t)
  | .def' a φ n args =>
    have : ∀ i, Stable (Valid α (args i)) := fun i => valid_stable (args i)
    inferInstanceAs (Stable (Bound (n+1) φ ∧ ∀ i, Valid α (args i) ∧ Stage α _ a))

instance {t : Name α.A} : Stable (Valid α t) := valid_stable α t

/-- Birth descent between names, the relation of the table recursion. -/
def NameRel (c d : Name α.A) : Prop := Stage α c.birth d.birth

instance {c d : Name α.A} : Stable (NameRel α c d) := inferInstanceAs (Stable (TC _ _ _))

theorem swf_nameRel : Graph.SWF (NameRel α) := by
  intro P hs H
  have key : ∀ a, ∀ c : Name α.A, c.birth = a → P c := by
    refine swf_tc α.swf (fun a => ∀ c : Name α.A, c.birth = a → P c) (fun _ => inferInstance) ?_
    intro a ih c hc
    exact H c fun c' hc' => ih c'.birth (hc ▸ hc') c' rfl
  exact fun c => key c.birth c rfl

/-! ### Earlier-stage graphs of a proposed table -/

/-- Tables: `T d c` says the name `c` denotes a member of the set named by `d`. -/
abbrev NTable := Name α.A → Name α.A → Prop

variable (T : NTable α) (b : α.A)

/-- Edges of the earlier-stage graph at `b`: name edges by the table, gated by validity and birth
descent below `b`; the valid names born below `b` under the root. -/
inductive StageRel : Option (Name α.A) → Option (Name α.A) → Prop
  | name {c d : Name α.A} : Valid α c → Valid α d → Stage α c.birth d.birth → Stage α d.birth b →
      ¬¬T d c → StageRel (some c) (some d)
  | root {c : Name α.A} : Valid α c → Stage α c.birth b → StageRel (some c) none

theorem stageRel_some {d : Name α.A} {x} (h : StageRel α T b x (some d)) :
    ∃ c, Valid α c ∧ Valid α d ∧ Stage α c.birth d.birth ∧ Stage α d.birth b ∧ ¬¬T d c ∧
      x = some c := by
  cases h with
  | name hc hd hcd hdb ht => exact ⟨_, hc, hd, hcd, hdb, ht, rfl⟩

theorem stageRel_none {x} (h : StageRel α T b x none) :
    ∃ c, Valid α c ∧ Stage α c.birth b ∧ x = some c := by
  cases h with
  | root hc hcb => exact ⟨_, hc, hcb, rfl⟩

/-- Stable well-founded induction, for every proposed table: name edges decrease the birth. -/
theorem swf_stageRel : Graph.SWF (StageRel α T b) := by
  intro P hs H
  have names : ∀ c : Name α.A, P (some c) := by
    refine swf_nameRel α (fun c => P (some c)) (fun _ => hs _) fun c ih => H _ fun x hx => ?_
    obtain ⟨c', _, _, hcd, _, _, rfl⟩ := stageRel_some α T b hx
    exact ih c' hcd
  intro x
  cases x with
  | some c => exact names c
  | none => exact H _ fun x hx => by obtain ⟨c, _, _, rfl⟩ := stageRel_none α T b hx; exact names c

/-- The earlier-stage graph at `b`, for the table `T`. -/
def stageGraph : GSet.{u} := ⟨Option (Name α.A), StageRel α T b, none, swf_stageRel α T b⟩

/-- The environment of a name's arguments, read in a graph on `Option (Name α.A)`. -/
def argEnv (M : GSet.{u}) (f : Name α.A → M.A) (t : Name α.A) : Nat → GSet.{u} := fun i =>
  if h : i < t.arity then M.at' (f (t.args ⟨i, h⟩)) else M

/-- The step operator: `c` is a member of the set named by `d` when it is valid, born below `d`,
and satisfies the formula of `d` over the earlier-stage graph at the birth of `d`. -/
def step (T : NTable α) (d c : Name α.A) : Prop :=
  Valid α d ∧ Valid α c ∧ Stage α c.birth d.birth ∧
    Sat (Mem · (stageGraph α T d.birth)) d.fml
      (Env.cons ((stageGraph α T d.birth).at' (some c)) (argEnv α (stageGraph α T d.birth) some d))

instance {T : NTable α} {d c : Name α.A} : Stable (step α T d c) :=
  inferInstanceAs (Stable (_ ∧ _ ∧ _ ∧ _))

end

/-! ### Locality -/

section
variable (α : GSet.{u})

/-- Tables agreeing on the rows of names born below `b` give equivalent earlier-stage graphs at
`b`, at every vertex. -/
theorem stageGraph_congr {T U : NTable α} {b : α.A}
    (h : ∀ d, Stage α d.birth b → ∀ c, T d c ↔ U d c) (x : Option (Name α.A)) :
    Equiv ((stageGraph α T b).at' x) ((stageGraph α U b).at' x) := by
  refine equiv_of_rel_iff (h := swf_stageRel α T b) (h' := swf_stageRel α U b) (fun y z => ?_) x
  constructor
  · intro hyz
    cases hyz with
    | name hc hd hcd hdb ht => exact .name hc hd hcd hdb (nn_map (h _ hdb _).1 ht)
    | root hc hcb => exact .root hc hcb
  · intro hyz
    cases hyz with
    | name hc hd hcd hdb ht => exact .name hc hd hcd hdb (nn_map (h _ hdb _).2 ht)
    | root hc hcb => exact .root hc hcb

/-- **Locality.** The step at `d` depends only on the rows of names born below `d`. -/
theorem step_local (T U : NTable α) (d : Name α.A)
    (h : ∀ d', NameRel α d' d → ∀ c, T d' c ↔ U d' c) (c : Name α.A) :
    step α T d c ↔ step α U d c := by
  have e := stageGraph_congr α (T := T) (U := U) (b := d.birth) h
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  refine Sat.resp_iff (fun K => mem_congr_right (e none)) d.fml ?_
  intro i
  cases i with
  | zero => exact e (some c)
  | succ i =>
    show Equiv (argEnv α (stageGraph α T d.birth) some d i)
      (argEnv α (stageGraph α U d.birth) some d i)
    unfold argEnv
    split
    · exact e _
    · exact e none

/-- **The solved table**, by predicate recursion. -/
def table : NTable α := Graph.joinedTable (NameRel α) (step α)

theorem table_eq : ∀ d c, table α d c ↔ step α (table α) d c :=
  Graph.predicate_recursion (NameRel α) (step α) (step_local α) (fun _ _ _ => inferInstance)
    (swf_nameRel α) (fun h h' => TC.trans h h') (fun _ _ => inferInstance)

instance {d c : Name α.A} : Stable (table α d c) := inferInstanceAs (Stable (¬_))

/-! ### The hierarchy graph -/

/-- Edges of the hierarchy: name edges by the solved table, and the names born below `a` under
the level vertex `a`. -/
inductive HierRel : Name α.A ⊕ α.A → Name α.A ⊕ α.A → Prop
  | name {c d : Name α.A} : Valid α c → Valid α d → Stage α c.birth d.birth → ¬¬table α d c →
      HierRel (.inl c) (.inl d)
  | lev {c : Name α.A} {a : α.A} : Valid α c → Stage α c.birth a → HierRel (.inl c) (.inr a)

theorem hierRel_inl {d : Name α.A} {x} (h : HierRel α x (.inl d)) :
    ∃ c, Valid α c ∧ Valid α d ∧ Stage α c.birth d.birth ∧ ¬¬table α d c ∧ x = .inl c := by
  cases h with
  | name hc hd hcd ht => exact ⟨_, hc, hd, hcd, ht, rfl⟩

theorem hierRel_inr {a : α.A} {x} (h : HierRel α x (.inr a)) :
    ∃ c, Valid α c ∧ Stage α c.birth a ∧ x = .inl c := by
  cases h with
  | lev hc hca => exact ⟨_, hc, hca, rfl⟩

theorem swf_hierRel : Graph.SWF (HierRel α) := by
  intro P hs H
  have names : ∀ c : Name α.A, P (.inl c) := by
    refine swf_nameRel α (fun c => P (.inl c)) (fun _ => hs _) fun c ih => H _ fun x hx => ?_
    obtain ⟨c', _, _, hcd, _, rfl⟩ := hierRel_inl α hx
    exact ih c' hcd
  intro x
  cases x with
  | inl c => exact names c
  | inr a => exact H _ fun x hx => by obtain ⟨c, _, _, rfl⟩ := hierRel_inr α hx; exact names c

/-- The hierarchy graph, rooted (arbitrarily) at the level of the presentation's root. -/
def hier : GSet.{u} := ⟨Name α.A ⊕ α.A, HierRel α, .inr α.r, swf_hierRel α⟩

/-- The constructible level at the stage `a`. -/
def L (a : α.A) : GSet.{u} := (hier α).at' (.inr a)

/-- The graph set named by a name. -/
def nameVal (t : Name α.A) : GSet.{u} := (hier α).at' (.inl t)

end

/-- info: 'GSet.table_eq' does not depend on any axioms -/
#guard_msgs in #print axioms table_eq
/-- info: 'GSet.swf_hierRel' does not depend on any axioms -/
#guard_msgs in #print axioms swf_hierRel

end GSet
