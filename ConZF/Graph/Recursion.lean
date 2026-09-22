import ConZF.Logic
/-!
Predecessor-local recursion into stable predicates on a fixed carrier, from well-founded
induction for stable predicates (`SWF`). For a table operator `F` whose value at `a` depends only
on the rows at predecessors of `a` (`hlocal`) and whose values are stable, the unconditional
table `joinedTable`, the union of all partial solutions, satisfies `T a b ↔ F T a b` at every
point (`predicate_recursion`). No monotonicity of `F` is assumed, no partial solution is
selected, and `SWF` is never eliminated into `Type`: the output is a predicate. A graph can use
that predicate as its edge relation, which is how the graph route produces new values.
-/
universe u v

namespace Graph

variable {A : Type u} {B : Type v}

abbrev Table (A : Type u) (B : Type v) := A → B → Prop

/-- Well-founded induction for stable predicates. -/
def SWF (R : A → A → Prop) : Prop :=
  ∀ P : A → Prop, (∀ a, Stable (P a)) → (∀ a, (∀ b, R b a → P b) → P a) → ∀ a, P a

structure PartialSolution (R : A → A → Prop) (F : Table A B → Table A B) where
  dom : A → Prop
  val : Table A B
  domStable : ∀ a, Stable (dom a)
  valStable : ∀ a b, Stable (val a b)
  down : ∀ {a b}, R b a → dom a → dom b
  equation : ∀ a, dom a → ∀ b, val a b ↔ F val a b

variable (R : A → A → Prop) (F : Table A B → Table A B)

/-- Both definitions are unconditional predicate-valued terms. -/
def joinedDomain (a : A) : Prop := ¬¬∃ p : PartialSolution R F, p.dom a

def joinedTable (a : A) (b : B) : Prop := ¬¬∃ p : PartialSolution R F, p.dom a ∧ p.val a b

instance {a : A} : Stable (joinedDomain R F a) := inferInstanceAs (Stable (¬_))
instance {a : A} {b : B} : Stable (joinedTable R F a b) := inferInstanceAs (Stable (¬_))

variable
  (hlocal : ∀ T U : Table A B, ∀ a,
    (∀ c, R c a → ∀ b, T c b ↔ U c b) → ∀ b, F T a b ↔ F U a b)
  (hF : ∀ T : Table A B, ∀ a b, Stable (F T a b))
  (hwf : SWF R)

include hlocal hwf in
/-- Any two partial solutions agree on their common domain. -/
theorem compatible : ∀ a, ∀ p q : PartialSolution R F,
    p.dom a → q.dom a → ∀ b, p.val a b ↔ q.val a b := by
  let P : A → Prop := fun a => ∀ p q : PartialSolution R F,
    p.dom a → q.dom a → ∀ b, p.val a b ↔ q.val a b
  have hs : ∀ a, Stable (P a) := by
    intro a
    refine ⟨fun hn p q hp hq b => ?_⟩
    have : Stable (p.val a b) := p.valStable a b
    have : Stable (q.val a b) := q.valStable a b
    exact Stable.of_nn hn fun H => H p q hp hq b
  apply hwf P hs
  intro a ih p q hp hq b
  exact (p.equation a hp b).trans
    ((hlocal p.val q.val a (fun c hc d => ih c hc p q (p.down hc hp) (q.down hc hq) d) b).trans
      (q.equation a hq b).symm)

include hlocal hwf in
/-- A partial solution computes the joined table on its domain. -/
theorem joined_agrees (p : PartialSolution R F) {a : A} (ha : p.dom a) (b : B) :
    joinedTable R F a b ↔ p.val a b := by
  have : Stable (p.val a b) := p.valStable a b
  constructor
  · intro h
    exact Stable.of_nn h fun ⟨q, hqa, hqb⟩ => (compatible R F hlocal hwf a q p hqa ha b).1 hqb
  · intro h
    exact nn_intro ⟨p, ha, h⟩

include hlocal hF hwf in
/-- The joined table solves the equation wherever a partial solution exists. -/
theorem joined_equation_on_domain {a : A} (ha : joinedDomain R F a) (b : B) :
    joinedTable R F a b ↔ F (joinedTable R F) a b := by
  have : Stable (F (joinedTable R F) a b) := hF _ a b
  refine Stable.of_nn ha fun ⟨p, hp⟩ => ?_
  exact (joined_agrees R F hlocal hwf p hp b).trans ((p.equation a hp b).trans
    (hlocal p.val (joinedTable R F) a
      (fun c hc d => (joined_agrees R F hlocal hwf p (p.down hc hp) d).symm) b))

variable (htrans : ∀ {a b c}, R a b → R b c → R a c) (hR : ∀ a b, Stable (R a b))

include hlocal hF hwf htrans hR in
/-- The joined domain is everything: extend over one downward cone using the joined table
itself, with no partial table chosen for the predecessors. -/
theorem joined_total : ∀ a, joinedDomain R F a := by
  apply hwf (joinedDomain R F) fun _ => inferInstance
  intro a ih
  let D : A → Prop := fun v => ¬¬(v = a ∨ R v a)
  have below : ∀ v, D v → ∀ c, R c v → R c a := by
    intro v hv c hcv
    have : Stable (R c a) := hR c a
    exact Stable.of_nn hv fun
      | .inl e => e ▸ hcv
      | .inr h => htrans hcv h
  let p : PartialSolution R F := {
    dom := D
    val := F (joinedTable R F)
    domStable := fun _ => inferInstanceAs (Stable (¬_))
    valStable := hF _
    down := fun {v c} hcv hv => nn_intro (.inr (below v hv c hcv))
    equation := fun v hv b =>
      hlocal (joinedTable R F) (F (joinedTable R F)) v
        (fun c hcv d => joined_equation_on_domain R F hlocal hF hwf (ih c (below v hv c hcv)) d) b }
  exact nn_intro ⟨p, nn_intro (.inl rfl)⟩

include hlocal hF hwf htrans hR in
/-- **Predicate recursion.** The joined table is the recursive predicate. -/
theorem predicate_recursion : ∀ a b, joinedTable R F a b ↔ F (joinedTable R F) a b :=
  fun a b => joined_equation_on_domain R F hlocal hF hwf
    (joined_total R F hlocal hF hwf htrans hR a) b

include hlocal hwf in
/-- Uniqueness among stable solutions, up to pointwise equivalence. -/
theorem solution_unique (T : Table A B) (hT : ∀ a b, Stable (T a b))
    (hEq : ∀ a b, T a b ↔ F T a b) : ∀ a b, T a b ↔ joinedTable R F a b := by
  let p : PartialSolution R F := {
    dom := fun _ => True
    val := T
    domStable := fun _ => inferInstance
    valStable := hT
    down := fun _ _ => trivial
    equation := fun a _ b => hEq a b }
  exact fun a b => (joined_agrees R F hlocal hwf p trivial b).symm

/-- info: 'Graph.predicate_recursion' does not depend on any axioms -/
#guard_msgs in #print axioms predicate_recursion
/-- info: 'Graph.solution_unique' does not depend on any axioms -/
#guard_msgs in #print axioms solution_unique

end Graph
