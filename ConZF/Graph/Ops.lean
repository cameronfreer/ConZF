import ConZF.Graph.GSet
/-!
Native graph operations: the range of a small family (`GSet.range`), Separation (`GSet.sep`),
and the powerset (`GSet.powerset`). Each is a graph on a carrier built from the supplied
carriers, with stable well-founded induction proved layer by layer, and each has the expected
negative membership law. Nothing collects a relation over unknown carriers: the families and
predicates are supplied as data.
-/
universe u

namespace GSet

/-- Membership in `G` is a stable predicate on graph sets. -/
theorem mem_iff_at' {K G : GSet.{u}} : Mem K G ↔ ¬¬∃ a, G.R a G.r ∧ Equiv K (G.at' a) := Iff.rfl

/-! ### Small ranges -/

section range
variable {ι : Type u} (F : ι → GSet.{u})

/-- Edges of the range: the component edges, and each component root below the new root. -/
inductive RangeRel : Option (Σ i, (F i).A) → Option (Σ i, (F i).A) → Prop
  | comp {i : ι} {a b : (F i).A} : (F i).R a b → RangeRel (some ⟨i, a⟩) (some ⟨i, b⟩)
  | root (i : ι) : RangeRel (some ⟨i, (F i).r⟩) none

theorem rangeRel_some {i : ι} {b : (F i).A} {x} (h : RangeRel F x (some ⟨i, b⟩)) :
    ∃ a, (F i).R a b ∧ x = some ⟨i, a⟩ := by
  cases h with
  | comp h => exact ⟨_, h, rfl⟩

theorem rangeRel_none {x} (h : RangeRel F x none) : ∃ i, x = some ⟨i, (F i).r⟩ := by
  cases h with
  | root i => exact ⟨i, rfl⟩

theorem swf_rangeRel : Graph.SWF (RangeRel F) := by
  intro P hs H
  have comp : ∀ i (a : (F i).A), P (some ⟨i, a⟩) := fun i => by
    refine (F i).swf (fun a => P (some ⟨i, a⟩)) (fun _ => hs _) fun a ih => ?_
    refine H _ fun x hx => ?_
    obtain ⟨a', ha', rfl⟩ := rangeRel_some F hx
    exact ih a' ha'
  intro x
  cases x with
  | some p => exact comp p.1 p.2
  | none => exact H _ fun x hx => by obtain ⟨i, rfl⟩ := rangeRel_none F hx; exact comp _ _

/-- The range of a small family. -/
def range : GSet.{u} := ⟨Option (Σ i, (F i).A), RangeRel F, none, swf_rangeRel F⟩

/-- A component, pointed at one of its vertices, is the corresponding pointed graph. -/
theorem range_at'_equiv (i : ι) (a : (F i).A) : Equiv ((range F).at' (some ⟨i, a⟩)) ((F i).at' a) := by
  refine nn_intro ⟨fun x b => ¬¬(x = some ⟨i, b⟩), ⟨fun _ _ => inferInstance, ?_, ?_⟩, nn_intro rfl⟩
  · intro x b hx x' hx'
    refine Stable.of_nn hx fun e => ?_
    subst e
    obtain ⟨a', ha', rfl⟩ := rangeRel_some F hx'
    exact nn_intro ⟨a', ha', nn_intro rfl⟩
  · intro x b hx b' hb'
    refine Stable.of_nn hx fun e => ?_
    subst e
    exact nn_intro ⟨some ⟨i, b'⟩, RangeRel.comp hb', nn_intro rfl⟩

theorem mem_range {K : GSet.{u}} : Mem K (range F) ↔ ¬¬∃ i, Equiv K (F i) := by
  constructor
  · refine nn_map fun ⟨x, hx, e⟩ => ?_
    obtain ⟨i, rfl⟩ := rangeRel_none F hx
    exact ⟨i, e.trans (range_at'_equiv F i (F i).r)⟩
  · refine nn_map fun ⟨i, e⟩ => ?_
    exact ⟨some ⟨i, (F i).r⟩, RangeRel.root i, e.trans (range_at'_equiv F i (F i).r).symm⟩

end range

/-! ### Separation -/

section sep
variable (P : GSet.{u} → Prop) (G : GSet.{u})

/-- Edges of the separation: the old edges, and the selected predecessors of the old root below
the new root. -/
inductive SepRel : Option G.A → Option G.A → Prop
  | old {a b : G.A} : G.R a b → SepRel (some a) (some b)
  | sel {a : G.A} : G.R a G.r → P (G.at' a) → SepRel (some a) none

theorem sepRel_some {b : G.A} {x} (h : SepRel P G x (some b)) : ∃ a, G.R a b ∧ x = some a := by
  cases h with
  | old h => exact ⟨_, h, rfl⟩

theorem sepRel_none {x} (h : SepRel P G x none) : ∃ a, G.R a G.r ∧ P (G.at' a) ∧ x = some a := by
  cases h with
  | sel h hp => exact ⟨_, h, hp, rfl⟩

theorem swf_sepRel : Graph.SWF (SepRel P G) := by
  intro Q hs H
  have old : ∀ a : G.A, Q (some a) := by
    refine G.swf (fun a => Q (some a)) (fun _ => hs _) fun a ih => H _ fun x hx => ?_
    obtain ⟨a', ha', rfl⟩ := sepRel_some P G hx
    exact ih a' ha'
  intro x
  cases x with
  | some a => exact old a
  | none => exact H _ fun x hx => by obtain ⟨a, _, _, rfl⟩ := sepRel_none P G hx; exact old a

/-- Separation. -/
def sep : GSet.{u} := ⟨Option G.A, SepRel P G, none, swf_sepRel P G⟩

theorem sep_at'_equiv (a : G.A) : Equiv ((sep P G).at' (some a)) (G.at' a) := by
  refine nn_intro ⟨fun x b => ¬¬(x = some b), ⟨fun _ _ => inferInstance, ?_, ?_⟩, nn_intro rfl⟩
  · intro x b hx x' hx'
    refine Stable.of_nn hx fun e => ?_
    subst e
    obtain ⟨a', ha', rfl⟩ := sepRel_some P G hx'
    exact nn_intro ⟨a', ha', nn_intro rfl⟩
  · intro x b hx b' hb'
    refine Stable.of_nn hx fun e => ?_
    subst e
    exact nn_intro ⟨some b', SepRel.old hb', nn_intro rfl⟩

theorem mem_sep [∀ K, Stable (P K)] (hP : ∀ K K', Equiv K K' → P K → P K') {K : GSet.{u}} :
    Mem K (sep P G) ↔ Mem K G ∧ P K := by
  constructor
  · intro h
    refine ⟨nn_map (fun ⟨x, hx, e⟩ => ?_) h, Stable.of_nn h fun ⟨x, hx, e⟩ => ?_⟩
    · obtain ⟨a, _, hp, rfl⟩ := sepRel_none P G hx
      exact hP _ _ (e.trans (sep_at'_equiv P G a)).symm hp
    · obtain ⟨a, ha, _, rfl⟩ := sepRel_none P G hx
      exact ⟨a, ha, e.trans (sep_at'_equiv P G a)⟩
  · rintro ⟨h, hp⟩
    refine nn_map (fun ⟨a, ha, e⟩ => ?_) h
    exact ⟨some a, SepRel.sel ha (hP _ _ e hp), e.trans (sep_at'_equiv P G a).symm⟩

end sep

/-! ### Powerset -/

section powerset
variable (G : GSet.{u})

/-- Vertices of the powerset: old vertices, a vertex for each predicate on the carrier, and an
outer root. -/
inductive PowV : Type u
  | old (a : G.A)
  | sub (S : G.A → Prop)
  | top

/-- Edges: old edges; the selected predecessors of the old root below a subset vertex; every
subset vertex below the top. -/
inductive PowRel : PowV G → PowV G → Prop
  | old {a b : G.A} : G.R a b → PowRel (.old a) (.old b)
  | sel {a : G.A} {S : G.A → Prop} : G.R a G.r → S a → PowRel (.old a) (.sub S)
  | top (S : G.A → Prop) : PowRel (.sub S) .top

theorem powRel_old {b : G.A} {x} (h : PowRel G x (.old b)) : ∃ a, G.R a b ∧ x = .old a := by
  cases h with
  | old h => exact ⟨_, h, rfl⟩

theorem powRel_sub {S : G.A → Prop} {x} (h : PowRel G x (.sub S)) :
    ∃ a, G.R a G.r ∧ S a ∧ x = .old a := by
  cases h with
  | sel h hs => exact ⟨_, h, hs, rfl⟩

theorem powRel_top {x} (h : PowRel G x .top) : ∃ S, x = .sub S := by
  cases h with
  | top S => exact ⟨S, rfl⟩

theorem swf_powRel : Graph.SWF (PowRel G) := by
  intro Q hs H
  have old : ∀ a : G.A, Q (.old a) := by
    refine G.swf (fun a => Q (.old a)) (fun _ => hs _) fun a ih => H _ fun x hx => ?_
    obtain ⟨a', ha', rfl⟩ := powRel_old G hx
    exact ih a' ha'
  have sub : ∀ S, Q (.sub S) := fun S => H _ fun x hx => by
    obtain ⟨a, _, _, rfl⟩ := powRel_sub G hx; exact old a
  intro x
  cases x with
  | old a => exact old a
  | sub S => exact sub S
  | top => exact H _ fun x hx => by obtain ⟨S, rfl⟩ := powRel_top G hx; exact sub S

/-- The powerset. -/
def powerset : GSet.{u} := ⟨PowV G, PowRel G, .top, swf_powRel G⟩

theorem powerset_old_equiv (a : G.A) : Equiv ((powerset G).at' (.old a)) (G.at' a) := by
  refine nn_intro ⟨fun x b => ¬¬(x = .old b), ⟨fun _ _ => inferInstance, ?_, ?_⟩, nn_intro rfl⟩
  · intro x b hx x' hx'
    refine Stable.of_nn hx fun e => ?_
    subst e
    obtain ⟨a', ha', rfl⟩ := powRel_old G hx'
    exact nn_intro ⟨a', ha', nn_intro rfl⟩
  · intro x b hx b' hb'
    refine Stable.of_nn hx fun e => ?_
    subst e
    exact nn_intro ⟨.old b', PowRel.old hb', nn_intro rfl⟩

/-- The members of a subset vertex are the selected members of `G`. -/
theorem mem_powerset_sub {S : G.A → Prop} {K : GSet.{u}} :
    Mem K ((powerset G).at' (.sub S)) ↔ ¬¬∃ a, G.R a G.r ∧ S a ∧ Equiv K (G.at' a) := by
  constructor
  · refine nn_map fun ⟨x, hx, e⟩ => ?_
    obtain ⟨a, ha, hs, rfl⟩ := powRel_sub G hx
    exact ⟨a, ha, hs, e.trans (powerset_old_equiv G a)⟩
  · refine nn_map fun ⟨a, ha, hs, e⟩ => ?_
    exact ⟨.old a, PowRel.sel ha hs, e.trans (powerset_old_equiv G a).symm⟩

/-- Subsets of `G`. -/
def Subset (Y G : GSet.{u}) : Prop := ∀ K, Mem K Y → Mem K G

/-- **The powerset law.** The members of the powerset are exactly the subsets of `G`. -/
theorem mem_powerset {K : GSet.{u}} : Mem K (powerset G) ↔ Subset K G := by
  constructor
  · intro h K' hK'
    refine Stable.of_nn h fun ⟨x, hx, e⟩ => ?_
    obtain ⟨S, rfl⟩ := powRel_top G hx
    refine Stable.of_nn ((mem_powerset_sub G).1 (Mem.congr_right e hK')) fun ⟨a, ha, _, e'⟩ => ?_
    exact nn_intro ⟨a, ha, e'⟩
  · intro h
    refine nn_intro ⟨.sub fun a => Mem (G.at' a) K, PowRel.top _, ext fun K' => ?_⟩
    refine Iff.trans ?_ (mem_powerset_sub G).symm
    constructor
    · intro hK'
      refine Stable.of_nn (h K' hK') fun ⟨a, ha, e⟩ => ?_
      exact nn_intro ⟨a, ha, Mem.congr_left e hK', e⟩
    · intro h'
      exact Stable.of_nn h' fun ⟨_, _, hm, e⟩ => Mem.congr_left e.symm hm

end powerset

end GSet
