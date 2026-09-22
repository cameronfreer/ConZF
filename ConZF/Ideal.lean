import ConZF.Ord
/-!
Ideal sets: the double-negation sheafification of the setoid of sets, as far as it exists
without higher inductive types. An *ideal set* is a stable, extensional, not not inhabited
predicate on sets all of whose elements are bisimilar (`Ideal`); ideals are compared pointwise.
Unique choice holds into ideals: a stable extensional functional relation that is not not
total is a function into `Ideal` (`Ideal.ofRel`). This is what `env_func` and `env_exists`
give for the envelope, and it is not a tree.

The constructor test: given a small family of ideal children `K : C → Ideal`, is there an
ideal parent whose members are exactly the `K c`? The parent is specified by a stable
extensional predicate (`IsParent`), functional by extensionality (`isParent_func`), but its
existence is exactly a small-indexed Collection for the family: it holds if and only if some
set not not contains a representative of every child (`isParent_exists_iff`). That is a
double-negation shift over the small index type, the shape of the obligation the whole
development is trying to avoid. So ideals of the existing trees do not give the sheafified
universe for free; the missing constructor is the Replacement problem in another form.
-/
universe u

namespace PSet

/-- An ideal set: a stable, extensional, not not inhabited predicate whose elements are all
bisimilar. -/
structure Ideal : Type (u+1) where
  S : PSet.{u} → Prop
  stable : ∀ x, ¬¬S x → S x
  resp : ∀ x y, x ≈ y → S x → S y
  inhab : ¬¬∃ x, S x
  single : ∀ x y, S x → S y → x ≈ y

instance {X : Ideal.{u}} {x : PSet.{u}} : Stable (X.S x) := ⟨X.stable x⟩

/-- Ideals are compared pointwise. -/
def Ideal.Equiv (X Y : Ideal.{u}) : Prop := ∀ x, X.S x ↔ Y.S x

/-- The ideal of a set. -/
def Ideal.of (x : PSet.{u}) : Ideal.{u} where
  S y := y ≈ x
  stable _ := Stable.dne
  resp _ _ e h := e.symm.trans h
  inhab := nn_intro ⟨x, Equiv.refl x⟩
  single _ _ h h' := h.trans h'.symm

/-- **Unique choice into ideals.** A stable extensional relation that is functional and not not
total is a function into ideals. -/
def Ideal.ofRel {α : Sort _} (F : α → PSet.{u} → Prop) (hs : ∀ a y, ¬¬F a y → F a y)
    (hr : ∀ a y y', y ≈ y' → F a y → F a y') (htot : ∀ a, ¬¬∃ y, F a y)
    (hf : ∀ a y y', F a y → F a y' → y ≈ y') (a : α) : Ideal.{u} where
  S := F a
  stable := hs a
  resp := hr a
  inhab := htot a
  single := hf a

theorem Ideal.ofRel_spec {α : Sort _} (F : α → PSet.{u} → Prop) (hs) (hr) (htot) (hf) (a : α)
    (y : PSet.{u}) : (Ideal.ofRel F hs hr htot hf a).S y ↔ F a y := Iff.rfl

/-! ### The constructor test -/

/-- `p` is a parent of the family of ideal children `K`: its members are exactly the
representatives of the children. -/
def IsParent {C : Type u} (K : C → Ideal.{u}) (p : PSet.{u}) : Prop :=
  ∀ z, z ∈ p ↔ ¬¬∃ c, (K c).S z

instance {C : Type u} {K : C → Ideal.{u}} {p : PSet.{u}} : Stable (IsParent K p) :=
  inferInstanceAs (Stable (∀ _, _ ↔ _))

theorem isParent_resp {C : Type u} {K : C → Ideal.{u}} {p p' : PSet.{u}} (e : p ≈ p')
    (h : IsParent K p) : IsParent K p' :=
  fun z => (mem_congr_right e).symm.trans (h z)

/-- The parent specification is functional. -/
theorem isParent_func {C : Type u} {K : C → Ideal.{u}} {p p' : PSet.{u}} (h : IsParent K p)
    (h' : IsParent K p') : p ≈ p' :=
  ext fun z => (h z).trans (h' z).symm

/-- **The parent exists exactly when the family is collected.** A parent is not not available
iff some set not not contains a representative of every child; the converse direction is one
Separation. -/
theorem isParent_exists_iff {C : Type u} (K : C → Ideal.{u}) :
    (¬¬∃ p, IsParent K p) ↔ ¬¬∃ b : PSet.{u}, ∀ c, ¬¬∃ x, (K c).S x ∧ x ∈ b := by
  constructor
  · refine nn_map fun ⟨p, hp⟩ => ⟨p, fun c => ?_⟩
    exact nn_map (fun ⟨x, hx⟩ => ⟨x, hx, (hp x).2 (nn_intro ⟨c, hx⟩)⟩) (K c).inhab
  · refine nn_map fun ⟨b, hb⟩ => ⟨sep (fun z => ¬¬∃ c, (K c).S z) b, fun z => ?_⟩
    refine (mem_sep fun _ _ e => nn_map fun ⟨c, h⟩ => ⟨c, (K c).resp _ _ e h⟩).trans
      ⟨And.right, fun h => ⟨?_, h⟩⟩
    refine Stable.of_nn h fun ⟨c, hc⟩ => Stable.of_nn (hb c) fun ⟨x, hx, hxb⟩ => ?_
    exact (mem_congr_left ((K c).single x z hx hc)).1 hxb

/-- A family with actual representatives has a parent: the range of the representatives. -/
theorem isParent_range {C : Type u} (K : C → Ideal.{u}) (r : C → PSet.{u})
    (hr : ∀ c, (K c).S (r c)) : IsParent K (range r) := fun _ =>
  ⟨nn_map fun ⟨c, e⟩ => ⟨c, (K c).resp _ _ e.symm (hr c)⟩,
   nn_map fun ⟨c, h⟩ => ⟨c, (K c).single _ _ h (hr c)⟩⟩

/-- info: 'PSet.isParent_exists_iff' does not depend on any axioms -/
#guard_msgs in #print axioms isParent_exists_iff

end PSet
