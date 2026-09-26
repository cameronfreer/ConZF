import ConZF.Fml
/-!
Witness menus (conzf23, con60). A *menu* is an actual small index type with a payload function;
the payload may be large. `Ready` is negative inhabitation of the index type, and nothing ever
extracts an index from it.

* `collection_spec`: from an **actual** family of ready menus of witnesses with evidence, one per
  literal index of the source, the native `range` over the sum of the indices is a collecting set
  satisfying both clauses of Strong Collection, with the evidence retained; the forward menu at an
  arbitrary member of the source is saturated over its literal representatives, so no
  extensionality of the family is assumed. This interprets Collection *from a realizer of its
  premise*; it does not produce that realizer.
* `contract_spec`: for a stable extensional **functional** specification, a ready menu of correct
  witnesses contracts (union of its values) to an actual correct witness. So for functional
  relations such as the decoder, menus are no weaker than witnesses.
* `Typed`: an auxiliary positive syntax with large semantic realizers (`Real`), a merging
  operation `merge` on menus of realizers, negative truth, with-truth validity, and the fusion
  theorem `merge_valid`: a ready menu of valid realizers merges to a valid realizer. This is
  fusion of large semantic realizers; it is not a translation of `Fml` proofs and says nothing
  about small codes.
-/
universe u v w

namespace PSet.Witness

/-- A small index type with a payload of any size. -/
structure Menu (A : Type v) : Type (max (u+1) v) where
  I : Type u
  val : I → A

namespace Menu
variable {A : Type v} {B : Type w}

def Ready (m : Menu.{u, v} A) : Prop := ¬¬Nonempty m.I

def map (f : A → B) (m : Menu.{u, v} A) : Menu.{u, w} B := ⟨m.I, fun i => f (m.val i)⟩

def pure (a : A) : Menu.{u, v} A := ⟨PUnit, fun _ => a⟩

def bind (m : Menu.{u, v} A) (f : A → Menu.{u, w} B) : Menu.{u, w} B :=
  ⟨Σ i : m.I, (f (m.val i)).I, fun ij => (f (m.val ij.1)).val ij.2⟩

/-- Dependent bind: the second answer's type mentions the actual first value. -/
def bindDep {C : A → Type w} (m : Menu.{u, v} A) (f : ∀ a, Menu.{u, w} (C a)) :
    Menu.{u, max v w} (Sigma C) :=
  ⟨Σ i : m.I, (f (m.val i)).I, fun ij => ⟨m.val ij.1, (f (m.val ij.1)).val ij.2⟩⟩

theorem ready_map (f : A → B) (m : Menu.{u, v} A) (h : m.Ready) : (m.map f).Ready := h

theorem ready_pure (a : A) : (pure.{u, v} a).Ready := nn_intro ⟨⟨⟩⟩

theorem ready_bind (m : Menu.{u, v} A) (f : A → Menu.{u, w} B) (hm : m.Ready)
    (hf : ∀ i, (f (m.val i)).Ready) : (m.bind f).Ready :=
  nn_bind hm fun ⟨i⟩ => nn_map (fun ⟨j⟩ => ⟨⟨i, j⟩⟩) (hf i)

theorem ready_bindDep {C : A → Type w} (m : Menu.{u, v} A) (f : ∀ a, Menu.{u, w} (C a))
    (hm : m.Ready) (hf : ∀ i, (f (m.val i)).Ready) : (bindDep m f).Ready :=
  nn_bind hm fun ⟨i⟩ => nn_map (fun ⟨j⟩ => ⟨⟨i, j⟩⟩) (hf i)

/-- A stable property of all entries holds of some entry, negatively. -/
theorem read {Q : A → Prop} (m : Menu.{u, v} A) (hm : m.Ready) (hq : ∀ i, Q (m.val i)) :
    ¬¬∃ a, Q a :=
  nn_map (fun ⟨i⟩ => ⟨m.val i, hq i⟩) hm

end Menu

/-! ### Collection from actual menus -/

section Collection
variable {W : Type v} (a : PSet.{u}) (m : a.Idx → Menu.{u, max (u+1) v} (PSet.{u} × W))

/-- The sum of the indices: a small type. -/
abbrev Token : Type u := Σ i : a.Idx, (m i).I

def entry (t : Token a m) : PSet.{u} × W := (m t.1).val t.2

/-- The collecting set: the witnesses, by native `range`. -/
def collect : PSet.{u} := range fun t : Token a m => (entry a m t).1

/-- The forward menu at `x`: all entries at literal representatives of `x`. -/
def forward (x : PSet.{u}) : Menu.{u, max (u+1) v} (PSet.{u} × W) :=
  ⟨{t : Token a m // x ≈ a.Func t.1}, fun t => entry a m t.1⟩

/-- The backward menu at `y`: the source tags and evidence of all entries equal to `y`. -/
def backward (y : PSet.{u}) : Menu.{u, max (u+1) v} (PSet.{u} × W) :=
  ⟨{t : Token a m // y ≈ (entry a m t).1}, fun t => (a.Func t.1.1, (entry a m t.1).2)⟩

theorem forward_ready (hm : ∀ i, (m i).Ready) {x : PSet.{u}} (hx : x ∈ a) :
    (forward a m x).Ready :=
  nn_bind hx fun ⟨i, hi⟩ => nn_map (fun ⟨j⟩ => ⟨⟨⟨i, j⟩, hi⟩⟩) (hm i)

theorem backward_ready {y : PSet.{u}} (hy : y ∈ collect a m) : (backward a m y).Ready :=
  nn_map (fun ⟨t, ht⟩ => ⟨⟨t, ht⟩⟩) hy

variable (V : PSet.{u} → PSet.{u} → W → Prop)
  (resp : ∀ x x' y y' r, x ≈ x' → y ≈ y' → V x y r → V x' y' r)
  (valid : ∀ i j, V (a.Func i) ((m i).val j).1 ((m i).val j).2)
include resp valid

theorem forward_valid (x : PSet.{u}) (t : (forward a m x).I) :
    ((forward a m x).val t).1 ∈ collect a m ∧ V x ((forward a m x).val t).1 ((forward a m x).val t).2 :=
  ⟨func_mem (collect a m) t.1, resp _ _ _ _ _ t.2.symm (Equiv.refl _) (valid t.1.1 t.1.2)⟩

theorem backward_valid (y : PSet.{u}) (t : (backward a m y).I) :
    ((backward a m y).val t).1 ∈ a ∧ V ((backward a m y).val t).1 y ((backward a m y).val t).2 :=
  ⟨func_mem a t.1.1, resp _ _ _ _ _ (Equiv.refl _) t.2.symm (valid t.1.1 t.1.2)⟩

/-- **Strong Collection from actual menus**, both clauses, evidence retained. -/
theorem collection_spec (hm : ∀ i, (m i).Ready) :
    (∀ x, x ∈ a → (forward a m x).Ready ∧ ∀ t, ((forward a m x).val t).1 ∈ collect a m ∧
      V x ((forward a m x).val t).1 ((forward a m x).val t).2) ∧
    (∀ y, y ∈ collect a m → (backward a m y).Ready ∧ ∀ t, ((backward a m y).val t).1 ∈ a ∧
      V ((backward a m y).val t).1 y ((backward a m y).val t).2) :=
  ⟨fun _ hx => ⟨forward_ready a m hm hx, forward_valid a m V resp valid _⟩,
   fun _ hy => ⟨backward_ready a m hy, backward_valid a m V resp valid _⟩⟩

end Collection

/-! ### Contraction of functional menus -/

section Contraction

def values (m : Menu.{u, u+1} PSet.{u}) : PSet.{u} := range m.val

/-- The union of the values. Sound only when all values agree. -/
def contract (m : Menu.{u, u+1} PSet.{u}) : PSet.{u} := sUnion (values m)

theorem contract_equiv (m : Menu.{u, u+1} PSet.{u}) (hm : m.Ready) {y : PSet.{u}}
    (h : ∀ i, m.val i ≈ y) : contract m ≈ y :=
  ext fun _ => ⟨fun hz => Stable.of_nn (mem_sUnion.1 hz) fun ⟨_, hw, hzw⟩ =>
      Stable.of_nn (mem_range.1 hw) fun ⟨i, ei⟩ => (mem_congr_right (ei.trans (h i))).1 hzw,
    fun hz => Stable.of_nn hm fun ⟨i⟩ => mem_sUnion.2 (nn_intro
      ⟨m.val i, func_mem (values m) i, (mem_congr_right (h i)).2 hz⟩)⟩

/-- **A ready menu of correct witnesses of a functional specification contracts to a correct
witness.** No index is selected: the term is defined before readiness is used. -/
theorem contract_spec {R : PSet.{u} → Prop} [∀ y, Stable (R y)] (resp : ∀ y z, y ≈ z → R y → R z)
    (func : ∀ y z, R y → R z → y ≈ z) (m : Menu.{u, u+1} PSet.{u}) (hm : m.Ready)
    (valid : ∀ i, R (m.val i)) : R (contract m) :=
  Stable.of_nn hm fun ⟨i⟩ =>
    resp _ _ (contract_equiv m hm fun j => func _ _ (valid j) (valid i)).symm (valid i)

end Contraction

/-! ### Typed fusion of large semantic realizers -/

namespace Typed

inductive Form : Type
  | atom (n : Nat)
  | both (a b : Form)
  | either (a b : Form)
  | implies (a b : Form)
  | all (a : Form)
  | exists_ (a : Form)

/-- Semantic realizers: function spaces over `PSet`, hence large; every menu has a small index. -/
def Real : Form → Type (u+1)
  | .atom _ => PUnit
  | .both a b => Real a × Real b
  | .either a b => Menu.{u, u+1} (Real a ⊕ Real b)
  | .implies a b => Real a → Real b
  | .all a => PSet.{u} → Real a
  | .exists_ a => Menu.{u, u+1} (PSet.{u} × Real a)

/-- Merge a menu of realizers into one realizer, by flattening menus and pointwise application. -/
def merge : (a : Form) → Menu.{u, u+1} (Real.{u} a) → Real.{u} a
  | .atom _, _ => ⟨⟩
  | .both a b, m => (merge a (m.map Prod.fst), merge b (m.map Prod.snd))
  | .either _ _, m => m.bind id
  | .implies _ b, m => fun r => merge b (m.map fun f => f r)
  | .all a, m => fun x => merge a (m.map fun f => f x)
  | .exists_ _, m => m.bind id

/-- Negative truth, from an atomic interpretation. -/
def Truth (atom : Nat → (Nat → PSet.{u}) → Prop) : Form → (Nat → PSet.{u}) → Prop
  | .atom n, e => atom n e
  | .both a b, e => Truth atom a e ∧ Truth atom b e
  | .either a b, e => ¬¬(Truth atom a e ∨ Truth atom b e)
  | .implies a b, e => Truth atom a e → Truth atom b e
  | .all a, e => ∀ x : PSet.{u}, Truth atom a (Env.cons x e)
  | .exists_ a, e => ¬¬∃ x : PSet.{u}, Truth atom a (Env.cons x e)

/-- Validity with truth: an implication realizer must also preserve truth. -/
def Valid (atom : Nat → (Nat → PSet.{u}) → Prop) :
    (a : Form) → (Nat → PSet.{u}) → Real.{u} a → Prop
  | .atom n, e, _ => atom n e
  | .both a b, e, r => Valid atom a e r.1 ∧ Valid atom b e r.2
  | .either a b, e, r => r.Ready ∧ ∀ i, (r.val i).elim (Valid atom a e) (Valid atom b e)
  | .implies a b, e, f =>
    (Truth atom a e → Truth atom b e) ∧ ∀ r, Valid atom a e r → Valid atom b e (f r)
  | .all a, e, f => ∀ x, Valid atom a (Env.cons x e) (f x)
  | .exists_ a, e, r => r.Ready ∧ ∀ i, Valid atom a (Env.cons (r.val i).1 e) (r.val i).2

section
variable {atom : Nat → (Nat → PSet.{u}) → Prop} (hs : ∀ n e, Stable (atom n e))
include hs

theorem truth_stable : ∀ (a : Form) (e : Nat → PSet.{u}), Stable (Truth atom a e)
  | .atom n, e => hs n e
  | .both a b, e => have := truth_stable a e; have := truth_stable b e
    inferInstanceAs (Stable (_ ∧ _))
  | .either _ _, _ => inferInstanceAs (Stable (¬ _))
  | .implies _ b, e => have := truth_stable b e; inferInstanceAs (Stable (_ → _))
  | .all a, e => ⟨fun h x => have := truth_stable a (Env.cons x e); Stable.of_nn h fun t => t x⟩
  | .exists_ _, _ => inferInstanceAs (Stable (¬ _))

/-- **Fusion.** A ready menu of valid realizers merges to a valid realizer. -/
theorem merge_valid : ∀ (a : Form) (e : Nat → PSet.{u}) (m : Menu.{u, u+1} (Real.{u} a)),
    m.Ready → (∀ i, Valid atom a e (m.val i)) → Valid atom a e (merge a m)
  | .atom n, e, _, hm, hv => show atom n e from have := hs n e; Stable.of_nn hm fun ⟨i⟩ => hv i
  | .both a b, e, m, hm, hv =>
    ⟨merge_valid a e (m.map Prod.fst) hm fun i => (hv i).1,
     merge_valid b e (m.map Prod.snd) hm fun i => (hv i).2⟩
  | .either _ _, _, m, hm, hv =>
    ⟨Menu.ready_bind m id hm fun i => (hv i).1, fun ij => (hv ij.1).2 ij.2⟩
  | .implies a b, e, m, hm, hv =>
    ⟨fun ta => have := truth_stable hs b e; Stable.of_nn hm fun ⟨i⟩ => (hv i).1 ta,
     fun r hr => merge_valid b e (m.map fun f : Real.{u} a → Real.{u} b => f r) hm
       fun i => (hv i).2 r hr⟩
  | .all a, e, m, hm, hv => fun x =>
    merge_valid a (Env.cons x e) (m.map fun f : PSet.{u} → Real.{u} a => f x) hm fun i => hv i x
  | .exists_ _, _, m, hm, hv =>
    ⟨Menu.ready_bind m id hm fun i => (hv i).1, fun ij => (hv ij.1).2 ij.2⟩

end
end Typed

/-! ### Certificate menus and native consolidation (conzf29)

The reviewer's correction of con71 §6: if possible witnesses already range over a supplied small
dependent carrier `C i`, then the family of *all* certified witnesses is an actual family of menus
(`certificates`), and pointwise negative existence proves readiness without selecting anything.
With a total readback into `PSet.{u}`, stable requested conclusions, and a condition predicate
antitone under inclusion, the union of all decoded valid certificates is one common condition bound
(`common_condition_bound`). What this does **not** supply: the small carrier and its readback, a
descriptor for the union in any fixed grammar (see `Audit/ObjectEnvelope.lean`), or any level
safety. -/

namespace Certified
variable {I : Type u} {C : I → Type u}

/-- All certified witnesses at `i`, as a menu: the index type is the certificate subtype. -/
def certificates (P : ∀ i, C i → Prop) (i : I) : Menu.{u, u} (C i) :=
  ⟨{c : C i // P i c}, fun c => c.1⟩

/-- Readiness from pointwise negative existence; no witness is selected. -/
theorem certificates_ready (P : ∀ i, C i → Prop) (h : ∀ i, ¬¬∃ c, P i c) (i : I) :
    (certificates P i).Ready :=
  nn_map (fun ⟨c, hc⟩ => ⟨⟨c, hc⟩⟩) (h i)

theorem certificates_valid (P : ∀ i, C i → Prop) (i : I) (t : (certificates P i).I) :
    P i ((certificates P i).val t) := t.2

/-- The native set of all decoded certified witnesses, over the small sum of the carriers. -/
def collected (P : ∀ i, C i → Prop) (read : ∀ i, C i → PSet.{u}) : PSet.{u} :=
  range fun t : Σ i, {c : C i // P i c} => read t.1 t.2.1

/-- Its union. -/
def combined (P : ∀ i, C i → Prop) (read : ∀ i, C i → PSet.{u}) : PSet.{u} :=
  sUnion (collected P read)

theorem read_subset_combined (P : ∀ i, C i → Prop) (read : ∀ i, C i → PSet.{u}) (i : I) (c : C i)
    (hc : P i c) (x : PSet.{u}) (hx : x ∈ read i c) : x ∈ combined P read :=
  mem_sUnion.2 (nn_intro ⟨read i c, func_mem (collected P read) ⟨i, ⟨c, hc⟩⟩, hx⟩)

/-- A concrete same-universe bound; defining it needs no existence premise. -/
def conditionBound (Tr : PSet.{u} → Prop) (Q : I → Prop) (read : ∀ i, C i → PSet.{u}) : PSet.{u} :=
  combined (fun i c => Tr (read i c) → Q i) read

/-- Native bound consolidation: with small dependent carriers, total readback, stable conclusions
and `Tr` antitone under inclusion, one bound serves every request. -/
theorem common_condition_bound (Tr : PSet.{u} → Prop) (Q : I → Prop) [∀ i, Stable (Q i)]
    (read : ∀ i, C i → PSet.{u})
    (antitone : ∀ U V : PSet.{u}, (∀ x, x ∈ U → x ∈ V) → Tr V → Tr U)
    (h : ∀ i, ¬¬∃ c : C i, Tr (read i c) → Q i) :
    Tr (conditionBound Tr Q read) → ∀ i, Q i := by
  intro hTr i
  exact Stable.of_nn (h i) fun ⟨c, hc⟩ => hc (antitone _ _ (read_subset_combined _ read i c hc) hTr)

/-- A large family of requests can share one bound when all candidate values come from one fixed
small decoder independent of the request. Readback of a small syntax at environments extended by
arbitrary native sets is not such a decoder. -/
theorem common_bound_of_fixed_decoder {J : Sort v} {D : Type u} (Tr : PSet.{u} → Prop) (Q : J → Prop)
    [∀ j, Stable (Q j)] (read : D → PSet.{u})
    (antitone : ∀ U V : PSet.{u}, (∀ x, x ∈ U → x ∈ V) → Tr V → Tr U)
    (h : ∀ j, ¬¬∃ d : D, Tr (read d) → Q j) :
    Tr (sUnion (range read)) → ∀ j, Q j := by
  intro hTr j
  exact Stable.of_nn (h j) fun ⟨d, hd⟩ => hd (antitone _ _
    (fun x hx => mem_sUnion.2 (nn_intro ⟨read d, func_mem (range read) d, hx⟩)) hTr)

end Certified

/-- info: 'PSet.Witness.Certified.certificates_ready' does not depend on any axioms -/
#guard_msgs in #print axioms Certified.certificates_ready
/-- info: 'PSet.Witness.Certified.common_condition_bound' does not depend on any axioms -/
#guard_msgs in #print axioms Certified.common_condition_bound
/-- info: 'PSet.Witness.Certified.common_bound_of_fixed_decoder' does not depend on any axioms -/
#guard_msgs in #print axioms Certified.common_bound_of_fixed_decoder
/-- info: 'PSet.Witness.collection_spec' does not depend on any axioms -/
#guard_msgs in #print axioms collection_spec
/-- info: 'PSet.Witness.contract_spec' does not depend on any axioms -/
#guard_msgs in #print axioms contract_spec
/-- info: 'PSet.Witness.Typed.merge_valid' does not depend on any axioms -/
#guard_msgs in #print axioms Typed.merge_valid

end PSet.Witness
