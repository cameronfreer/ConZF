-- Reviewer audit probe (2026-09-26), incorporated verbatim from the small-machine audit after conzf25;
-- its scope is stated in its own docstring. Empty axiom reports.
import ConZF.Fml
import ConZF.Ord

/-!
A deliberately small positive logical core for the context discipline.

Codes can mention object variables absent from their conclusion. Code renaming
acts on both witness references and the body under a new binder. Realizability
respects joint formula/code renaming under pointwise bisimilar environments.

This covers atoms, conjunction, and positive existential introduction only.
It supplies neither arbitrary menu elimination, implication/universal adequacy,
nor Separation. Its final counterexample shows why the old formula-only
environment-agreement theorem must not be retained after fixing witnesses.
-/
universe u
namespace PSet.SupportedCoreAudit

inductive Form : Type
  | mem (i j : Nat)
  | eq (i j : Nat)
  | fls
  | and (a b : Form)
  | ex (a : Form)

inductive Code : Type
  | atom
  | pair (a b : Code)
  | packVar (j : Nat) (body : Code)
  | packEmpty (body : Code)

def Form.rename (ρ : Nat → Nat) : Form → Form
  | .mem i j => .mem (ρ i) (ρ j)
  | .eq i j => .eq (ρ i) (ρ j)
  | .fls => .fls
  | .and a b => .and (a.rename ρ) (b.rename ρ)
  | .ex a => .ex (a.rename (Fml.up ρ))

def Code.rename (ρ : Nat → Nat) : Code → Code
  | .atom => .atom
  | .pair a b => .pair (a.rename ρ) (b.rename ρ)
  | .packVar j body => .packVar (ρ j) (body.rename (Fml.up ρ))
  | .packEmpty body => .packEmpty (body.rename (Fml.up ρ))

abbrev Env := Nat → PSet.{u}

def Real : Form → Env.{u} → Code → Prop
  | .mem i j, e, _ => e i ∈ e j
  | .eq i j, e, _ => e i ≈ e j
  | .fls, _, _ => False
  | .and a b, e, c => match c with
      | .atom => False
      | .pair x y => Real a e x ∧ Real b e y
      | .packVar _ _ => False
      | .packEmpty _ => False
  | .ex a, e, c => match c with
      | .atom => False
      | .pair _ _ => False
      | .packVar j body => Real a (PSet.Env.cons (e j) e) body
      | .packEmpty body => Real a (PSet.Env.cons empty e) body

theorem ex_intro_var (a : Form) (e : Env.{u}) (j : Nat) (c : Code)
    (h : Real a (PSet.Env.cons (e j) e) c) : Real (.ex a) e (.packVar j c) := h

theorem and_intro (a b : Form) (e : Env.{u}) (c d : Code)
    (hc : Real a e c) (hd : Real b e d) : Real (.and a b) e (.pair c d) := ⟨hc, hd⟩

def Code.fst : Code → Code
  | .atom => .atom
  | .pair c _ => c
  | .packVar _ _ => .atom
  | .packEmpty _ => .atom

def Code.snd : Code → Code
  | .atom => .atom
  | .pair _ d => d
  | .packVar _ _ => .atom
  | .packEmpty _ => .atom

theorem and_elim (a b : Form) (e : Env.{u}) (c : Code) (h : Real (.and a b) e c) :
    Real a e c.fst ∧ Real b e c.snd := by
  cases c with
  | atom => exact h.elim
  | pair c d => exact h
  | packVar j body => exact h.elim
  | packEmpty body => exact h.elim

theorem cons_agree {ρ : Nat → Nat} {e e' : Env.{u}} {x x' : PSet.{u}}
    (he : ∀ n, e n ≈ e' (ρ n)) (hx : x ≈ x') :
    ∀ n, PSet.Env.cons x e n ≈ PSet.Env.cons x' e' (Fml.up ρ n)
  | 0 => hx
  | n+1 => he n

/-- Arbitrary renamings are allowed, not just injective slot insertions. -/
theorem real_rename (a : Form) : ∀ (ρ : Nat → Nat) (e e' : Env.{u}) (c : Code),
    (∀ n, e n ≈ e' (ρ n)) → (Real a e c ↔ Real (a.rename ρ) e' (c.rename ρ)) := by
  induction a with
  | mem i j =>
    intro ρ e e' c he
    exact (mem_congr_left (he i)).trans (mem_congr_right (he j))
  | eq i j =>
    intro ρ e e' c he
    exact ⟨fun h => (he i).symm.trans (h.trans (he j)),
      fun h => (he i).trans (h.trans (he j).symm)⟩
  | fls => intro ρ e e' c he; exact Iff.rfl
  | and a b iha ihb =>
    intro ρ e e' c he
    cases c with
    | atom => exact Iff.rfl
    | pair c d => exact and_congr (iha ρ e e' c he) (ihb ρ e e' d he)
    | packVar j body => exact Iff.rfl
    | packEmpty body => exact Iff.rfl
  | ex a ih =>
    intro ρ e e' c he
    cases c with
    | atom => exact Iff.rfl
    | pair c d => exact Iff.rfl
    | packVar j body => exact ih (Fml.up ρ) _ _ body (cons_agree he (he j))
    | packEmpty body => exact ih (Fml.up ρ) _ _ body (cons_agree he (Equiv.refl empty))

def insertAt (k : Nat) (e : Env.{u}) (x : PSet.{u}) : Env.{u}
  | 0 => match k with
    | 0 => x
    | _+1 => e 0
  | n+1 => match k with
    | 0 => e n
    | k+1 => insertAt k (fun j => e (j+1)) x n

def skip (k : Nat) : Nat → Nat
  | 0 => match k with
    | 0 => 1
    | _+1 => 0
  | n+1 => match k with
    | 0 => n+2
    | k+1 => skip k n + 1

theorem insert_skip : ∀ (k n : Nat) (e : Env.{u}) (x : PSet.{u}),
    insertAt k e x (skip k n) = e n
  | 0, 0, _, _ => rfl
  | 0, _+1, _, _ => rfl
  | _+1, 0, _, _ => rfl
  | k+1, n+1, e, x => insert_skip k n (fun j => e (j+1)) x

/-- Inserting the collector slot is compatible with renaming the code as well as its formula. -/
theorem real_insert (k : Nat) (a : Form) (e : Env.{u}) (x : PSet.{u}) (c : Code) :
    Real a e c ↔ Real (a.rename (skip k)) (insertAt k e x) (c.rename (skip k)) :=
  real_rename a (skip k) e (insertAt k e x) c fun n =>
    (insert_skip k n e x).symm ▸ Equiv.refl (e n)

/-- The earlier missing witness can now be passed, even though it is absent from the conclusion. -/
theorem member_witness (e : Env.{u}) (h : e 0 ∈ e 1) :
    Real (.ex (.mem 0 2)) e (.packVar 0 .atom) := h

private def w : PSet.{u} := singleton empty
private def z : PSet.{u} := singleton w
private def envWith : Env.{u} := PSet.Env.cons z (PSet.Env.cons w (fun _ => empty))
private def envWithout : Env.{u} := PSet.Env.cons z (fun _ => empty)

/-- The formula's sole free variable is 0, equal in the two environments. -/
theorem formula_parameter_agrees : envWith.{u} 0 ≈ envWithout.{u} 0 := Equiv.refl _

theorem extra_slot_supplies_witness :
    Real (.ex (.mem 0 1)) envWith.{u} (.packVar 1 .atom) :=
  mem_singleton.2 (Equiv.refl _)

theorem resetting_extra_slot_loses_witness :
    ¬ Real (.ex (.mem 0 1)) envWithout.{u} (.packVar 1 .atom) := by
  intro h
  have he : empty ≈ w := mem_singleton.1 h
  have hm : empty ∈ w := mem_singleton.2 (Equiv.refl _)
  exact not_mem_empty empty ((mem_congr_right he.symm).1 hm)

#print axioms ex_intro_var
#print axioms and_elim
#print axioms real_rename
#print axioms real_insert
#print axioms member_witness
#print axioms extra_slot_supplies_witness
#print axioms resetting_extra_slot_loses_witness

end PSet.SupportedCoreAudit
