-- Reviewer audit probe (2026-09-26), incorporated verbatim; it checks a natural specialization of conzf26's
-- cumulative approximation, conditional on the stated application-menu assumptions, not every step-indexed
-- semantics. Empty axiom reports.
import ConZF.RelMachine

/-!
Audit of conzf26's cumulative approximation proposal.

This is its propositional negative fragment with menu-valued application.
Applications are represented by a relation on small codes, so their candidate
menus are subtypes of RCode. The theorem is conditional on one code having
ready application menus at depth zero at the type Top -> Bottom.

The condition holds for menus of all syntactic reducts (reflexivity suffices).
Under that condition the cumulative clauses reject the intuitionistic theorem
Top -> not-not Top. A different, explicitly certified AppView might reject this
shallow pseudo-function; the note has not defined those views. The theorem does
not rule out all step-indexed semantics.
-/
namespace PSet.CumulativeFuelAudit
open RelM

inductive Form : Type
  | top
  | bot
  | imp (a b : Form)

abbrev AppRel := Nat → Form → Form → RCode → RCode → RCode → Prop

def Approx (app : AppRel) : Nat → Form → RCode → Prop
  | 0, _, _ => True
  | n+1, .top, c => Approx app n .top c ∧ True
  | n+1, .bot, c => Approx app n .bot c ∧ False
  | n+1, .imp a b, c => Approx app n (.imp a b) c ∧
      ∀ d, Approx app n a d →
        ¬¬∃ r, app n a b c d r ∧ Approx app n b r

def neg (a : Form) : Form := .imp a .bot

theorem downward (app : AppRel) (n : Nat) (a : Form) (c : RCode) :
    Approx app (n+1) a c → Approx app n a c := by
  cases a <;> exact And.left

theorem shallow_neg_top (app : AppRel) (i : RCode)
    (ready : ∀ d, ¬¬∃ r, app 0 .top .bot i d r) : Approx app 1 (neg .top) i :=
  ⟨True.intro, fun d _ => nn_map (fun ⟨r, hr⟩ => ⟨r, hr, True.intro⟩) (ready d)⟩

theorem no_double_neg_top_at_two (app : AppRel) (i : RCode)
    (ready : ∀ d, ¬¬∃ r, app 0 .top .bot i d r) (c : RCode) :
    ¬ Approx app 2 (neg (neg .top)) c := by
  intro h
  exact h.2 i (shallow_neg_top app i ready) fun ⟨_, _, hr⟩ => hr.2

theorem double_neg_intro_fails (app : AppRel) (i : RCode)
    (ready : ∀ d, ¬¬∃ r, app 0 .top .bot i d r) (c : RCode) :
    ¬ Approx app 3 (.imp .top (neg (neg .top))) c := by
  intro h
  exact h.2 .tok ⟨⟨True.intro, True.intro⟩, True.intro⟩
    fun ⟨r, _, hr⟩ => no_double_neg_top_at_two app i ready r hr

def reducts : AppRel := fun _ _ _ c d r => Reduces (.app c d) r

theorem reduct_menu_double_neg_intro_fails (c : RCode) :
    ¬ Approx reducts 3 (.imp .top (neg (neg .top))) c :=
  double_neg_intro_fails reducts .tok
    (fun d => nn_intro ⟨.app .tok d, .refl _⟩) c

#print axioms downward
#print axioms shallow_neg_top
#print axioms no_double_neg_top_at_two
#print axioms double_neg_intro_fails
#print axioms reduct_menu_double_neg_intro_fails

end PSet.CumulativeFuelAudit
