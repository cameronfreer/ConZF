import ConZF.RelMachine
import ConZF.Ord
/-!
Two checked counterexamples against the prototype machine (reviewer, 2026-09-26), kept as
regression cases for any revised semantics. Both are failures of the interpretation's *logical
rules*, not of the theorems proved in `RelMachine.lean`.

1. **Pruning blocks existential introduction.** With `x = {∅}` and `a = {{∅}}`, no code realizes
   `x ∈ a → ∃y (y ∈ a)`: the only unpruned witness of `∃y (y ∈ a)` is `a` itself, and the empty
   witness is not in `a`. A proof may use a witness variable absent from its conclusion, and pruning
   forbids exactly that.
2. **Separation's semantic menus are not consumable by projection.** `app sepFwd tok` realizes
   `x = x ∧ ∃y (y = y)` through the semantic pair entries of `AndHeads`, but `snd (app sepFwd tok)`
   does not realize `∃y (y = y)`, since `snd` only follows syntactic reduction to pairs.

These two theorems describe the current defects; they are not success criteria. A repaired
semantics should invalidate both and replace them by positive tests of unrestricted introduction
and of the consumption of Separation-generated menus.
-/
namespace PSet.RelM

/-! ### 1. Pruning versus existential introduction -/

def testS : PSet := singleton empty
def testT : PSet := singleton testS
def testE : Env := Env.cons testS (fun _ => testT)

theorem empty_not_testT : ¬ empty ∈ testT := by
  intro h
  have he : empty ≈ testS := mem_singleton.1 h
  have hm : empty ∈ testS := mem_singleton.2 (Equiv.refl _)
  exact not_mem_empty empty ((mem_congr_right he.symm).1 hm)

theorem witness_not_testT (r : RCode) : ¬ witness (.mem 0 2) testE r ∈ testT := by
  cases r with
  | exIntro j c =>
    rw [witness_exIntro]
    cases j with
    | zero => exact empty_not_testT
    | succ j =>
      cases j with
      | zero => exact not_mem_self testT
      | succ j => exact empty_not_testT
  | tok => exact empty_not_testT
  | k => exact empty_not_testT
  | s => exact empty_not_testT
  | app _ _ => exact empty_not_testT
  | pair _ _ => exact empty_not_testT
  | fst _ => exact empty_not_testT
  | snd _ => exact empty_not_testT
  | gen _ => exact empty_not_testT
  | exIntroE _ => exact empty_not_testT
  | sepAx => exact empty_not_testT
  | sepBody => exact empty_not_testT
  | sepIff => exact empty_not_testT
  | sepFwd => exact empty_not_testT
  | sepBwd => exact empty_not_testT

theorem no_exists_realizer (c : RCode) : ¬ Realizes (.ex (.mem 0 2)) testE c := by
  intro h
  exact (realizes_ex.1 h).1 fun ⟨r⟩ =>
    witness_not_testT r.1 (realizes_mem.1 ((realizes_ex.1 h).2 r))

/-- **No code realizes `x ∈ a → ∃y (y ∈ a)` at `x = {∅}`, `a = {{∅}}`.** -/
theorem no_logical_intro_realizer (c : RCode) :
    ¬ Realizes (.imp (.mem 0 1) (.ex (.mem 0 2))) testE c := by
  intro h
  have ha : Realizes (.mem 0 1) testE .tok := realizes_mem.2 (mem_singleton.2 (Equiv.refl _))
  exact no_exists_realizer _ ((realizes_imp.1 h) .tok ha)

/-! ### 2. Semantic conjunction menus versus projection -/

def projectionA : IFml := .eq 0 0
def projectionB : IFml := .ex (.eq 0 0)
def projectionCode : RCode := .app .sepFwd .tok

theorem semantic_pair_realizes (e : Env) : Realizes (.and projectionA projectionB) e projectionCode := by
  have hb : Realizes projectionB e (.exIntroE .tok) := ex_intro_empty (realizes_eq.2 (Equiv.refl _))
  refine realizes_and.2 ⟨nn_intro ⟨⟨.pair .tok (.exIntroE .tok),
    Or.inr ⟨rfl, rfl, ⟨.tok, .refl _⟩, hb⟩⟩⟩, ?_⟩
  intro r
  rcases r.2 with ⟨hr, hp⟩ | ⟨_, _, _, hb'⟩
  · have hh := reduces_app_sepFwd hr
    exact Bool.noConfusion ((congrArg isPair hh).symm.trans hp)
  · exact ⟨realizes_eq.2 (Equiv.refl _), hb'⟩

theorem projectionCode_no_step {r : RCode} (h : Step projectionCode r) : False := by
  cases h with
  | appL h => exact step_sepFwd h

theorem snd_projectionCode_no_step {r : RCode} (h : Step (.snd projectionCode) r) : False := by
  cases h with
  | sndC h => exact projectionCode_no_step h

/-- **The right projection of a semantic pair realizer does not realize the right conjunct.** -/
theorem semantic_pair_snd_not_realizes (e : Env) : ¬ Realizes projectionB e (.snd projectionCode) := by
  intro h
  apply (realizes_ex.1 h).1
  intro ⟨r⟩
  rcases r with ⟨r, hr, hp⟩
  cases hr with
  | refl => exact Bool.noConfusion hp
  | step hs _ => exact snd_projectionCode_no_step hs

/-- info: 'PSet.RelM.no_logical_intro_realizer' does not depend on any axioms -/
#guard_msgs in #print axioms no_logical_intro_realizer
/-- info: 'PSet.RelM.semantic_pair_realizes' does not depend on any axioms -/
#guard_msgs in #print axioms semantic_pair_realizes
/-- info: 'PSet.RelM.semantic_pair_snd_not_realizes' does not depend on any axioms -/
#guard_msgs in #print axioms semantic_pair_snd_not_realizes

end PSet.RelM
