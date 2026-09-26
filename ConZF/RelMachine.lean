import ConZF.Fml
/-!
A relational small-code realizability machine: a focused prototype (conzf24, con64).

Formulas `IFml` have positive `∃`, `∧`, `↔`; codes `RCode` are a small syntax in `Type`; reduction
`Reduces` is the reflexive transitive closure of a syntactic `Step`; the semantics `SemN` is a
fuelled structural recursion (all recursive calls at fuel `n` from fuel `n+1`), so every
unfolding is definitional, and `Realizes φ e c` is its second component at fuel `size φ`. The first
component is the actual **witness readback** `witness a e r` of an existential head `r`:
`e j` for `exIntro j` (pruned, see below), `∅` for `exIntroE`, and the native `sep` at the
realizability predicate of the matrix for the Separation head `sepAx`. Head menus are subtypes of
`RCode`, small index types; validity asserts only their negative inhabitation (`Ready`).

* `semN_stmt`: jointly, fuel irrelevance and **agreement**: realizability and witnesses respect,
  up to bisimulation, environments agreeing on the variables mentioned in the formula
  (`realizes_resp`, `witness_resp`).
* `ex_witness`, `ex_elim`, `ex_intro_var`, `ex_intro_empty`: readiness with actual payloads,
  elimination into stable goals with no head selected, and the two introductions.
* `sep_realizes`: **the Separation axiom code realizes every instance** `∃b ∀z (z ∈ b ↔ z ∈ a ∧ χ)`
  whose matrix does not mention `b`; the forward clause returns every code realizing the matrix,
  the backward clause consumes readiness only.
* `collect`, `collect_forward`, `collect_backward`: from a realizer of `∀x ∈ a ∃y θ`, the native
  `range` over the sum of the gen heads, the existential heads of their instances, and the literal
  indices of `a`, with the witness readback as payload, is a collecting set satisfying both
  Collection clauses; no menu family is supplied. `collect_sep`: the collector is a base for
  Separation.

The design commitment that makes Separation sound: a **variable witness is pruned to the free
variables of the existential** (`exIntro j` reads `e j` only if `j` is free in `ex φ`, else `∅`).
Without it, a code realizing the matrix `χ` of a Separation instance could read the slot of the set
being separated, and the backward clause of the axiom would fail (`χ = ∃w (w ∈ z)` read at that
slot); with it, realizability is invariant under unmentioned slots, and the separating set is
`sep (fun z => ¬¬∃ c, Realizes χ (cons z (cons ∅ e)) c) a`.

* `step_det`, `realizes_of_reduces`, `k_realizes`, `s_realizes`: one-step reduction is
  deterministic, heads are normal, so a code and its reducts have the same normal heads and the same
  realizability; the two combinators follow. **Infrastructure only.**

**Known failures of the logical rules**, checked in `RelMachineTests.lean` (reviewer, 2026-09-26):
pruning blocks existential introduction with a witness variable absent from the conclusion, and the
semantic pair entries supplied by the forward Separation code are not consumable by `snd`. The
prototype therefore does not yet validate ordinary intuitionistic inference. What the prover found
when trying to repair it, stated with its scope: for *this* Separation interpretation, dropping
pruning lets a matrix realizer read the slot of the set being separated, so the backward clause
would need the separating predicate at an environment already containing the set, and no
fixed-point construction for that has been supplied; restricting codes not to read that slot is
not preserved by compilation, since a derivation may use the eigenvariable of a Separation
instance as a witness inside its own matrix; and the one repair tried for the eliminators, a code
whose heads are those of every realizer of the same formula, is a same-size query whose fuel slack
grows with nesting depth, so it breaks fuel irrelevance. None of this rules out a contextual or
certified interpretation with explicitly composed menus; see `Audit/SupportedCore.lean` for a
checked context interface with unrestricted introduction and joint renaming, and
`Audit/RawCollector.lean`, `Audit/WitnessErasure.lean` for two constraints any such design must
respect. Not done: a code for the Collection axiom formula, adequacy for any translated proof.
-/
universe u

namespace PSet.RelM

/-! ### Formulas -/

inductive IFml : Type
  | mem (i j : Nat)
  | eq (i j : Nat)
  | fls
  | imp (a b : IFml)
  | and (a b : IFml)
  | iff (a b : IFml)
  | all (a : IFml)
  | ex (a : IFml)

namespace IFml

def rename (ρ : Nat → Nat) : IFml → IFml
  | mem i j => mem (ρ i) (ρ j)
  | eq i j => eq (ρ i) (ρ j)
  | fls => fls
  | imp a b => imp (rename ρ a) (rename ρ b)
  | and a b => and (rename ρ a) (rename ρ b)
  | iff a b => iff (rename ρ a) (rename ρ b)
  | all a => all (rename (Fml.up ρ) a)
  | ex a => ex (rename (Fml.up ρ) a)

def size : IFml → Nat
  | mem _ _ => 1
  | eq _ _ => 1
  | fls => 1
  | imp a b => size a + size b + 1
  | and a b => size a + size b + 1
  | iff a b => size a + size b + 1
  | all a => size a + 1
  | ex a => size a + 1

theorem size_rename (ρ : Nat → Nat) : ∀ φ, size (rename ρ φ) = size φ
  | mem _ _ => rfl
  | eq _ _ => rfl
  | fls => rfl
  | imp a b => by simp only [rename, size, size_rename ρ a, size_rename ρ b]
  | and a b => by simp only [rename, size, size_rename ρ a, size_rename ρ b]
  | iff a b => by simp only [rename, size, size_rename ρ a, size_rename ρ b]
  | all a => by simp only [rename, size, size_rename (Fml.up ρ) a]
  | ex a => by simp only [rename, size, size_rename (Fml.up ρ) a]

/-- Variable `n` occurs free. -/
def mentions : IFml → Nat → Bool
  | mem i j, n => (Nat.beq i n || Nat.beq j n)
  | eq i j, n => (Nat.beq i n || Nat.beq j n)
  | fls, _ => false
  | imp a b, n => (mentions a n || mentions b n)
  | and a b, n => (mentions a n || mentions b n)
  | iff a b, n => (mentions a n || mentions b n)
  | all a, n => mentions a (n+1)
  | ex a, n => mentions a (n+1)

theorem lt_size_left {a b : IFml} : size a < size a + size b + 1 :=
  Nat.lt_succ_of_le (Nat.le_add_right _ _)
theorem lt_size_right {a b : IFml} : size b < size a + size b + 1 :=
  Nat.lt_succ_of_le (Nat.le_add_left _ _)

end IFml

/-! ### Codes and reduction -/

/-- Small codes. The axiom codes carry no formula: the formula supplies everything. -/
inductive RCode : Type
  | tok
  | k
  | s
  | app (c d : RCode)
  | pair (c d : RCode)
  | fst (c : RCode)
  | snd (c : RCode)
  | gen (c : RCode)
  /-- existential introduction with the witness `e j`, pruned to the free variables -/
  | exIntro (j : Nat) (c : RCode)
  /-- existential introduction with the witness `∅` -/
  | exIntroE (c : RCode)
  /-- the Separation axiom: a head of its existential -/
  | sepAx
  | sepBody
  | sepIff
  | sepFwd
  | sepBwd

/-- One syntactic reduction step. -/
inductive Step : RCode → RCode → Prop
  | k {a b} : Step (.app (.app .k a) b) a
  | s {a b c} : Step (.app (.app (.app .s a) b) c) (.app (.app a c) (.app b c))
  | fst {a b} : Step (.fst (.pair a b)) a
  | snd {a b} : Step (.snd (.pair a b)) b
  | appL {c c' d} : Step c c' → Step (.app c d) (.app c' d)
  | fstC {c c'} : Step c c' → Step (.fst c) (.fst c')
  | sndC {c c'} : Step c c' → Step (.snd c) (.snd c')
  | sepBody : Step .sepBody (.gen .sepIff)
  | sepIff : Step .sepIff (.pair .sepFwd .sepBwd)
  | sepBwd {d} : Step (.app .sepBwd d) .tok

/-- Reduction: the reflexive transitive closure of `Step`. -/
inductive Reduces : RCode → RCode → Prop
  | refl (c) : Reduces c c
  | step {a b c} : Step a b → Reduces b c → Reduces a c

theorem Reduces.trans {a b c : RCode} (h1 : Reduces a b) (h2 : Reduces b c) : Reduces a c := by
  induction h1 with
  | refl => exact h2
  | step s _ ih => exact .step s (ih h2)

theorem Reduces.single {a b : RCode} (h : Step a b) : Reduces a b := .step h (.refl _)

theorem Reduces.appL {c c' d : RCode} (h : Reduces c c') : Reduces (.app c d) (.app c' d) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.appL s) ih

/-- Existential heads. -/
def isExHead : RCode → Bool
  | .tok => false
  | .k => false
  | .s => false
  | .app _ _ => false
  | .pair _ _ => false
  | .fst _ => false
  | .snd _ => false
  | .gen _ => false
  | .exIntro _ _ => true
  | .exIntroE _ => true
  | .sepAx => true
  | .sepBody => false
  | .sepIff => false
  | .sepFwd => false
  | .sepBwd => false

/-- The body code of an existential head; `tok` elsewhere. -/
def exBody : RCode → RCode
  | .tok => .tok
  | .k => .tok
  | .s => .tok
  | .app _ _ => .tok
  | .pair _ _ => .tok
  | .fst _ => .tok
  | .snd _ => .tok
  | .gen _ => .tok
  | .exIntro _ c => c
  | .exIntroE c => c
  | .sepAx => .sepBody
  | .sepBody => .tok
  | .sepIff => .tok
  | .sepFwd => .tok
  | .sepBwd => .tok

def isGen : RCode → Bool
  | .tok => false
  | .k => false
  | .s => false
  | .app _ _ => false
  | .pair _ _ => false
  | .fst _ => false
  | .snd _ => false
  | .gen _ => true
  | .exIntro _ _ => false
  | .exIntroE _ => false
  | .sepAx => false
  | .sepBody => false
  | .sepIff => false
  | .sepFwd => false
  | .sepBwd => false

def genBody : RCode → RCode
  | .tok => .tok
  | .k => .tok
  | .s => .tok
  | .app _ _ => .tok
  | .pair _ _ => .tok
  | .fst _ => .tok
  | .snd _ => .tok
  | .gen c => c
  | .exIntro _ _ => .tok
  | .exIntroE _ => .tok
  | .sepAx => .tok
  | .sepBody => .tok
  | .sepIff => .tok
  | .sepFwd => .tok
  | .sepBwd => .tok

def isPair : RCode → Bool
  | .tok => false
  | .k => false
  | .s => false
  | .app _ _ => false
  | .pair _ _ => true
  | .fst _ => false
  | .snd _ => false
  | .gen _ => false
  | .exIntro _ _ => false
  | .exIntroE _ => false
  | .sepAx => false
  | .sepBody => false
  | .sepIff => false
  | .sepFwd => false
  | .sepBwd => false

def pairFst : RCode → RCode
  | .tok => .tok
  | .k => .tok
  | .s => .tok
  | .app _ _ => .tok
  | .pair c _ => c
  | .fst _ => .tok
  | .snd _ => .tok
  | .gen _ => .tok
  | .exIntro _ _ => .tok
  | .exIntroE _ => .tok
  | .sepAx => .tok
  | .sepBody => .tok
  | .sepIff => .tok
  | .sepFwd => .tok
  | .sepBwd => .tok

def pairSnd : RCode → RCode
  | .tok => .tok
  | .k => .tok
  | .s => .tok
  | .app _ _ => .tok
  | .pair _ d => d
  | .fst _ => .tok
  | .snd _ => .tok
  | .gen _ => .tok
  | .exIntro _ _ => .tok
  | .exIntroE _ => .tok
  | .sepAx => .tok
  | .sepBody => .tok
  | .sepIff => .tok
  | .sepFwd => .tok
  | .sepBwd => .tok

def isSepFwd : RCode → Bool
  | .tok => false
  | .k => false
  | .s => false
  | .app _ _ => false
  | .pair _ _ => false
  | .fst _ => false
  | .snd _ => false
  | .gen _ => false
  | .exIntro _ _ => false
  | .exIntroE _ => false
  | .sepAx => false
  | .sepBody => false
  | .sepIff => false
  | .sepFwd => true
  | .sepBwd => false

/-- Negative inhabitation of an index type. -/
def Ready (I : Type u) : Prop := ¬¬Nonempty I

abbrev Env := Nat → PSet.{u}

/-- The heads reached from `c` satisfying a Boolean test. -/
abbrev Heads (c : RCode) (p : RCode → Bool) : Type := {r : RCode // Reduces c r ∧ p r = true}

/-- The witness of an existential head, given the Separation witness for this formula. -/
def headWit (a : IFml) (e : Env.{u}) (sepW : PSet.{u}) : RCode → PSet.{u}
  | .tok => empty
  | .k => empty
  | .s => empty
  | .app _ _ => empty
  | .pair _ _ => empty
  | .fst _ => empty
  | .snd _ => empty
  | .gen _ => empty
  | .exIntro j _ => cond (IFml.mentions (.ex a) j) (e j) empty
  | .exIntroE _ => empty
  | .sepAx => sepW
  | .sepBody => empty
  | .sepIff => empty
  | .sepFwd => empty
  | .sepBwd => empty

/-! The Separation shape `z ∈ b ↔ (z ∈ a ∧ χ)`, under the binders `z, b`, with `a` the variable
`n` of the outer environment; written with exhaustive matches (overlapping patterns with numeral
literals compile to matchers using propext on this toolchain). -/

def isMem01 : IFml → Bool
  | .mem i j => Nat.beq i 0 && Nat.beq j 1
  | .eq _ _ => false
  | .fls => false
  | .imp _ _ => false
  | .and _ _ => false
  | .iff _ _ => false
  | .all _ => false
  | .ex _ => false

def isMem0Ge2 : IFml → Bool
  | .mem i j => Nat.beq i 0 && Nat.ble 2 j
  | .eq _ _ => false
  | .fls => false
  | .imp _ _ => false
  | .and _ _ => false
  | .iff _ _ => false
  | .all _ => false
  | .ex _ => false

/-- The variable of the second atom, minus two. -/
def memVar : IFml → Nat
  | .mem _ j => j - 2
  | .eq _ _ => 0
  | .fls => 0
  | .imp _ _ => 0
  | .and _ _ => 0
  | .iff _ _ => 0
  | .all _ => 0
  | .ex _ => 0

def andLeft : IFml → IFml
  | .mem _ _ => .fls
  | .eq _ _ => .fls
  | .fls => .fls
  | .imp _ _ => .fls
  | .and a _ => a
  | .iff _ _ => .fls
  | .all _ => .fls
  | .ex _ => .fls

def andRight : IFml → IFml
  | .mem _ _ => .fls
  | .eq _ _ => .fls
  | .fls => .fls
  | .imp _ _ => .fls
  | .and _ b => b
  | .iff _ _ => .fls
  | .all _ => .fls
  | .ex _ => .fls

def isAnd : IFml → Bool
  | .mem _ _ => false
  | .eq _ _ => false
  | .fls => false
  | .imp _ _ => false
  | .and _ _ => true
  | .iff _ _ => false
  | .all _ => false
  | .ex _ => false

def iffLeft : IFml → IFml
  | .mem _ _ => .fls
  | .eq _ _ => .fls
  | .fls => .fls
  | .imp _ _ => .fls
  | .and _ _ => .fls
  | .iff a _ => a
  | .all _ => .fls
  | .ex _ => .fls

def iffRight : IFml → IFml
  | .mem _ _ => .fls
  | .eq _ _ => .fls
  | .fls => .fls
  | .imp _ _ => .fls
  | .and _ _ => .fls
  | .iff _ b => b
  | .all _ => .fls
  | .ex _ => .fls

def isIff : IFml → Bool
  | .mem _ _ => false
  | .eq _ _ => false
  | .fls => false
  | .imp _ _ => false
  | .and _ _ => false
  | .iff _ _ => true
  | .all _ => false
  | .ex _ => false

/-- `a = iff (mem 0 1) (and (mem 0 (n+2)) χ)`. -/
def sepShape (a : IFml) : Bool :=
  isIff a && isMem01 (iffLeft a) && isAnd (iffRight a) && isMem0Ge2 (andLeft (iffRight a))

def sepMat (a : IFml) : IFml := andRight (iffRight a)

def sepVar (a : IFml) : Nat := memVar (andLeft (iffRight a))

theorem size_andRight_le : ∀ a : IFml, IFml.size (andRight a) ≤ IFml.size a
  | .mem _ _ => Nat.le_refl _
  | .eq _ _ => Nat.le_refl _
  | .fls => Nat.le_refl _
  | .imp _ _ => Nat.succ_le_succ (Nat.zero_le _)
  | .and _ _ => Nat.le_succ_of_le (Nat.le_add_left _ _)
  | .iff _ _ => Nat.succ_le_succ (Nat.zero_le _)
  | .all _ => Nat.succ_le_succ (Nat.zero_le _)
  | .ex _ => Nat.succ_le_succ (Nat.zero_le _)

theorem size_iffRight_le : ∀ a : IFml, IFml.size (iffRight a) ≤ IFml.size a
  | .mem _ _ => Nat.le_refl _
  | .eq _ _ => Nat.le_refl _
  | .fls => Nat.le_refl _
  | .imp _ _ => Nat.succ_le_succ (Nat.zero_le _)
  | .and _ _ => Nat.succ_le_succ (Nat.zero_le _)
  | .iff _ _ => Nat.le_succ_of_le (Nat.le_add_left _ _)
  | .all _ => Nat.succ_le_succ (Nat.zero_le _)
  | .ex _ => Nat.succ_le_succ (Nat.zero_le _)

theorem size_sepMat_le (a : IFml) : IFml.size (sepMat a) ≤ IFml.size a :=
  Nat.le_trans (size_andRight_le _) (size_iffRight_le a)

/-! ### Realizability -/

/-- The semantics of an implication: applying to any code realizing the antecedent realizes the
consequent. Results are read off the heads reached by the application. -/
def ImpSem (SA SB : RCode → Prop) (c : RCode) : Prop := ∀ d, SA d → SB (.app c d)

/-- The pair heads of `c` at a conjunction whose right conjunct has semantics `SB`: syntactic pair
reducts, and, when `c` reduces to a forward Separation application, every `pair tok c'` with `c'`
realizing the right conjunct. -/
abbrev AndHeads (SB : RCode → Prop) (c : RCode) : Type :=
  {r : RCode // (Reduces c r ∧ isPair r = true) ∨
    (isPair r = true ∧ pairFst r = .tok ∧ (∃ d, Reduces c (.app .sepFwd d)) ∧ SB (pairSnd r))}

/-- The fuelled semantics: at fuel `n+1`, a formula's clause with all recursive calls at fuel `n`.
The first component is the witness of the code taken as an existential head of `ex φ`; the second
is realizability. Structural recursion, so every unfolding is definitional. -/
def SemN : Nat → IFml → Env.{u} → RCode → PSet.{u} × Prop
  | 0, _, _, _ => (empty, False)
  | _+1, .mem i j, e, c => (headWit (.mem i j) e empty c, e i ∈ e j)
  | _+1, .eq i j, e, c => (headWit (.eq i j) e empty c, e i ≈ e j)
  | _+1, .fls, e, c => (headWit .fls e empty c, False)
  | n+1, .imp a b, e, c => (headWit (.imp a b) e empty c,
      ImpSem (fun d => (SemN n a e d).2) (fun r => (SemN n b e r).2) c)
  | n+1, .and a b, e, c => (headWit (.and a b) e empty c,
      Ready (AndHeads (fun r => (SemN n b e r).2) c) ∧
      ∀ r : AndHeads (fun r => (SemN n b e r).2) c, (SemN n a e (pairFst r.1)).2 ∧ (SemN n b e (pairSnd r.1)).2)
  | n+1, .iff a b, e, c => (headWit (.iff a b) e empty c, Ready (Heads c isPair) ∧
      ∀ r : Heads c isPair,
        ImpSem (fun d => (SemN n a e d).2) (fun r => (SemN n b e r).2) (pairFst r.1) ∧
        ImpSem (fun d => (SemN n b e d).2) (fun r => (SemN n a e r).2) (pairSnd r.1))
  | n+1, .all a, e, c => (headWit (.all a) e (cond (sepShape a)
        (sep (fun z => ¬¬∃ c', (SemN n (sepMat a) (Env.cons z (Env.cons empty e)) c').2) (e (sepVar a)))
        empty) c,
      ∀ x : PSet.{u}, Ready (Heads c isGen) ∧ ∀ r : Heads c isGen, (SemN n a (Env.cons x e) (genBody r.1)).2)
  | n+1, .ex a, e, c => (headWit (.ex a) e empty c, Ready (Heads c isExHead) ∧
      ∀ r : Heads c isExHead, (SemN n a (Env.cons (SemN n a e r.1).1 e) (exBody r.1)).2)

/-- `c` realizes `φ` at `e`: the fuelled semantics at fuel the size of `φ`. -/
def Realizes (φ : IFml) (e : Env.{u}) (c : RCode) : Prop := (SemN (IFml.size φ) φ e c).2

/-- The witness of `r` as a head of `ex a` at `e`. -/
def witness (a : IFml) (e : Env.{u}) (r : RCode) : PSet.{u} := (SemN (IFml.size a) a e r).1

/-! ### Inversion of reduction from constants and heads -/

theorem step_sepAx {r : RCode} (h : Step .sepAx r) : False := by cases h
theorem step_sepFwd {r : RCode} (h : Step .sepFwd r) : False := by cases h
theorem step_sepBwd {r : RCode} (h : Step .sepBwd r) : False := by cases h
theorem step_tok {r : RCode} (h : Step .tok r) : False := by cases h
theorem step_gen {x r : RCode} (h : Step (.gen x) r) : False := by cases h
theorem step_pair {x y r : RCode} (h : Step (.pair x y) r) : False := by cases h
theorem step_exIntro {j : Nat} {x r : RCode} (h : Step (.exIntro j x) r) : False := by cases h
theorem step_exIntroE {x r : RCode} (h : Step (.exIntroE x) r) : False := by cases h

theorem reduces_sepAx {r : RCode} (h : Reduces .sepAx r) : r = .sepAx := by
  cases h with
  | refl => rfl
  | step h1 _ => exact (step_sepAx h1).elim
theorem reduces_sepFwd {r : RCode} (h : Reduces .sepFwd r) : r = .sepFwd := by
  cases h with
  | refl => rfl
  | step h1 _ => exact (step_sepFwd h1).elim
theorem reduces_sepBwd {r : RCode} (h : Reduces .sepBwd r) : r = .sepBwd := by
  cases h with
  | refl => rfl
  | step h1 _ => exact (step_sepBwd h1).elim
theorem reduces_tok {r : RCode} (h : Reduces .tok r) : r = .tok := by
  cases h with
  | refl => rfl
  | step h1 _ => exact (step_tok h1).elim
theorem reduces_gen {x r : RCode} (h : Reduces (.gen x) r) : r = .gen x := by
  cases h with
  | refl => rfl
  | step h1 _ => exact (step_gen h1).elim
theorem reduces_pair {x y r : RCode} (h : Reduces (.pair x y) r) : r = .pair x y := by
  cases h with
  | refl => rfl
  | step h1 _ => exact (step_pair h1).elim
theorem reduces_exIntro {j : Nat} {x r : RCode} (h : Reduces (.exIntro j x) r) : r = .exIntro j x := by
  cases h with
  | refl => rfl
  | step h1 _ => exact (step_exIntro h1).elim
theorem reduces_exIntroE {x r : RCode} (h : Reduces (.exIntroE x) r) : r = .exIntroE x := by
  cases h with
  | refl => rfl
  | step h1 _ => exact (step_exIntroE h1).elim
theorem reduces_sepIff {r : RCode} (h : Reduces .sepIff r) : r = .sepIff ∨ r = .pair .sepFwd .sepBwd := by
  cases h with
  | refl => exact .inl rfl
  | step h1 h2 => cases h1; exact .inr (reduces_pair h2)
theorem reduces_sepBody {r : RCode} (h : Reduces .sepBody r) : r = .sepBody ∨ r = .gen .sepIff := by
  cases h with
  | refl => exact .inl rfl
  | step h1 h2 => cases h1; exact .inr (reduces_gen h2)
theorem reduces_app_sepFwd {d r : RCode} (h : Reduces (.app .sepFwd d) r) : r = .app .sepFwd d := by
  cases h with
  | refl => rfl
  | step h1 _ => cases h1 with | appL h' => exact (step_sepFwd h').elim
theorem reduces_app_sepBwd {d r : RCode} (h : Reduces (.app .sepBwd d) r) :
    r = .app .sepBwd d ∨ r = .tok := by
  cases h with
  | refl => exact .inl rfl
  | step h1 h2 =>
    cases h1 with
    | appL h' => exact (step_sepBwd h').elim
    | sepBwd => exact .inr (reduces_tok h2)

/-! ### Fuel irrelevance and agreement on the mentioned variables, up to bisimulation -/

theorem bor_left {a b : Bool} (h : a = true) : (a || b) = true := by
  cases a
  · exact Bool.noConfusion h
  · rfl
theorem bor_right {a b : Bool} (h : b = true) : (a || b) = true := by
  cases a
  · exact h
  · rfl
theorem band_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a
  · exact Bool.noConfusion h
  · exact ⟨rfl, h⟩
theorem beq_self : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n+1 => beq_self n

/-- `e` and `e'` agree, up to bisimulation, on the variables mentioned in `φ`. -/
def Agree (φ : IFml) (e e' : Env.{u}) : Prop := ∀ n, IFml.mentions φ n = true → e n ≈ e' n

namespace Agree
variable {a b : IFml} {e e' : Env.{u}}
theorem imp_left (h : Agree (.imp a b) e e') : Agree a e e' := fun n hn => h n (bor_left hn)
theorem imp_right (h : Agree (.imp a b) e e') : Agree b e e' := fun n hn => h n (bor_right hn)
theorem and_left (h : Agree (.and a b) e e') : Agree a e e' := fun n hn => h n (bor_left hn)
theorem and_right (h : Agree (.and a b) e e') : Agree b e e' := fun n hn => h n (bor_right hn)
theorem iff_left (h : Agree (.iff a b) e e') : Agree a e e' := fun n hn => h n (bor_left hn)
theorem iff_right (h : Agree (.iff a b) e e') : Agree b e e' := fun n hn => h n (bor_right hn)
theorem cons_all (h : Agree (.all a) e e') {x x' : PSet.{u}} (hx : x ≈ x') :
    Agree a (Env.cons x e) (Env.cons x' e')
  | 0, _ => hx
  | n+1, hn => h n hn
theorem cons_ex (h : Agree (.ex a) e e') {x x' : PSet.{u}} (hx : x ≈ x') :
    Agree a (Env.cons x e) (Env.cons x' e')
  | 0, _ => hx
  | n+1, hn => h n hn
theorem refl (φ : IFml) (e : Env.{u}) : Agree φ e e := fun _ _ => Equiv.refl _
theorem symm (h : Agree a e e') : Agree a e' e := fun n hn => (h n hn).symm
end Agree

theorem impSem_congr {SA SA' SB SB' : RCode → Prop} (hA : ∀ d, SA d ↔ SA' d) (hB : ∀ r, SB r ↔ SB' r)
    (c : RCode) : ImpSem SA SB c ↔ ImpSem SA' SB' c :=
  ⟨fun h d hd => (hB _).1 (h d ((hA d).2 hd)), fun h d hd => (hB _).2 (h d ((hA d).1 hd))⟩

def AndHeads.map {SB SB' : RCode → Prop} (h : ∀ r, SB r → SB' r) {c : RCode} :
    AndHeads SB c → AndHeads SB' c :=
  fun ⟨r, hr⟩ => ⟨r, hr.elim Or.inl fun ⟨hp, hf, hd, hs⟩ => Or.inr ⟨hp, hf, hd, h _ hs⟩⟩

theorem andSem_congr {SA SA' SB SB' : RCode → Prop} (hA : ∀ d, SA d ↔ SA' d) (hB : ∀ r, SB r ↔ SB' r)
    (c : RCode) :
    (Ready (AndHeads SB c) ∧ ∀ r : AndHeads SB c, SA (pairFst r.1) ∧ SB (pairSnd r.1)) ↔
    (Ready (AndHeads SB' c) ∧ ∀ r : AndHeads SB' c, SA' (pairFst r.1) ∧ SB' (pairSnd r.1)) := by
  constructor
  · rintro ⟨hr, hall⟩
    refine ⟨nn_map (fun ⟨r⟩ => ⟨AndHeads.map (fun r => (hB r).1) r⟩) hr, fun r => ?_⟩
    have := hall (AndHeads.map (fun r => (hB r).2) r)
    exact ⟨(hA _).1 this.1, (hB _).1 this.2⟩
  · rintro ⟨hr, hall⟩
    refine ⟨nn_map (fun ⟨r⟩ => ⟨AndHeads.map (fun r => (hB r).2) r⟩) hr, fun r => ?_⟩
    have := hall (AndHeads.map (fun r => (hB r).1) r)
    exact ⟨(hA _).2 this.1, (hB _).2 this.2⟩

theorem headWit_agree (φ : IFml) {e e' : Env.{u}} {w w' : PSet.{u}} (hw : w ≈ w') (H : Agree (.ex φ) e e') :
    ∀ r, headWit φ e w r ≈ headWit φ e' w' r
  | .tok => Equiv.refl _
  | .k => Equiv.refl _
  | .s => Equiv.refl _
  | .app _ _ => Equiv.refl _
  | .pair _ _ => Equiv.refl _
  | .fst _ => Equiv.refl _
  | .snd _ => Equiv.refl _
  | .gen _ => Equiv.refl _
  | .exIntro j _ => by
    show cond (IFml.mentions (.ex φ) j) (e j) empty ≈ cond (IFml.mentions (.ex φ) j) (e' j) empty
    cases hm : IFml.mentions (.ex φ) j
    · exact Equiv.refl _
    · exact H j hm
  | .exIntroE _ => Equiv.refl _
  | .sepAx => hw
  | .sepBody => Equiv.refl _
  | .sepIff => Equiv.refl _
  | .sepFwd => Equiv.refl _
  | .sepBwd => Equiv.refl _

theorem isIff_true : ∀ {a : IFml}, isIff a = true → ∃ l r, a = .iff l r
  | .iff l r, _ => ⟨l, r, rfl⟩
  | .mem _ _, h => absurd h Bool.false_ne_true
  | .eq _ _, h => absurd h Bool.false_ne_true
  | .fls, h => absurd h Bool.false_ne_true
  | .imp _ _, h => absurd h Bool.false_ne_true
  | .and _ _, h => absurd h Bool.false_ne_true
  | .all _, h => absurd h Bool.false_ne_true
  | .ex _, h => absurd h Bool.false_ne_true

theorem isAnd_true : ∀ {a : IFml}, isAnd a = true → ∃ l r, a = .and l r
  | .and l r, _ => ⟨l, r, rfl⟩
  | .mem _ _, h => absurd h Bool.false_ne_true
  | .eq _ _, h => absurd h Bool.false_ne_true
  | .fls, h => absurd h Bool.false_ne_true
  | .imp _ _, h => absurd h Bool.false_ne_true
  | .iff _ _, h => absurd h Bool.false_ne_true
  | .all _, h => absurd h Bool.false_ne_true
  | .ex _, h => absurd h Bool.false_ne_true

theorem isMem01_true : ∀ {a : IFml}, isMem01 a = true → a = .mem 0 1
  | .mem i j, h => by
    obtain ⟨hi, hj⟩ := band_true h
    rw [Nat.eq_of_beq_eq_true hi, Nat.eq_of_beq_eq_true hj]
  | .eq _ _, h => absurd h Bool.false_ne_true
  | .fls, h => absurd h Bool.false_ne_true
  | .imp _ _, h => absurd h Bool.false_ne_true
  | .and _ _, h => absurd h Bool.false_ne_true
  | .iff _ _, h => absurd h Bool.false_ne_true
  | .all _, h => absurd h Bool.false_ne_true
  | .ex _, h => absurd h Bool.false_ne_true

theorem isMem0Ge2_true : ∀ {a : IFml}, isMem0Ge2 a = true → ∃ m, a = .mem 0 (m+2)
  | .mem i j, h => by
    obtain ⟨hi, hj⟩ := band_true h
    rw [Nat.eq_of_beq_eq_true hi]
    match j, hj with
    | m+2, _ => exact ⟨m, rfl⟩
  | .eq _ _, h => absurd h Bool.false_ne_true
  | .fls, h => absurd h Bool.false_ne_true
  | .imp _ _, h => absurd h Bool.false_ne_true
  | .and _ _, h => absurd h Bool.false_ne_true
  | .iff _ _, h => absurd h Bool.false_ne_true
  | .all _, h => absurd h Bool.false_ne_true
  | .ex _, h => absurd h Bool.false_ne_true

theorem sepShape_true {a : IFml} (h : sepShape a = true) :
    ∃ k χ, a = .iff (.mem 0 1) (.and (.mem 0 (k+2)) χ) := by
  unfold sepShape at h
  obtain ⟨h123, h4⟩ := band_true h
  obtain ⟨h12, h3⟩ := band_true h123
  obtain ⟨h1, h2⟩ := band_true h12
  obtain ⟨l, r, rfl⟩ := isIff_true h1
  cases isMem01_true h2
  obtain ⟨p, q, rfl⟩ := isAnd_true h3
  obtain ⟨m, hm⟩ := isMem0Ge2_true h4
  cases hm
  exact ⟨m, q, rfl⟩

theorem sep_congr {P P' : PSet.{u} → Prop} [∀ z, Stable (P z)] [∀ z, Stable (P' z)]
    (hP : ∀ x y, x ≈ y → P x → P y) (hP' : ∀ x y, x ≈ y → P' x → P' y) (hPP' : ∀ z, P z ↔ P' z)
    {x x' : PSet.{u}} (hx : x ≈ x') : sep P x ≈ sep P' x' :=
  ext fun z => (mem_sep hP).trans ((and_congr (mem_congr_right hx) (hPP' z)).trans (mem_sep hP').symm)

theorem size_pos : ∀ φ : IFml, 0 < IFml.size φ
  | .mem _ _ => Nat.succ_pos _
  | .eq _ _ => Nat.succ_pos _
  | .fls => Nat.succ_pos _
  | .imp _ _ => Nat.succ_pos _
  | .and _ _ => Nat.succ_pos _
  | .iff _ _ => Nat.succ_pos _
  | .all _ => Nat.succ_pos _
  | .ex _ => Nat.succ_pos _

theorem mentions_mem (i j n : Nat) : IFml.mentions (.mem i j) n = (Nat.beq i n || Nat.beq j n) := rfl
theorem mentions_and (a b : IFml) (n : Nat) :
    IFml.mentions (.and a b) n = (IFml.mentions a n || IFml.mentions b n) := rfl
theorem mentions_iff (a b : IFml) (n : Nat) :
    IFml.mentions (.iff a b) n = (IFml.mentions a n || IFml.mentions b n) := rfl
theorem mentions_ex_all (a : IFml) (n : Nat) : IFml.mentions (.ex (.all a)) n = IFml.mentions a (n+2) := rfl

/-- The variables mentioned by the Separation shape. -/
theorem mentions_sepShape_var (k : Nat) (χ : IFml) :
    IFml.mentions (.ex (.all (.iff (.mem 0 1) (.and (.mem 0 (k+2)) χ)))) k = true := by
  rw [mentions_ex_all, mentions_iff, mentions_and, mentions_mem]
  exact bor_right (bor_left (bor_right (beq_self _)))

theorem mentions_sepShape_mat (k : Nat) (χ : IFml) {m : Nat} (h : IFml.mentions χ (m+2) = true) :
    IFml.mentions (.ex (.all (.iff (.mem 0 1) (.and (.mem 0 (k+2)) χ)))) m = true := by
  rw [mentions_ex_all, mentions_iff, mentions_and]
  exact bor_right (bor_right h)

theorem size_mat_lt (k : Nat) (χ : IFml) :
    IFml.size χ < IFml.size (.all (.iff (.mem 0 1) (.and (.mem 0 (k+2)) χ))) :=
  Nat.lt_trans (@IFml.lt_size_right (.mem 0 (k+2)) χ)
    (Nat.lt_trans (@IFml.lt_size_right (.mem 0 1) (.and (.mem 0 (k+2)) χ)) (Nat.lt_succ_self _))

/-- The joint statement: at any two sufficient fuels, realizability and witnesses agree, up to
bisimulation, on environments agreeing on the mentioned variables. -/
def Stmt (n m : Nat) (φ : IFml) : Prop :=
  (∀ (e e' : Env.{u}) c, Agree φ e e' → ((SemN n φ e c).2 ↔ (SemN m φ e' c).2)) ∧
  (∀ (e e' : Env.{u}) r, Agree (.ex φ) e e' → (SemN n φ e r).1 ≈ (SemN m φ e' r).1)

theorem semN_stmt : ∀ (n : Nat) (φ : IFml), IFml.size φ ≤ n → ∀ m, IFml.size φ ≤ m → Stmt.{u} n m φ := by
  intro n
  induction n with
  | zero => exact fun φ h => (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le (size_pos φ) h)).elim
  | succ n IH =>
    intro φ hφ m hm
    cases m with
    | zero => exact (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le (size_pos φ) hm)).elim
    | succ m =>
    have sub : ∀ {ψ : IFml}, IFml.size ψ < IFml.size φ → Stmt.{u} n m ψ :=
      fun h => IH _ (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le h hφ)) m (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le h hm))
    have subn : ∀ {ψ : IFml}, IFml.size ψ < IFml.size φ → Stmt.{u} n n ψ :=
      fun h => IH _ (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le h hφ)) n (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le h hφ))
    cases φ with
    | mem i j =>
      refine ⟨fun e e' c H => ?_, fun e e' r H => headWit_agree _ (Equiv.refl _) H r⟩
      exact (mem_congr_left (H i (bor_left (beq_self i)))).trans (mem_congr_right (H j (bor_right (beq_self j))))
    | eq i j =>
      refine ⟨fun e e' c H => ?_, fun e e' r H => headWit_agree _ (Equiv.refl _) H r⟩
      have hi := H i (bor_left (beq_self i))
      have hj := H j (bor_right (beq_self j))
      exact ⟨fun h => hi.symm.trans (h.trans hj), fun h => hi.trans (h.trans hj.symm)⟩
    | fls => exact ⟨fun _ _ _ _ => Iff.rfl, fun e e' r H => headWit_agree _ (Equiv.refl _) H r⟩
    | imp a b =>
      refine ⟨fun e e' c H => ?_, fun e e' r H => headWit_agree _ (Equiv.refl _) H r⟩
      exact impSem_congr (fun d => (sub IFml.lt_size_left).1 e e' d H.imp_left)
        (fun d => (sub IFml.lt_size_right).1 e e' d H.imp_right) c
    | and a b =>
      refine ⟨fun e e' c H => ?_, fun e e' r H => headWit_agree _ (Equiv.refl _) H r⟩
      exact andSem_congr (fun d => (sub IFml.lt_size_left).1 e e' d H.and_left)
        (fun d => (sub IFml.lt_size_right).1 e e' d H.and_right) c
    | iff a b =>
      refine ⟨fun e e' c H => ?_, fun e e' r H => headWit_agree _ (Equiv.refl _) H r⟩
      have ha := fun d => (sub IFml.lt_size_left).1 e e' d H.iff_left
      have hb := fun d => (sub IFml.lt_size_right).1 e e' d H.iff_right
      exact and_congr Iff.rfl (forall_congr' fun r => and_congr (impSem_congr ha hb _) (impSem_congr hb ha _))
    | all a =>
      constructor
      · intro e e' c H
        exact forall_congr' fun x => and_congr Iff.rfl (forall_congr' fun r =>
          (sub (Nat.lt_succ_self _)).1 _ _ _ (H.cons_all (Equiv.refl x)))
      · intro e e' r H
        refine headWit_agree _ ?_ H r
        cases hs : sepShape a
        · exact Equiv.refl _
        · obtain ⟨k, χ, rfl⟩ := sepShape_true hs
          have hχ := size_mat_lt k χ
          have hnm := (sub hχ).1
          have hnn := (subn hχ).1
          show sep (fun z => ¬¬∃ c', (SemN n χ (Env.cons z (Env.cons empty e)) c').2) (e k) ≈
            sep (fun z => ¬¬∃ c', (SemN m χ (Env.cons z (Env.cons empty e')) c').2) (e' k)
          have agr : ∀ (E : Env.{u}) {x y : PSet.{u}}, x ≈ y →
              Agree χ (Env.cons x (Env.cons empty E)) (Env.cons y (Env.cons empty E))
            | _, _, _, hxy, 0, _ => hxy
            | _, _, _, _, n+1, _ => Equiv.refl _
          have agr' : ∀ z : PSet.{u}, Agree χ (Env.cons z (Env.cons empty e)) (Env.cons z (Env.cons empty e'))
            | _, 0, _ => Equiv.refl _
            | _, 1, _ => Equiv.refl _
            | _, m+2, hm => H m (mentions_sepShape_mat k χ hm)
          exact sep_congr (fun x y hxy => nn_map fun ⟨c', hc⟩ => ⟨c', (hnn _ _ c' (agr e hxy)).1 hc⟩)
            (fun x y hxy => nn_map fun ⟨c', hc⟩ => ⟨c',
              (hnm _ _ c' (Agree.refl _ _)).1 ((hnn _ _ c' (agr e' hxy)).1 ((hnm _ _ c' (Agree.refl _ _)).2 hc))⟩)
            (fun z => nn_congr (exists_congr fun c' => hnm _ _ c' (agr' z)))
            (H k (mentions_sepShape_var k χ))
    | ex a =>
      refine ⟨fun e e' c H => ?_, fun e e' r H => headWit_agree _ (Equiv.refl _) H r⟩
      have hs := sub (Nat.lt_succ_self (IFml.size a))
      exact and_congr Iff.rfl (forall_congr' fun r => hs.1 _ _ _ (H.cons_ex (hs.2 e e' r.1 H)))

/-- Fuel irrelevance for realizability. -/
theorem semN_fuel {n m : Nat} {φ : IFml} (h1 : IFml.size φ ≤ n) (h2 : IFml.size φ ≤ m) (e : Env.{u}) (c : RCode) :
    (SemN n φ e c).2 ↔ (SemN m φ e c).2 :=
  (semN_stmt n φ h1 m h2).1 e e c (Agree.refl _ _)

/-- **Realizability respects agreement on the mentioned variables, up to bisimulation.** -/
theorem realizes_resp {φ : IFml} {e e' : Env.{u}} {c : RCode} (H : Agree φ e e') :
    Realizes φ e c ↔ Realizes φ e' c :=
  (semN_stmt _ φ (Nat.le_refl _) _ (Nat.le_refl _)).1 e e' c H

theorem witness_resp {a : IFml} {e e' : Env.{u}} (r : RCode) (H : Agree (.ex a) e e') :
    witness a e r ≈ witness a e' r :=
  (semN_stmt _ a (Nat.le_refl _) _ (Nat.le_refl _)).2 e e' r H

/-! ### Unfolding -/

section
variable {i j : Nat} {a b : IFml} {e : Env.{u}} {c : RCode}

theorem realizes_mem : Realizes (.mem i j) e c ↔ e i ∈ e j := Iff.rfl
theorem realizes_eq : Realizes (.eq i j) e c ↔ e i ≈ e j := Iff.rfl
theorem realizes_fls : Realizes .fls e c ↔ False := Iff.rfl
theorem realizes_imp : Realizes (.imp a b) e c ↔ ImpSem (Realizes a e) (Realizes b e) c :=
  impSem_congr (fun d => semN_fuel (Nat.le_add_right _ _) (Nat.le_refl _) e d)
    (fun r => semN_fuel (Nat.le_add_left _ _) (Nat.le_refl _) e r) c
theorem realizes_and : Realizes (.and a b) e c ↔ Ready (AndHeads (Realizes b e) c) ∧
    ∀ r : AndHeads (Realizes b e) c, Realizes a e (pairFst r.1) ∧ Realizes b e (pairSnd r.1) :=
  andSem_congr (fun d => semN_fuel (Nat.le_add_right _ _) (Nat.le_refl _) e d)
    (fun r => semN_fuel (Nat.le_add_left _ _) (Nat.le_refl _) e r) c
theorem realizes_iff : Realizes (.iff a b) e c ↔ Ready (Heads c isPair) ∧ ∀ r : Heads c isPair,
    ImpSem (Realizes a e) (Realizes b e) (pairFst r.1) ∧ ImpSem (Realizes b e) (Realizes a e) (pairSnd r.1) :=
  and_congr Iff.rfl (forall_congr' fun _ => and_congr
    (impSem_congr (fun d => semN_fuel (Nat.le_add_right _ _) (Nat.le_refl _) e d)
      (fun r => semN_fuel (Nat.le_add_left _ _) (Nat.le_refl _) e r) _)
    (impSem_congr (fun d => semN_fuel (Nat.le_add_left _ _) (Nat.le_refl _) e d)
      (fun r => semN_fuel (Nat.le_add_right _ _) (Nat.le_refl _) e r) _))
theorem realizes_all : Realizes (.all a) e c ↔ ∀ x : PSet.{u}, Ready (Heads c isGen) ∧
    ∀ r : Heads c isGen, Realizes a (Env.cons x e) (genBody r.1) := Iff.rfl
theorem realizes_ex : Realizes (.ex a) e c ↔ Ready (Heads c isExHead) ∧
    ∀ r : Heads c isExHead, Realizes a (Env.cons (witness a e r.1) e) (exBody r.1) := Iff.rfl

theorem witness_exIntro (φ : IFml) (e : Env.{u}) (j : Nat) (c : RCode) :
    witness φ e (.exIntro j c) = cond (IFml.mentions (.ex φ) j) (e j) empty := by
  cases φ <;> rfl
theorem witness_exIntroE (φ : IFml) (e : Env.{u}) (c : RCode) : witness φ e (.exIntroE c) = empty := by
  cases φ <;> rfl

/-- The Separation witness: the native `sep` at the pruned predicate. -/
theorem witness_sepAx (k : Nat) (χ : IFml) (e : Env.{u}) :
    witness (.all (.iff (.mem 0 1) (.and (.mem 0 (k+2)) χ))) e .sepAx ≈
      sep (fun z => ¬¬∃ c', Realizes χ (Env.cons z (Env.cons empty e)) c') (e k) := by
  show sep (fun z => ¬¬∃ c', (SemN (IFml.size (.iff (.mem 0 1) (.and (.mem 0 (k+2)) χ))) χ
      (Env.cons z (Env.cons empty e)) c').2) (e k) ≈ _
  have hle : IFml.size χ ≤ IFml.size (.iff (.mem 0 1) (.and (.mem 0 (k+2)) χ)) :=
    Nat.le_of_lt (Nat.lt_trans (@IFml.lt_size_right (.mem 0 (k+2)) χ)
      (@IFml.lt_size_right (.mem 0 1) (.and (.mem 0 (k+2)) χ)))
  have agr : ∀ {x y : PSet.{u}}, x ≈ y →
      Agree χ (Env.cons x (Env.cons empty e)) (Env.cons y (Env.cons empty e))
    | _, _, hxy, 0, _ => hxy
    | _, _, _, n+1, _ => Equiv.refl _
  refine sep_congr (fun x y hxy => nn_map fun ⟨c', hc⟩ => ⟨c',
      (semN_fuel hle hle _ c').1 ((semN_fuel hle (Nat.le_refl _) _ c').2
        ((realizes_resp (agr hxy)).1 ((semN_fuel hle (Nat.le_refl _) _ c').1 hc)))⟩)
    (fun x y hxy => nn_map fun ⟨c', hc⟩ => ⟨c', (realizes_resp (agr hxy)).1 hc⟩)
    (fun z => nn_congr (exists_congr fun c' => semN_fuel hle (Nat.le_refl _) _ c')) (Equiv.refl _)

end

/-! ### Stability -/

theorem stable_ready (I : Type u) : Stable (Ready I) := inferInstanceAs (Stable (¬ _))

theorem semN_stable : ∀ (n : Nat) (φ : IFml) (e : Env.{u}) (c : RCode), Stable (SemN n φ e c).2
  | 0, _, _, _ => inferInstanceAs (Stable False)
  | _+1, .mem _ _, _, _ => inferInstanceAs (Stable (_ ∈ _))
  | _+1, .eq _ _, _, _ => inferInstanceAs (Stable (_ ≈ _))
  | _+1, .fls, _, _ => inferInstanceAs (Stable False)
  | n+1, .imp _ b, e, c =>
    have := fun d => semN_stable n b e (.app c d)
    inferInstanceAs (Stable (∀ d, _ → (SemN n b e (.app c d)).2))
  | n+1, .and a b, e, c =>
    have := fun r => semN_stable n a e (pairFst r)
    have := fun r => semN_stable n b e (pairSnd r)
    have := stable_ready (AndHeads (fun r => (SemN n b e r).2) c)
    inferInstanceAs (Stable (_ ∧ ∀ _, _ ∧ _))
  | n+1, .iff a b, e, c =>
    have := fun d => semN_stable n b e d
    have := fun d => semN_stable n a e d
    have := stable_ready (Heads c isPair)
    inferInstanceAs (Stable (_ ∧ ∀ _, (∀ _, _ → (SemN n b e _).2) ∧ (∀ _, _ → (SemN n a e _).2)))
  | n+1, .all a, e, c =>
    have := fun x r => semN_stable n a (Env.cons x e) (genBody r)
    have := stable_ready (Heads c isGen)
    inferInstanceAs (Stable (∀ _, _ ∧ ∀ _, _))
  | n+1, .ex a, e, c =>
    have := fun (r' : RCode) => semN_stable n a (Env.cons (SemN n a e r').1 e) (exBody r')
    have := stable_ready (Heads c isExHead)
    inferInstanceAs (Stable (_ ∧ ∀ _, _))

instance {φ : IFml} {e : Env.{u}} {c : RCode} : Stable (Realizes φ e c) := semN_stable _ φ e c

/-! ### Existential introduction and elimination -/

section
variable {a : IFml} {e : Env.{u}} {c : RCode}

/-- **Readiness with payloads**: a realizer of `∃ a` yields, negatively, a head with its actual
witness and body code, the body realizing `a` at the witness. -/
theorem ex_witness (h : Realizes (.ex a) e c) :
    ¬¬∃ r : Heads c isExHead, Realizes a (Env.cons (witness a e r.1) e) (exBody r.1) :=
  nn_map (fun ⟨r⟩ => ⟨r, (realizes_ex.1 h).2 r⟩) (realizes_ex.1 h).1

/-- Existential elimination into a stable goal. No head is selected. -/
theorem ex_elim {G : Prop} [Stable G] (h : Realizes (.ex a) e c)
    (k : ∀ w c', Realizes a (Env.cons w e) c' → G) : G :=
  Stable.of_nn (ex_witness h) fun ⟨_, hr⟩ => k _ _ hr

theorem ex_intro_var (j : Nat) (hj : IFml.mentions (.ex a) j = true)
    (h : Realizes a (Env.cons (e j) e) c) : Realizes (.ex a) e (.exIntro j c) := by
  refine realizes_ex.2 ⟨nn_intro ⟨⟨_, .refl _, rfl⟩⟩, fun ⟨r, hr, _⟩ => ?_⟩
  cases reduces_exIntro hr
  show Realizes a (Env.cons (witness a e (.exIntro j c)) e) c
  rw [witness_exIntro, hj]
  exact h

theorem ex_intro_empty (h : Realizes a (Env.cons empty e) c) : Realizes (.ex a) e (.exIntroE c) := by
  refine realizes_ex.2 ⟨nn_intro ⟨⟨_, .refl _, rfl⟩⟩, fun ⟨r, hr, _⟩ => ?_⟩
  cases reduces_exIntroE hr
  show Realizes a (Env.cons (witness a e (.exIntroE c)) e) c
  rw [witness_exIntroE]
  exact h

end

/-! ### Separation -/

/-- The Separation instance `∃b ∀z (z ∈ b ↔ (z ∈ a ∧ χ))`, `a` the variable `k` of the outer
environment, `χ` under the binders `z, b` (variables `0`, `1`). -/
def sepForm (k : Nat) (χ : IFml) : IFml := .ex (.all (.iff (.mem 0 1) (.and (.mem 0 (k+2)) χ)))

/-- **The Separation axiom code realizes every instance whose matrix does not mention the set
being separated.** The witness is the native `sep` at the pruned predicate; the forward clause
returns every code realizing the matrix, the backward clause uses only readiness. -/
theorem sep_realizes (k : Nat) (χ : IFml) (hχ : IFml.mentions χ 1 = false) (e : Env.{u}) :
    Realizes (sepForm k χ) e .sepAx := by
  let P : PSet.{u} → Prop := fun z => ¬¬∃ c', Realizes χ (Env.cons z (Env.cons empty e)) c'
  have agr : ∀ (b : PSet.{u}) {x y : PSet.{u}}, x ≈ y →
      Agree χ (Env.cons x (Env.cons empty e)) (Env.cons y (Env.cons b e))
    | _, _, _, hxy, 0, _ => hxy
    | _, _, _, _, 1, h => Bool.noConfusion (hχ.symm.trans h)
    | _, _, _, _, n+2, _ => Equiv.refl _
  have hresp : ∀ x y, x ≈ y → P x → P y := fun x y hxy =>
    nn_map fun ⟨c', hc⟩ => ⟨c', (realizes_resp (agr empty hxy)).1 hc⟩
  let b := sep P (e k)
  refine realizes_ex.2 ⟨nn_intro ⟨⟨_, .refl _, rfl⟩⟩, fun ⟨r, hr, _⟩ => ?_⟩
  cases reduces_sepAx hr
  have hw : witness (.all (.iff (.mem 0 1) (.and (.mem 0 (k+2)) χ))) e .sepAx ≈ b := witness_sepAx k χ e
  have agrb : Agree (.all (.iff (.mem 0 1) (.and (.mem 0 (k+2)) χ)))
      (Env.cons (witness (.all (.iff (.mem 0 1) (.and (.mem 0 (k+2)) χ))) e .sepAx) e) (Env.cons b e)
    | 0, _ => hw
    | _+1, _ => Equiv.refl _
  refine (realizes_resp agrb).2 ?_
  show Realizes (.all (.iff (.mem 0 1) (.and (.mem 0 (k+2)) χ))) (Env.cons b e) .sepBody
  refine realizes_all.2 fun z => ⟨nn_intro ⟨⟨_, .single .sepBody, rfl⟩⟩, fun ⟨r, hr, hg⟩ => ?_⟩
  rcases reduces_sepBody hr with h | h
  · cases h; exact Bool.noConfusion hg
  cases h
  show Realizes (.iff (.mem 0 1) (.and (.mem 0 (k+2)) χ)) (Env.cons z (Env.cons b e)) .sepIff
  refine realizes_iff.2 ⟨nn_intro ⟨⟨_, .single .sepIff, rfl⟩⟩, fun ⟨r, hr, hp⟩ => ?_⟩
  rcases reduces_sepIff hr with h | h
  · cases h; exact Bool.noConfusion hp
  cases h
  show ImpSem (Realizes (.mem 0 1) (Env.cons z (Env.cons b e))) (Realizes (.and (.mem 0 (k+2)) χ) (Env.cons z (Env.cons b e))) .sepFwd ∧
    ImpSem (Realizes (.and (.mem 0 (k+2)) χ) (Env.cons z (Env.cons b e))) (Realizes (.mem 0 1) (Env.cons z (Env.cons b e))) .sepBwd
  have hb : ∀ {d : RCode}, Realizes (.mem 0 1) (Env.cons z (Env.cons b e)) d ↔ z ∈ b := fun {_} => realizes_mem
  constructor
  · intro d hd
    obtain ⟨hza, hP⟩ := (mem_sep hresp).1 (hb.1 hd)
    refine realizes_and.2 ⟨nn_map (fun ⟨c', hc⟩ => ⟨⟨.pair .tok c', Or.inr ⟨rfl, rfl, ⟨d, .refl _⟩,
      (realizes_resp (agr b (Equiv.refl z))).1 hc⟩⟩⟩) hP, fun ⟨r, hr⟩ => ?_⟩
    rcases hr with ⟨hred, hp⟩ | ⟨hp, hf, _, hc⟩
    · cases reduces_app_sepFwd hred; exact Bool.noConfusion hp
    · exact ⟨realizes_mem.2 hza, hc⟩
  · intro d hd
    have hd := realizes_and.1 hd
    refine hb.2 (Stable.of_nn hd.1 fun ⟨r⟩ => ?_)
    obtain ⟨h1, h2⟩ := hd.2 r
    exact (mem_sep hresp).2 ⟨realizes_mem.1 h1, nn_intro ⟨pairSnd r.1,
      (realizes_resp (agr b (Equiv.refl z))).2 h2⟩⟩

/-! ### Collection from a premise realizer -/

/-- The premise of Collection at `a = var k`: `∀x (x ∈ a → ∃y θ)`, `θ` under the binders `y, x`. -/
def collPrem (k : Nat) (θ : IFml) : IFml := .all (.imp (.mem 0 (k+1)) (.ex θ))

/-- The collecting set of a premise realizer `d`: for each literal element of `a`, each gen head of
`d`, and each existential head of its instance applied to the membership token, the witness read
back. A native `range` over a small index type; nothing is supplied. -/
def collect (k : Nat) (θ : IFml) (d : RCode) (e : Env.{u}) : PSet.{u} :=
  range (ι := Σ (_ : (e k).Idx) (g : Heads d isGen), Heads (.app (genBody g.1) .tok) isExHead)
    fun t => witness θ (Env.cons ((e k).Func t.1) e) t.2.2.1

section
variable {k : Nat} {θ : IFml} {d : RCode} {e : Env.{u}}

theorem agree_swap_x {x x' y : PSet.{u}} (h : x ≈ x') :
    Agree θ (Env.cons y (Env.cons x e)) (Env.cons y (Env.cons x' e))
  | 0, _ => Equiv.refl _
  | 1, _ => h
  | _+2, _ => Equiv.refl _

theorem agree_swap_y {x y y' : PSet.{u}} (h : y ≈ y') :
    Agree θ (Env.cons y (Env.cons x e)) (Env.cons y' (Env.cons x e))
  | 0, _ => h
  | _+1, _ => Equiv.refl _

/-- The instance of the premise at a literal element: the existential is realized. -/
theorem collPrem_inst (hd : Realizes (collPrem k θ) e d) (i : (e k).Idx) (g : Heads d isGen) :
    Realizes (.ex θ) (Env.cons ((e k).Func i) e) (.app (genBody g.1) .tok) :=
  (realizes_imp.1 ((realizes_all.1 hd _).2 g)) .tok (realizes_mem.2 (func_mem (e k) i))

/-- **Forward clause.** Every element of `a` has, negatively, a witness in the collector, with
the matrix realized there. -/
theorem collect_forward (hd : Realizes (collPrem k θ) e d) {x : PSet.{u}} (hx : x ∈ e k) :
    ¬¬∃ y, y ∈ collect k θ d e ∧ ¬¬∃ c', Realizes θ (Env.cons y (Env.cons x e)) c' := by
  refine nn_bind hx fun ⟨_i, hi⟩ => ?_
  refine nn_bind (realizes_all.1 hd ((e k).Func _i)).1 fun ⟨g⟩ => ?_
  refine nn_map (fun ⟨h⟩ => ?_) (realizes_ex.1 (collPrem_inst hd _i g)).1
  refine ⟨_, func_mem (collect k θ d e) ⟨_i, g, h⟩, nn_intro ⟨exBody h.1, ?_⟩⟩
  exact (realizes_resp (agree_swap_x hi.symm)).1 ((realizes_ex.1 (collPrem_inst hd _i g)).2 h)

/-- **Backward clause.** Every element of the collector is, negatively, a witness at some element
of `a`, with the matrix realized. -/
theorem collect_backward (hd : Realizes (collPrem k θ) e d) {y : PSet.{u}} (hy : y ∈ collect k θ d e) :
    ¬¬∃ x, x ∈ e k ∧ ¬¬∃ c', Realizes θ (Env.cons y (Env.cons x e)) c' := by
  refine nn_map (fun ⟨⟨_i, g, h⟩, hyw⟩ => ⟨(e k).Func _i, func_mem _ _i, nn_intro ⟨exBody h.1, ?_⟩⟩) hy
  exact (realizes_resp (agree_swap_y hyw.symm)).1 ((realizes_ex.1 (collPrem_inst hd _i g)).2 h)

/-- **Reuse of the collector**: it is a base for Separation, at the slot `0` of the extended
environment. -/
theorem collect_sep (χ : IFml) (hχ : IFml.mentions χ 1 = false) :
    Realizes (sepForm 0 χ) (Env.cons (collect k θ d e) e) .sepAx :=
  sep_realizes 0 χ hχ _

end

/-! ### Determinism, normal heads, and reduction expansion -/

theorem step_k {r : RCode} (h : Step .k r) : False := by cases h
theorem step_s {r : RCode} (h : Step .s r) : False := by cases h

/-- One-step reduction is deterministic. -/
theorem step_det {c r r' : RCode} (h : Step c r) (h' : Step c r') : r = r' := by
  induction h generalizing r' with
  | k =>
    cases h' with
    | k => rfl
    | appL h2 => cases h2 with | appL h3 => exact (step_k h3).elim
  | s =>
    cases h' with
    | s => rfl
    | appL h2 => cases h2 with | appL h3 => cases h3 with | appL h4 => exact (step_s h4).elim
  | fst =>
    cases h' with
    | fst => rfl
    | fstC h2 => exact (step_pair h2).elim
  | snd =>
    cases h' with
    | snd => rfl
    | sndC h2 => exact (step_pair h2).elim
  | appL h ih =>
    cases h' with
    | k => cases h with | appL h3 => exact (step_k h3).elim
    | s => cases h with | appL h3 => cases h3 with | appL h4 => exact (step_s h4).elim
    | appL h2 => rw [ih h2]
    | sepBwd => exact (step_sepBwd h).elim
  | fstC h ih =>
    cases h' with
    | fst => exact (step_pair h).elim
    | fstC h2 => rw [ih h2]
  | sndC h ih =>
    cases h' with
    | snd => exact (step_pair h).elim
    | sndC h2 => rw [ih h2]
  | sepBody => cases h'; rfl
  | sepIff => cases h'; rfl
  | sepBwd =>
    cases h' with
    | appL h2 => exact (step_sepBwd h2).elim
    | sepBwd => rfl

/-- Heads are normal. -/
theorem pair_normal {r r' : RCode} (hp : isPair r = true) (h : Step r r') : False := by
  cases r <;> first | exact Bool.noConfusion hp | exact step_pair h
theorem gen_normal {r r' : RCode} (hp : isGen r = true) (h : Step r r') : False := by
  cases r <;> first | exact Bool.noConfusion hp | exact step_gen h
theorem exHead_normal {r r' : RCode} (hp : isExHead r = true) (h : Step r r') : False := by
  cases r <;> (first
    | exact Bool.noConfusion hp
    | exact step_exIntro h
    | exact step_exIntroE h
    | exact step_sepAx h)
theorem app_sepFwd_normal {d r : RCode} (h : Step (.app .sepFwd d) r) : False := by
  cases h with | appL h' => exact step_sepFwd h'

/-- A normal reduct of `c` is a reduct of every reduct of `c`. -/
theorem reduces_normal_of_reduces {c c' h : RCode} (h1 : Reduces c c') (h2 : Reduces c h)
    (hn : ∀ r, Step h r → False) : Reduces c' h := by
  induction h1 with
  | refl => exact h2
  | step s _ ih =>
    cases h2 with
    | refl => exact (hn _ s).elim
    | step s' h2' => cases step_det s s'; exact ih h2'

def heads_of_reduces {c c' : RCode} (h1 : Reduces c c') {p : RCode → Bool}
    (hn : ∀ r r', p r = true → Step r r' → False) (r : Heads c p) : Heads c' p :=
  ⟨r.1, reduces_normal_of_reduces h1 r.2.1 (fun _ hs => hn _ _ r.2.2 hs), r.2.2⟩

def heads_of_reduces_back {c c' : RCode} (h1 : Reduces c c') {p : RCode → Bool} (r : Heads c' p) :
    Heads c p :=
  ⟨r.1, h1.trans r.2.1, r.2.2⟩

def andHeads_of_reduces {SB : RCode → Prop} {c c' : RCode} (h1 : Reduces c c') (r : AndHeads SB c) :
    AndHeads SB c' :=
  ⟨r.1, r.2.elim (fun ⟨hr, hp⟩ => Or.inl ⟨reduces_normal_of_reduces h1 hr (fun _ hs => pair_normal hp hs), hp⟩)
    fun ⟨hp, hf, ⟨d, hd⟩, hs⟩ =>
      Or.inr ⟨hp, hf, ⟨d, reduces_normal_of_reduces h1 hd (fun _ => app_sepFwd_normal)⟩, hs⟩⟩

def andHeads_of_reduces_back {SB : RCode → Prop} {c c' : RCode} (h1 : Reduces c c')
    (r : AndHeads SB c') : AndHeads SB c :=
  ⟨r.1, r.2.elim (fun ⟨hr, hp⟩ => Or.inl ⟨h1.trans hr, hp⟩)
    fun ⟨hp, hf, ⟨d, hd⟩, hs⟩ => Or.inr ⟨hp, hf, ⟨d, h1.trans hd⟩, hs⟩⟩

/-- **Reduction expansion**, in both directions, at every fuel: realizability is determined by the
normal heads, and by determinism a code and its reducts have the same normal heads. -/
theorem semN_of_reduces : ∀ (n : Nat) (φ : IFml) (e : Env.{u}) {c c' : RCode}, Reduces c c' →
    ((SemN n φ e c).2 ↔ (SemN n φ e c').2)
  | 0, _, _, _, _, _ => Iff.rfl
  | _+1, .mem _ _, _, _, _, _ => Iff.rfl
  | _+1, .eq _ _, _, _, _, _ => Iff.rfl
  | _+1, .fls, _, _, _, _ => Iff.rfl
  | n+1, .imp _ b, e, _, _, h =>
    ⟨fun H d hd => (semN_of_reduces n b e (Reduces.appL h)).1 (H d hd),
     fun H d hd => (semN_of_reduces n b e (Reduces.appL h)).2 (H d hd)⟩
  | _+1, .and _ _, _, _, _, h =>
    ⟨fun ⟨hr, H⟩ => ⟨nn_map (fun ⟨r⟩ => ⟨andHeads_of_reduces h r⟩) hr,
        fun r => H (andHeads_of_reduces_back h r)⟩,
     fun ⟨hr, H⟩ => ⟨nn_map (fun ⟨r⟩ => ⟨andHeads_of_reduces_back h r⟩) hr,
        fun r => H (andHeads_of_reduces h r)⟩⟩
  | _+1, .iff _ _, _, _, _, h =>
    ⟨fun ⟨hr, H⟩ => ⟨nn_map (fun ⟨r⟩ => ⟨heads_of_reduces h (fun _ _ => pair_normal) r⟩) hr,
        fun r => H (heads_of_reduces_back h r)⟩,
     fun ⟨hr, H⟩ => ⟨nn_map (fun ⟨r⟩ => ⟨heads_of_reduces_back h r⟩) hr,
        fun r => H (heads_of_reduces h (fun _ _ => pair_normal) r)⟩⟩
  | _+1, .all _, _, _, _, h =>
    ⟨fun H x => ⟨nn_map (fun ⟨r⟩ => ⟨heads_of_reduces h (fun _ _ => gen_normal) r⟩) (H x).1,
        fun r => (H x).2 (heads_of_reduces_back h r)⟩,
     fun H x => ⟨nn_map (fun ⟨r⟩ => ⟨heads_of_reduces_back h r⟩) (H x).1,
        fun r => (H x).2 (heads_of_reduces h (fun _ _ => gen_normal) r)⟩⟩
  | _+1, .ex _, _, _, _, h =>
    ⟨fun ⟨hr, H⟩ => ⟨nn_map (fun ⟨r⟩ => ⟨heads_of_reduces h (fun _ _ => exHead_normal) r⟩) hr,
        fun r => H (heads_of_reduces_back h r)⟩,
     fun ⟨hr, H⟩ => ⟨nn_map (fun ⟨r⟩ => ⟨heads_of_reduces_back h r⟩) hr,
        fun r => H (heads_of_reduces h (fun _ _ => exHead_normal) r)⟩⟩

theorem realizes_of_reduces {φ : IFml} {e : Env.{u}} {c c' : RCode} (h : Reduces c c') :
    Realizes φ e c ↔ Realizes φ e c' :=
  semN_of_reduces _ φ e h

/-! ### The combinators. Infrastructure only: these say nothing about the counterexamples in
`RelMachineTests.lean`, which concern existential introduction and the consumption of semantic
menus, not reduction. -/

theorem k_realizes (a b : IFml) (e : Env.{u}) : Realizes (.imp a (.imp b a)) e .k :=
  realizes_imp.2 fun _ hd => realizes_imp.2 fun _ _ =>
    (realizes_of_reduces (Reduces.single .k)).2 hd

theorem s_realizes (a b c : IFml) (e : Env.{u}) :
    Realizes (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c))) e .s :=
  realizes_imp.2 fun _ hf => realizes_imp.2 fun g hg => realizes_imp.2 fun x hx =>
    (realizes_of_reduces (Reduces.single .s)).2
      (realizes_imp.1 (realizes_imp.1 hf x hx) (.app g x) (realizes_imp.1 hg x hx))

/-- info: 'PSet.RelM.realizes_resp' does not depend on any axioms -/
#guard_msgs in #print axioms realizes_resp
/-- info: 'PSet.RelM.sep_realizes' does not depend on any axioms -/
#guard_msgs in #print axioms sep_realizes
/-- info: 'PSet.RelM.ex_elim' does not depend on any axioms -/
#guard_msgs in #print axioms ex_elim
/-- info: 'PSet.RelM.ex_intro_var' does not depend on any axioms -/
#guard_msgs in #print axioms ex_intro_var
/-- info: 'PSet.RelM.collect_forward' does not depend on any axioms -/
#guard_msgs in #print axioms collect_forward
/-- info: 'PSet.RelM.collect_backward' does not depend on any axioms -/
#guard_msgs in #print axioms collect_backward
/-- info: 'PSet.RelM.collect_sep' does not depend on any axioms -/
#guard_msgs in #print axioms collect_sep
/-- info: 'PSet.RelM.realizes_of_reduces' does not depend on any axioms -/
#guard_msgs in #print axioms realizes_of_reduces
/-- info: 'PSet.RelM.s_realizes' does not depend on any axioms -/
#guard_msgs in #print axioms s_realizes

end PSet.RelM
