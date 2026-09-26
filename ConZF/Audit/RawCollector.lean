-- Reviewer audit probe (2026-09-26), incorporated verbatim from the small-machine audit after conzf25;
-- its scope is stated in its own docstring. Empty axiom reports.
import ConZF.Ord

/-!
An audit of total raw witness reconstruction, independent of RelMachine.

Terms contain no PSet values. The only runtime rule is ordinary beta reduction.
An `emit q` head asks for the native value of descriptor q; `collect p` asks for
the range of values emitted by p. The diagonal program beta-reduces in one step
to a head asking for its own collector.

There is no total native readback satisfying this collector equation for all raw
programs. This does not rule out a typed/certified or partial machine.
-/
universe u
namespace PSet.RawCollectorAudit

inductive Code : Type
  | var (n : Nat)
  | lam (b : Code)
  | app (f a : Code)
  | emit (q : Code)
  | collect (p : Code)

def rename (ρ : Nat → Nat) : Code → Code
  | .var n => .var (ρ n)
  | .lam b => .lam (rename (fun n => match n with
      | 0 => 0
      | k+1 => ρ k + 1) b)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .emit q => .emit (rename ρ q)
  | .collect p => .collect (rename ρ p)

def subst (σ : Nat → Code) : Code → Code
  | .var n => σ n
  | .lam b => .lam (subst (fun n => match n with
      | 0 => .var 0
      | k+1 => rename Nat.succ (σ k)) b)
  | .app f a => .app (subst σ f) (subst σ a)
  | .emit q => .emit (subst σ q)
  | .collect p => .collect (subst σ p)

def plug (a : Code) : Nat → Code
  | 0 => a
  | n+1 => .var n

inductive Step : Code → Code → Prop
  | beta (b a : Code) : Step (.app (.lam b) a) (subst (plug a) b)

inductive Reduces : Code → Code → Prop
  | refl (c : Code) : Reduces c c
  | step {a b c} : Step a b → Reduces b c → Reduces a c

def delta : Code := .lam (.emit (.collect (.app (.var 0) (.var 0))))
def loop : Code := .app delta delta

theorem loop_head : Reduces loop (.emit (.collect loop)) :=
  .step (.beta _ _) (.refl _)

abbrev Outputs (p : Code) : Type := {q : Code // Reduces p (.emit q)}

def collected (read : Code → PSet.{u}) (p : Code) : PSet.{u} :=
  range (fun t : ULift.{u} (Outputs p) => read t.down.1)

theorem no_total_raw_readback (read : Code → PSet.{u})
    (collect_law : ∀ p, read (.collect p) ≈ collected read p) : False := by
  have hmem : read (.collect loop) ∈ collected read loop :=
    func_mem (collected read loop) ⟨⟨.collect loop, loop_head⟩⟩
  exact not_mem_self (read (.collect loop))
    ((mem_congr_right (collect_law loop).symm).1 hmem)

/-- Even making the collector law conditional on reaching an emit head does not suffice. -/
theorem head_readiness_is_not_enough (read : Code → PSet.{u})
    (collect_law : ∀ p, (¬¬Nonempty (Outputs p)) →
      read (.collect p) ≈ collected read p) : False := by
  have he := collect_law loop (nn_intro ⟨⟨.collect loop, loop_head⟩⟩)
  have hmem : read (.collect loop) ∈ collected read loop :=
    func_mem (collected read loop) ⟨⟨.collect loop, loop_head⟩⟩
  exact not_mem_self (read (.collect loop)) ((mem_congr_right he.symm).1 hmem)

private theorem emit_terminal {q r : Code} (h : Step (.emit q) r) : False := by cases h

private theorem reduces_emit {q r : Code} (h : Reduces (.emit q) r) : r = .emit q := by
  cases h with
  | refl => rfl
  | step hs _ => exact (emit_terminal hs).elim

theorem loop_output_unique {q : Code} (h : Reduces loop (.emit q)) : q = .collect loop := by
  cases h with
  | step hs ht =>
    cases hs
    exact Code.emit.inj (reduces_emit ht)

theorem collected_loop (read : Code → PSet.{u}) :
    collected read loop ≈ singleton (read (.collect loop)) := by
  apply ext
  intro x
  constructor
  · intro hx
    exact Stable.of_nn hx fun ⟨i, hi⟩ => mem_singleton.2
      (Eq.mp (congrArg (fun q => x ≈ read q) (loop_output_unique i.down.2)) hi)
  · intro hx
    exact nn_intro ⟨⟨⟨.collect loop, loop_head⟩⟩, mem_singleton.1 hx⟩

/-- A genuine fuelled implementation of the raw collector. Every recursive read uses lower fuel. -/
def rawReadN : Nat → Code → PSet.{u}
  | 0, _ => empty
  | n+1, .collect p => collected (rawReadN n) p
  | _+1, .var _ => empty
  | _+1, .lam _ => empty
  | _+1, .app _ _ => empty
  | _+1, .emit _ => empty

/-- Its diagonal outputs are exactly the successive singleton towers, up to bisimulation. -/
theorem rawReadN_loop (n : Nat) :
    rawReadN.{u} (n+1) (.collect loop) ≈ singleton (rawReadN n (.collect loop)) :=
  collected_loop _

theorem rawReadN_ne_next (n : Nat) :
    ¬ rawReadN.{u} n (.collect loop) ≈ rawReadN (n+1) (.collect loop) := by
  intro h
  have hm : rawReadN n (.collect loop) ∈ rawReadN (n+1) (.collect loop) :=
    (mem_congr_right (rawReadN_loop n)).2 (mem_singleton.2 (Equiv.refl _))
  exact not_mem_self (rawReadN n (.collect loop)) ((mem_congr_right h.symm).1 hm)

/-- Terminating Nat recursion does not give eventual fuel irrelevance, even for this one code. -/
theorem no_uniform_fuel_threshold :
    ¬∃ N, ∀ n m, N ≤ n → N ≤ m →
      rawReadN.{u} n (.collect loop) ≈ rawReadN m (.collect loop) := by
  intro ⟨N, hN⟩
  exact rawReadN_ne_next N (hN N (N+1) (Nat.le_refl _) (Nat.le_succ _))

/-! One elementary way to exclude this particular raw diagonal: a type discipline.
This proves rejection of the example only, not normalization or adequacy of a typed collector.
-/
inductive Ty : Type
  | obj
  | output
  | arrow (a b : Ty)

def Ty.size : Ty → Nat
  | .obj => 1
  | .output => 1
  | .arrow a b => a.size + b.size + 1

def extend (a : Ty) (Γ : Nat → Ty) : Nat → Ty
  | 0 => a
  | n+1 => Γ n

inductive Typed : (Nat → Ty) → Code → Ty → Prop
  | var (Γ n) : Typed Γ (.var n) (Γ n)
  | lam {Γ a b body} : Typed (extend a Γ) body b → Typed Γ (.lam body) (.arrow a b)
  | app {Γ a b f x} : Typed Γ f (.arrow a b) → Typed Γ x a → Typed Γ (.app f x) b
  | emit {Γ q} : Typed Γ q .obj → Typed Γ (.emit q) .output
  | collect {Γ p} : Typed Γ p .output → Typed Γ (.collect p) .obj

theorem type_not_own_arrow (a b : Ty) : ¬ a = .arrow a b := by
  intro he
  have hlt : a.size < (Ty.arrow a b).size := Nat.lt_succ_of_le (Nat.le_add_right _ _)
  exact (Nat.ne_of_lt hlt) (congrArg Ty.size he)

theorem typed_var {Γ n a} (h : Typed Γ (.var n) a) : Γ n = a := by
  cases h
  rfl

theorem self_application_untypable {Γ n a} : ¬ Typed Γ (.app (.var n) (.var n)) a := by
  intro h
  cases h with
  | app hf hx => exact type_not_own_arrow _ _ ((typed_var hx).symm.trans (typed_var hf))

theorem delta_untypable {Γ a} : ¬ Typed Γ delta a := by
  intro h
  cases h with
  | lam hb =>
    cases hb with
    | emit hc =>
      cases hc with
      | collect hp => exact self_application_untypable hp

theorem loop_untypable {Γ a} : ¬ Typed Γ loop a := by
  intro h
  cases h with
  | app hf _ => exact delta_untypable hf

#print axioms loop_head
#print axioms no_total_raw_readback
#print axioms head_readiness_is_not_enough
#print axioms loop_output_unique
#print axioms collected_loop
#print axioms rawReadN_loop
#print axioms rawReadN_ne_next
#print axioms no_uniform_fuel_threshold
#print axioms loop_untypable

end PSet.RawCollectorAudit
