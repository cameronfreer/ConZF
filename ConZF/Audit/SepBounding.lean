import ConZF.NegCore
/-!
Reviewer conjecture after con73, checked here: in the current `NegCore`, a realizer of Separation by
a **positive** existential `∃⁺y N(x, y)` with `N` negative already bounds the native witnesses, with
no Collection constructor. Given a realizer of `sepAx k (.ex N)` at `e`, negatively there is a set
`b` such that every `x ∈ e k` with a native witness `y` for `N` has a witness in `b`
(`sep_ex_bounds`), and if `N` is functional then every witness lies in `b`
(`sep_ex_bounds_functional`).

The proof runs exactly the reviewer's outline: open the Separation head to a native `S`; for a
native witness `y`, extend the environment by `y`, where canonical completeness and existential
introduction at the variable give a positive realizer, and the backward implication's Kripke clause
puts `x` in `S`; at the original environment the forward implication then supplies a pack head
whose object descriptor reconstructs a witness, validated by `neg_reflect`; the candidates are the
native range of all descriptor values at `[a.Func i, S, e]` over literal `i` and `q`, a small
carrier with no correctness filter and no selection.

Scope: this shows the positive-existential Separation request carries native collecting strength
in this semantics. It is neither a Separation producer nor an impossibility theorem, and the native
range need not have an `Obj` descriptor.
-/
universe u
namespace PSet.SepBoundingAudit
open NegCore

/-- The native range of every descriptor value at `[a.Func i, S, e]`, over literal `i` and `q`. -/
def candidates (a S : PSet.{u}) (e : Env.{u}) : PSet.{u} :=
  range fun p : a.Idx × ULift.{u} Obj => Obj.eval p.2.down (Env.cons (a.Func p.1) (Env.cons S e))

theorem sep_ex_bounds {N : IFml} (hN : Neg N) (k : Nat) (e : Env.{u}) {c : RCode}
    (hc : Realizes (sepAx k (.ex N)) (fun n => n) e c) :
    ¬¬∃ b : PSet.{u}, ∀ x, x ∈ e k → (¬¬∃ y, Truth N (Env.cons y (Env.cons x e))) →
      ¬¬∃ y, y ∈ b ∧ Truth N (Env.cons y (Env.cons x e)) := by
  refine Stable.of_nn hc.1 fun ⟨r⟩ => ?_
  have hall := hc.2 r
  refine nn_intro ⟨candidates (e k) (Obj.eval (packObj r.1) e) e, fun x hx hy => ?_⟩
  refine Stable.of_nn hx fun ⟨i, hxi⟩ => ?_
  -- work at the literal element `x' = (e k).Func i`
  have hy' : ¬¬∃ y, Truth N (Env.cons y (Env.cons ((e k).Func i) e)) :=
    nn_map (fun ⟨y, h⟩ => ⟨y, (truth_congr N (Env.cons_resp (Equiv.refl y)
      (Env.cons_resp hxi fun _ => Equiv.refl _))).1 h⟩) hy
  refine Stable.of_nn (hall ((e k).Func i)).1 fun ⟨r2⟩ => ?_
  have hb := (hall ((e k).Func i)).2 r2
  -- the element is in `S`, by the backward implication at the environment extended by a witness
  have hxS : Realizes (.mem 0 1) (Fml.up (Fml.up fun n => n))
      (Env.cons ((e k).Func i) (Env.cons (Obj.eval (packObj r.1) e) e)) .tok := by
    refine Stable.of_nn hy' fun ⟨y, hyN⟩ => ?_
    have hB := and_snd hb
    refine hB Nat.succ (Env.cons y (Env.cons ((e k).Func i) (Env.cons (Obj.eval (packObj r.1) e) e)))
      (along_succ _ _) (.pair .tok (.pack (.var 0) (canon N))) (and_intro ?_ ?_)
    · exact func_mem (e k) i
    · refine ex_intro (.var 0) ((realizes_rename N).2 ((neg_reflect hN _ _).2 ?_))
      exact (truth_congr N (fun n => by rcases n with _ | _ | n <;> exact Equiv.refl _)).1 hyN
  -- the forward implication at the original environment reconstructs a witness
  have hE : Realizes (.ex (IFml.rename (Fml.up sepR) N)) (Fml.up (Fml.up fun n => n))
      (Env.cons ((e k).Func i) (Env.cons (Obj.eval (packObj r.1) e) e)) _ :=
    and_snd (imp_elim (and_fst hb) hxS)
  refine Stable.of_nn hE.1 fun ⟨r'⟩ => ?_
  have hT := (neg_reflect hN _ _).1 _ ((realizes_rename N).1 (hE.2 r'))
  refine nn_intro ⟨Obj.eval (packObj r'.1) (Env.cons ((e k).Func i) (Env.cons (Obj.eval (packObj r.1) e) e)),
    func_mem (candidates (e k) (Obj.eval (packObj r.1) e) e) (i, ⟨packObj r'.1⟩), ?_⟩
  refine (truth_congr N (Env.cons_resp (Equiv.refl _) (Env.cons_resp hxi.symm fun _ => Equiv.refl _))).1 ?_
  exact (truth_congr N (fun n => by rcases n with _ | _ | n <;> exact Equiv.refl _)).1 hT

/-- For a functional matrix, every native witness lies in the candidate set. -/
theorem sep_ex_bounds_functional {N : IFml} (hN : Neg N) (k : Nat) (e : Env.{u}) {c : RCode}
    (hc : Realizes (sepAx k (.ex N)) (fun n => n) e c)
    (func : ∀ x y y', Truth N (Env.cons y (Env.cons x e)) → Truth N (Env.cons y' (Env.cons x e)) → y ≈ y') :
    ¬¬∃ b : PSet.{u}, ∀ x, x ∈ e k → ∀ y, Truth N (Env.cons y (Env.cons x e)) → y ∈ b :=
  nn_map (fun ⟨b, hb⟩ => ⟨b, fun x hx y hy => Stable.of_nn (hb x hx (nn_intro ⟨y, hy⟩))
    fun ⟨y', hy'b, hy'⟩ => (mem_congr_left (func x y' y hy' hy)).1 hy'b⟩) (sep_ex_bounds hN k e hc)

/-- info: 'PSet.SepBoundingAudit.sep_ex_bounds' does not depend on any axioms -/
#guard_msgs in #print axioms sep_ex_bounds
/-- info: 'PSet.SepBoundingAudit.sep_ex_bounds_functional' does not depend on any axioms -/
#guard_msgs in #print axioms sep_ex_bounds_functional

end PSet.SepBoundingAudit
