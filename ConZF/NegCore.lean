import ConZF.Derived
import ConZF.Pair
/-!
A restricted realizability core (conzf27, con69), separate from the prototype in `RelMachine.lean`.

* **Objects.** Witnesses are expressions `Obj` with a structural readback `Obj.eval`: variables,
  `∅`, pairs, unions, powersets, the negative-matrix separation `sepNeg a N` read as the native
  `sep` at the truth of `N`, and a local binding `letVar q o`. No constructor turns a code into an
  object, so the raw-collector diagonal is not expressible.
* **Codes.** A small syntax with unrestricted variable reads through `pack q c`; `uinstO q c`
  instantiating a universal at an object; `exElim d c` eliminating an existential into a code; and
  a closure `letObj q c` binding the value of `q` at variable `0` of `c`. Both β-rules produce a
  closure. Closures are never pushed by reduction: the head readers (`pairFst`, `genBody`,
  `packObj`, …) see through them, and an application to a closure pulls the argument inside
  (`letPull`). One-step reduction is deterministic.
* **Realizability** `Realizes φ σ e c` is structural on `φ`; the renaming `σ` maps the variables of
  `φ` to slots of the environment `e`, and the readback never calls it, so no fuel. Implication is
  read in the Kripke way: a realizer of `A → B` sends, at every environment `e'` reached by a
  renaming `ρ` with `e i ≈ e' (ρ i)`, every realizer of `A` to a realizer of `B` (the code renamed
  by `ρ`), so weakening is built in. Realizability is determined by the normal heads, hence
  invariant under reduction in both directions (`realizes_of_reduces`).
* **Checked.** Reduction compatibility with renaming (`step_rename`); monotonicity along
  environment renamings (`realizes_mono`); object substitution by closures (`letObj_realizes`);
  `I`, `K`, `S`, double negation introduction; projections through actual pair heads; unrestricted
  existential introduction at any object or variable; universal elimination at a variable and at an
  object (`all_elim_var`, `all_elim_obj`); code-producing existential elimination (`ex_elim`);
  negative soundness and canonical completeness (`neg_reflect`); negative Separation with a
  reconstructible witness (`neg_sep`).
* **Not here.** No Collection constructor, no claim of source adequacy, and the certification
  judgment is just `Realizes`: negative matrices are the only ones certified by truth
  (`neg_reflect`), so `neg_truth_iff_realizer` is the same scoped fact as the prototype's
  negative-fragment audit.
-/
universe u

namespace PSet.NegCore

/-! ### Formulas -/

inductive IFml : Type
  | mem (i j : Nat)
  | eq (i j : Nat)
  | fls
  | imp (a b : IFml)
  | and (a b : IFml)
  | all (a : IFml)
  | ex (a : IFml)

namespace IFml
def rename (ρ : Nat → Nat) : IFml → IFml
  | mem i j => mem (ρ i) (ρ j)
  | eq i j => eq (ρ i) (ρ j)
  | fls => fls
  | imp a b => imp (rename ρ a) (rename ρ b)
  | and a b => and (rename ρ a) (rename ρ b)
  | all a => all (rename (Fml.up ρ) a)
  | ex a => ex (rename (Fml.up ρ) a)
def lift (φ : IFml) : IFml := rename Nat.succ φ

theorem rename_congr {ρ σ : Nat → Nat} (h : ∀ n, ρ n = σ n) : ∀ φ, rename ρ φ = rename σ φ
  | .mem i j => show IFml.mem (ρ i) (ρ j) = IFml.mem (σ i) (σ j) from congr (congrArg IFml.mem (h i)) (h j)
  | .eq i j => show IFml.eq (ρ i) (ρ j) = IFml.eq (σ i) (σ j) from congr (congrArg IFml.eq (h i)) (h j)
  | .fls => rfl
  | .imp a b => show IFml.imp (rename ρ a) (rename ρ b) = IFml.imp (rename σ a) (rename σ b) from
      congr (congrArg IFml.imp (rename_congr h a)) (rename_congr h b)
  | .and a b => show IFml.and (rename ρ a) (rename ρ b) = IFml.and (rename σ a) (rename σ b) from
      congr (congrArg IFml.and (rename_congr h a)) (rename_congr h b)
  | .all a => show IFml.all (rename (Fml.up ρ) a) = IFml.all (rename (Fml.up σ) a) from
      congrArg IFml.all (rename_congr (Fml.up_congr h) a)
  | .ex a => show IFml.ex (rename (Fml.up ρ) a) = IFml.ex (rename (Fml.up σ) a) from
      congrArg IFml.ex (rename_congr (Fml.up_congr h) a)

theorem rename_rename (ρ σ : Nat → Nat) : ∀ φ, rename ρ (rename σ φ) = rename (fun n => ρ (σ n)) φ
  | .mem _ _ => rfl
  | .eq _ _ => rfl
  | .fls => rfl
  | .imp a b => show IFml.imp _ _ = IFml.imp _ _ from
      congr (congrArg IFml.imp (rename_rename ρ σ a)) (rename_rename ρ σ b)
  | .and a b => show IFml.and _ _ = IFml.and _ _ from
      congr (congrArg IFml.and (rename_rename ρ σ a)) (rename_rename ρ σ b)
  | .all a => show IFml.all _ = IFml.all _ from
      congrArg IFml.all ((rename_rename _ _ a).trans (rename_congr (Fml.up_up ρ σ) a))
  | .ex a => show IFml.ex _ = IFml.ex _ from
      congrArg IFml.ex ((rename_rename _ _ a).trans (rename_congr (Fml.up_up ρ σ) a))

theorem rename_id : ∀ φ, rename (fun n => n) φ = φ
  | .mem _ _ => rfl
  | .eq _ _ => rfl
  | .fls => rfl
  | .imp a b => show IFml.imp _ _ = IFml.imp a b from congr (congrArg IFml.imp (rename_id a)) (rename_id b)
  | .and a b => show IFml.and _ _ = IFml.and a b from congr (congrArg IFml.and (rename_id a)) (rename_id b)
  | .all a => show IFml.all _ = IFml.all a from congrArg IFml.all ((rename_congr Fml.up_id a).trans (rename_id a))
  | .ex a => show IFml.ex _ = IFml.ex a from congrArg IFml.ex ((rename_congr Fml.up_id a).trans (rename_id a))
end IFml

abbrev Env := Nat → PSet.{u}

/-- Environments agree along a renaming. -/
def Along (ρ : Nat → Nat) (e e' : Env.{u}) : Prop := ∀ i, e i ≈ e' (ρ i)

theorem along_refl (e : Env.{u}) : Along (fun n => n) e e := fun i => Equiv.refl (e i)
theorem along_succ (x : PSet.{u}) (e : Env.{u}) : Along Nat.succ e (Env.cons x e) := fun i => Equiv.refl (e i)
theorem along_comp {ρ ρ' : Nat → Nat} {e e' e'' : Env.{u}} (h : Along ρ e e') (h' : Along ρ' e' e'') :
    Along (fun n => ρ' (ρ n)) e e'' := fun i => (h i).trans (h' (ρ i))
theorem along_up {ρ : Nat → Nat} {e e' : Env.{u}} {x x' : PSet.{u}} (hx : x ≈ x') (h : Along ρ e e') :
    Along (Fml.up ρ) (Env.cons x e) (Env.cons x' e')
  | 0 => hx
  | n+1 => h n

/-- Native truth, negative existential. -/
def Truth : IFml → Env.{u} → Prop
  | .mem i j, e => e i ∈ e j
  | .eq i j, e => e i ≈ e j
  | .fls, _ => False
  | .imp a b, e => Truth a e → Truth b e
  | .and a b, e => Truth a e ∧ Truth b e
  | .all a, e => ∀ x : PSet.{u}, Truth a (Env.cons x e)
  | .ex a, e => ¬¬∃ x : PSet.{u}, Truth a (Env.cons x e)

theorem truth_stable : ∀ (φ : IFml) (e : Env.{u}), Stable (Truth φ e)
  | .mem _ _, _ => inferInstanceAs (Stable (_ ∈ _))
  | .eq _ _, _ => inferInstanceAs (Stable (_ ≈ _))
  | .fls, _ => inferInstanceAs (Stable False)
  | .imp _ b, e => have := truth_stable b e; inferInstanceAs (Stable (_ → _))
  | .and a b, e => have := truth_stable a e; have := truth_stable b e; inferInstanceAs (Stable (_ ∧ _))
  | .all a, e => have := fun x => truth_stable a (Env.cons x e); inferInstanceAs (Stable (∀ _, _))
  | .ex _, _ => inferInstanceAs (Stable (¬ _))

instance {φ : IFml} {e : Env.{u}} : Stable (Truth φ e) := truth_stable φ e

theorem truth_rename : ∀ (N : IFml) {ρ : Nat → Nat} {e e' : Env.{u}}, Along ρ e e' →
    (Truth (N.rename ρ) e' ↔ Truth N e)
  | .mem i j, _, _, _, h => (mem_congr_left (h i).symm).trans (mem_congr_right (h j).symm)
  | .eq i j, _, _, _, h => ⟨fun k => (h i).trans (k.trans (h j).symm), fun k => (h i).symm.trans (k.trans (h j))⟩
  | .fls, _, _, _, _ => Iff.rfl
  | .imp a b, _, _, _, h => ⟨fun k ha => (truth_rename b h).1 (k ((truth_rename a h).2 ha)),
      fun k ha => (truth_rename b h).2 (k ((truth_rename a h).1 ha))⟩
  | .and a b, _, _, _, h => ⟨fun k => ⟨(truth_rename a h).1 k.1, (truth_rename b h).1 k.2⟩,
      fun k => ⟨(truth_rename a h).2 k.1, (truth_rename b h).2 k.2⟩⟩
  | .all a, _, _, _, h => ⟨fun k x => (truth_rename a (along_up (Equiv.refl x) h)).1 (k x),
      fun k x => (truth_rename a (along_up (Equiv.refl x) h)).2 (k x)⟩
  | .ex a, _, _, _, h => nn_congr ⟨fun ⟨x, hx⟩ => ⟨x, (truth_rename a (along_up (Equiv.refl x) h)).1 hx⟩,
      fun ⟨x, hx⟩ => ⟨x, (truth_rename a (along_up (Equiv.refl x) h)).2 hx⟩⟩

theorem truth_congr (N : IFml) {e e' : Env.{u}} (h : ∀ i, e i ≈ e' i) : Truth N e ↔ Truth N e' := by
  have := truth_rename N (ρ := fun n => n) h
  rw [IFml.rename_id] at this
  exact this.symm

/-! ### Objects -/

inductive Obj : Type
  | var (j : Nat)
  | emp
  | upair (a b : Obj)
  | sUnion (a : Obj)
  | pow (a : Obj)
  /-- `{z ∈ a | N}`, `N` under the binder `z`. -/
  | sepNeg (a : Obj) (N : IFml)
  /-- `o` with the value of `q` bound at slot `0`. -/
  | letVar (q o : Obj)

namespace Obj
def eval : Obj → Env.{u} → PSet.{u}
  | var j, e => e j
  | emp, _ => empty
  | upair a b, e => PSet.upair (eval a e) (eval b e)
  | sUnion a, e => PSet.sUnion (eval a e)
  | pow a, e => powerset (eval a e)
  | sepNeg a N, e => sep (fun z => Truth N (Env.cons z e)) (eval a e)
  | letVar q o, e => eval o (Env.cons (eval q e) e)

def rename (ρ : Nat → Nat) : Obj → Obj
  | var j => var (ρ j)
  | emp => emp
  | upair a b => upair (rename ρ a) (rename ρ b)
  | sUnion a => sUnion (rename ρ a)
  | pow a => pow (rename ρ a)
  | sepNeg a N => sepNeg (rename ρ a) (IFml.rename (Fml.up ρ) N)
  | letVar q o => letVar (rename ρ q) (rename (Fml.up ρ) o)

def lift (q : Obj) : Obj := rename Nat.succ q

theorem rename_congr {ρ σ : Nat → Nat} (h : ∀ n, ρ n = σ n) : ∀ q, rename ρ q = rename σ q
  | var j => show Obj.var (ρ j) = Obj.var (σ j) from congrArg Obj.var (h j)
  | emp => rfl
  | upair a b => show Obj.upair _ _ = Obj.upair _ _ from
      congr (congrArg Obj.upair (rename_congr h a)) (rename_congr h b)
  | sUnion a => show Obj.sUnion _ = Obj.sUnion _ from congrArg Obj.sUnion (rename_congr h a)
  | pow a => show Obj.pow _ = Obj.pow _ from congrArg Obj.pow (rename_congr h a)
  | sepNeg a N => show Obj.sepNeg _ _ = Obj.sepNeg _ _ from
      congr (congrArg Obj.sepNeg (rename_congr h a)) (IFml.rename_congr (Fml.up_congr h) N)
  | letVar q o => show Obj.letVar _ _ = Obj.letVar _ _ from
      congr (congrArg Obj.letVar (rename_congr h q)) (rename_congr (Fml.up_congr h) o)

theorem rename_rename (ρ σ : Nat → Nat) : ∀ q, rename ρ (rename σ q) = rename (fun n => ρ (σ n)) q
  | var _ => rfl
  | emp => rfl
  | upair a b => show Obj.upair _ _ = Obj.upair _ _ from
      congr (congrArg Obj.upair (rename_rename ρ σ a)) (rename_rename ρ σ b)
  | sUnion a => show Obj.sUnion _ = Obj.sUnion _ from congrArg Obj.sUnion (rename_rename ρ σ a)
  | pow a => show Obj.pow _ = Obj.pow _ from congrArg Obj.pow (rename_rename ρ σ a)
  | sepNeg a N => show Obj.sepNeg _ _ = Obj.sepNeg _ _ from
      congr (congrArg Obj.sepNeg (rename_rename ρ σ a))
        ((IFml.rename_rename _ _ N).trans (IFml.rename_congr (Fml.up_up ρ σ) N))
  | letVar q o => show Obj.letVar _ _ = Obj.letVar _ _ from
      congr (congrArg Obj.letVar (rename_rename ρ σ q))
        ((rename_rename _ _ o).trans (rename_congr (Fml.up_up ρ σ) o))

theorem rename_id : ∀ q, rename (fun n => n) q = q
  | var _ => rfl
  | emp => rfl
  | upair a b => show Obj.upair _ _ = Obj.upair a b from congr (congrArg Obj.upair (rename_id a)) (rename_id b)
  | sUnion a => show Obj.sUnion _ = Obj.sUnion a from congrArg Obj.sUnion (rename_id a)
  | pow a => show Obj.pow _ = Obj.pow a from congrArg Obj.pow (rename_id a)
  | sepNeg a N => show Obj.sepNeg _ _ = Obj.sepNeg a N from
      congr (congrArg Obj.sepNeg (rename_id a)) ((IFml.rename_congr Fml.up_id N).trans (IFml.rename_id N))
  | letVar q o => show Obj.letVar _ _ = Obj.letVar q o from
      congr (congrArg Obj.letVar (rename_id q)) ((rename_congr Fml.up_id o).trans (rename_id o))

theorem lift_rename (ρ : Nat → Nat) (q : Obj) : rename (Fml.up ρ) (lift q) = lift (rename ρ q) := by
  unfold lift; rw [rename_rename, rename_rename]; exact rename_congr (fun _ => rfl) q
end Obj

theorem upair_congr {a a' b b' : PSet.{u}} (ha : a ≈ a') (hb : b ≈ b') : upair a b ≈ upair a' b' :=
  ext fun _ => mem_upair.trans <| (nn_congr ⟨fun h => h.elim (fun h => .inl (h.trans ha)) (fun h => .inr (h.trans hb)),
    fun h => h.elim (fun h => .inl (h.trans ha.symm)) (fun h => .inr (h.trans hb.symm))⟩).trans mem_upair.symm

theorem sUnion_congr {a a' : PSet.{u}} (ha : a ≈ a') : sUnion a ≈ sUnion a' :=
  ext fun _ => mem_sUnion.trans <| (nn_congr ⟨fun ⟨y, hy, hz⟩ => ⟨y, (mem_congr_right ha).1 hy, hz⟩,
    fun ⟨y, hy, hz⟩ => ⟨y, (mem_congr_right ha).2 hy, hz⟩⟩).trans mem_sUnion.symm

theorem powerset_congr {a a' : PSet.{u}} (ha : a ≈ a') : powerset a ≈ powerset a' :=
  ext fun z => mem_powerset.trans <| (⟨fun h w hw => (mem_congr_right ha).1 (h w hw),
    fun h w hw => (mem_congr_right ha).2 (h w hw)⟩ : (∀ w, w ∈ z → w ∈ a) ↔ (∀ w, w ∈ z → w ∈ a')).trans
    mem_powerset.symm

theorem truth_cons_resp (N : IFml) (e : Env.{u}) : ∀ x y, x ≈ y → Truth N (Env.cons x e) → Truth N (Env.cons y e) :=
  fun _ _ hxy => (truth_congr N (Env.cons_resp hxy fun i => Equiv.refl (e i))).1

theorem Obj.eval_rename : ∀ (q : Obj) {ρ : Nat → Nat} {e e' : Env.{u}}, Along ρ e e' →
    Obj.eval (q.rename ρ) e' ≈ Obj.eval q e
  | .var j, _, _, _, h => (h j).symm
  | .emp, _, _, _, _ => Equiv.refl _
  | .upair a b, _, _, _, h => upair_congr (eval_rename a h) (eval_rename b h)
  | .sUnion a, _, _, _, h => sUnion_congr (eval_rename a h)
  | .pow a, _, _, _, h => powerset_congr (eval_rename a h)
  | .sepNeg a N, _, e, e', h => ext fun z =>
      ((mem_sep (truth_cons_resp _ e')).trans ((and_congr (mem_congr_right (eval_rename a h))
        (truth_rename N (along_up (Equiv.refl z) h))))).trans (mem_sep (truth_cons_resp N e)).symm
  | .letVar q o, _, _, _, h => eval_rename o (along_up (eval_rename q h).symm h)

/-! ### Codes -/

inductive RCode : Type
  | tok
  | k
  | s
  | app (c d : RCode)
  | pair (c d : RCode)
  | fst (c : RCode)
  | snd (c : RCode)
  | gen (c : RCode)
  /-- universal instantiation at an object -/
  | uinstO (q : Obj) (c : RCode)
  /-- existential introduction with witness `q` and body `c` (under the witness binder) -/
  | pack (q : Obj) (c : RCode)
  /-- existential elimination: `d` realizes `∀ (A → B↑)`, `c` realizes `∃ A` -/
  | exElim (d c : RCode)
  /-- closure: `c` with the value of `q` bound at variable `0` -/
  | letObj (q : Obj) (c : RCode)

/-- The canonical code of a negative formula. -/
def canon : IFml → RCode
  | .mem _ _ => .tok
  | .eq _ _ => .tok
  | .fls => .tok
  | .imp _ b => .app .k (canon b)
  | .and a b => .pair (canon a) (canon b)
  | .all a => .gen (canon a)
  | .ex _ => .tok

/-- Swap the two innermost variables. -/
def swap : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n+2 => n+2

namespace RCode
def rename (ρ : Nat → Nat) : RCode → RCode
  | tok => tok
  | k => k
  | s => s
  | app c d => app (rename ρ c) (rename ρ d)
  | pair c d => pair (rename ρ c) (rename ρ d)
  | fst c => fst (rename ρ c)
  | snd c => snd (rename ρ c)
  | gen c => gen (rename (Fml.up ρ) c)
  | uinstO q c => uinstO (Obj.rename ρ q) (rename ρ c)
  | pack q c => pack (Obj.rename ρ q) (rename (Fml.up ρ) c)
  | exElim d c => exElim (rename ρ d) (rename ρ c)
  | letObj q c => letObj (Obj.rename ρ q) (rename (Fml.up ρ) c)

def lift (c : RCode) : RCode := rename Nat.succ c

theorem rename_congr {ρ σ : Nat → Nat} (h : ∀ n, ρ n = σ n) : ∀ c, rename ρ c = rename σ c
  | tok => rfl
  | k => rfl
  | s => rfl
  | app c d => show RCode.app _ _ = RCode.app _ _ from congr (congrArg RCode.app (rename_congr h c)) (rename_congr h d)
  | pair c d => show RCode.pair _ _ = RCode.pair _ _ from congr (congrArg RCode.pair (rename_congr h c)) (rename_congr h d)
  | fst c => show RCode.fst _ = RCode.fst _ from congrArg RCode.fst (rename_congr h c)
  | snd c => show RCode.snd _ = RCode.snd _ from congrArg RCode.snd (rename_congr h c)
  | gen c => show RCode.gen _ = RCode.gen _ from congrArg RCode.gen (rename_congr (Fml.up_congr h) c)
  | uinstO q c => show RCode.uinstO _ _ = RCode.uinstO _ _ from
      congr (congrArg RCode.uinstO (Obj.rename_congr h q)) (rename_congr h c)
  | pack q c => show RCode.pack _ _ = RCode.pack _ _ from
      congr (congrArg RCode.pack (Obj.rename_congr h q)) (rename_congr (Fml.up_congr h) c)
  | exElim d c => show RCode.exElim _ _ = RCode.exElim _ _ from
      congr (congrArg RCode.exElim (rename_congr h d)) (rename_congr h c)
  | letObj q c => show RCode.letObj _ _ = RCode.letObj _ _ from
      congr (congrArg RCode.letObj (Obj.rename_congr h q)) (rename_congr (Fml.up_congr h) c)

theorem rename_rename (ρ σ : Nat → Nat) : ∀ c, rename ρ (rename σ c) = rename (fun n => ρ (σ n)) c
  | tok => rfl
  | k => rfl
  | s => rfl
  | app c d => show RCode.app _ _ = RCode.app _ _ from
      congr (congrArg RCode.app (rename_rename ρ σ c)) (rename_rename ρ σ d)
  | pair c d => show RCode.pair _ _ = RCode.pair _ _ from
      congr (congrArg RCode.pair (rename_rename ρ σ c)) (rename_rename ρ σ d)
  | fst c => show RCode.fst _ = RCode.fst _ from congrArg RCode.fst (rename_rename ρ σ c)
  | snd c => show RCode.snd _ = RCode.snd _ from congrArg RCode.snd (rename_rename ρ σ c)
  | gen c => show RCode.gen _ = RCode.gen _ from
      congrArg RCode.gen ((rename_rename _ _ c).trans (rename_congr (Fml.up_up ρ σ) c))
  | uinstO q c => show RCode.uinstO _ _ = RCode.uinstO _ _ from
      congr (congrArg RCode.uinstO (Obj.rename_rename ρ σ q)) (rename_rename ρ σ c)
  | pack q c => show RCode.pack _ _ = RCode.pack _ _ from
      congr (congrArg RCode.pack (Obj.rename_rename ρ σ q))
        ((rename_rename _ _ c).trans (rename_congr (Fml.up_up ρ σ) c))
  | exElim d c => show RCode.exElim _ _ = RCode.exElim _ _ from
      congr (congrArg RCode.exElim (rename_rename ρ σ d)) (rename_rename ρ σ c)
  | letObj q c => show RCode.letObj _ _ = RCode.letObj _ _ from
      congr (congrArg RCode.letObj (Obj.rename_rename ρ σ q))
        ((rename_rename _ _ c).trans (rename_congr (Fml.up_up ρ σ) c))

theorem rename_id : ∀ c, rename (fun n => n) c = c
  | tok => rfl
  | k => rfl
  | s => rfl
  | app c d => show RCode.app _ _ = RCode.app c d from congr (congrArg RCode.app (rename_id c)) (rename_id d)
  | pair c d => show RCode.pair _ _ = RCode.pair c d from congr (congrArg RCode.pair (rename_id c)) (rename_id d)
  | fst c => show RCode.fst _ = RCode.fst c from congrArg RCode.fst (rename_id c)
  | snd c => show RCode.snd _ = RCode.snd c from congrArg RCode.snd (rename_id c)
  | gen c => show RCode.gen _ = RCode.gen c from congrArg RCode.gen ((rename_congr Fml.up_id c).trans (rename_id c))
  | uinstO q c => show RCode.uinstO _ _ = RCode.uinstO q c from
      congr (congrArg RCode.uinstO (Obj.rename_id q)) (rename_id c)
  | pack q c => show RCode.pack _ _ = RCode.pack q c from
      congr (congrArg RCode.pack (Obj.rename_id q)) ((rename_congr Fml.up_id c).trans (rename_id c))
  | exElim d c => show RCode.exElim _ _ = RCode.exElim d c from
      congr (congrArg RCode.exElim (rename_id d)) (rename_id c)
  | letObj q c => show RCode.letObj _ _ = RCode.letObj q c from
      congr (congrArg RCode.letObj (Obj.rename_id q)) ((rename_congr Fml.up_id c).trans (rename_id c))

theorem lift_rename (ρ : Nat → Nat) (c : RCode) : rename (Fml.up ρ) (lift c) = lift (rename ρ c) := by
  unfold lift; rw [rename_rename, rename_rename]; exact rename_congr (fun _ => rfl) c

theorem swap_rename (ρ : Nat → Nat) (c : RCode) :
    rename swap (rename (Fml.up (Fml.up ρ)) c) = rename (Fml.up (Fml.up ρ)) (rename swap c) := by
  rw [rename_rename, rename_rename]
  exact rename_congr (fun n => by rcases n with _ | _ | n <;> rfl) c
end RCode

theorem canon_rename (ρ : Nat → Nat) : ∀ N, RCode.rename ρ (canon N) = canon N
  | .mem _ _ => rfl
  | .eq _ _ => rfl
  | .fls => rfl
  | .imp _ b => show RCode.app .k _ = RCode.app .k _ from congrArg (RCode.app .k) (canon_rename ρ b)
  | .and a b => show RCode.pair _ _ = RCode.pair _ _ from
      congr (congrArg RCode.pair (canon_rename ρ a)) (canon_rename ρ b)
  | .all a => show RCode.gen _ = RCode.gen _ from congrArg RCode.gen (canon_rename _ a)
  | .ex _ => rfl

/-! ### Heads, seen through closures -/

def isPair : RCode → Bool
  | .pair _ _ => true
  | .letObj _ c => isPair c
  | .tok => false | .k => false | .s => false | .app _ _ => false | .fst _ => false | .snd _ => false
  | .gen _ => false | .uinstO _ _ => false | .pack _ _ => false | .exElim _ _ => false
def pairFst : RCode → RCode
  | .pair c _ => c
  | .letObj q c => .letObj q (pairFst c)
  | .tok => .tok | .k => .tok | .s => .tok | .app _ _ => .tok | .fst _ => .tok | .snd _ => .tok
  | .gen _ => .tok | .uinstO _ _ => .tok | .pack _ _ => .tok | .exElim _ _ => .tok
def pairSnd : RCode → RCode
  | .pair _ d => d
  | .letObj q c => .letObj q (pairSnd c)
  | .tok => .tok | .k => .tok | .s => .tok | .app _ _ => .tok | .fst _ => .tok | .snd _ => .tok
  | .gen _ => .tok | .uinstO _ _ => .tok | .pack _ _ => .tok | .exElim _ _ => .tok
def isGen : RCode → Bool
  | .gen _ => true
  | .letObj _ c => isGen c
  | .tok => false | .k => false | .s => false | .app _ _ => false | .pair _ _ => false | .fst _ => false
  | .snd _ => false | .uinstO _ _ => false | .pack _ _ => false | .exElim _ _ => false
/-- The body of a universal head, under its binder; a closure moves under the binder. -/
def genBody : RCode → RCode
  | .gen c => c
  | .letObj q c => .letObj q.lift ((genBody c).rename swap)
  | .tok => .tok | .k => .tok | .s => .tok | .app _ _ => .tok | .pair _ _ => .tok | .fst _ => .tok
  | .snd _ => .tok | .uinstO _ _ => .tok | .pack _ _ => .tok | .exElim _ _ => .tok
def isPack : RCode → Bool
  | .pack _ _ => true
  | .letObj _ c => isPack c
  | .tok => false | .k => false | .s => false | .app _ _ => false | .pair _ _ => false | .fst _ => false
  | .snd _ => false | .gen _ => false | .uinstO _ _ => false | .exElim _ _ => false
def packObj : RCode → Obj
  | .pack q _ => q
  | .letObj q c => .letVar q (packObj c)
  | .tok => .emp | .k => .emp | .s => .emp | .app _ _ => .emp | .pair _ _ => .emp | .fst _ => .emp
  | .snd _ => .emp | .gen _ => .emp | .uinstO _ _ => .emp | .exElim _ _ => .emp
def packBody : RCode → RCode
  | .pack _ c => c
  | .letObj q c => .letObj q.lift ((packBody c).rename swap)
  | .tok => .tok | .k => .tok | .s => .tok | .app _ _ => .tok | .pair _ _ => .tok | .fst _ => .tok
  | .snd _ => .tok | .gen _ => .tok | .uinstO _ _ => .tok | .exElim _ _ => .tok
def notLet : RCode → Bool
  | .letObj _ _ => false
  | .tok => true | .k => true | .s => true | .app _ _ => true | .pair _ _ => true | .fst _ => true
  | .snd _ => true | .gen _ => true | .uinstO _ _ => true | .pack _ _ => true | .exElim _ _ => true

theorem isPair_rename (ρ : Nat → Nat) (c : RCode) : isPair (c.rename ρ) = isPair c := by
  induction c generalizing ρ with
  | letObj q c ih => exact ih (Fml.up ρ)
  | _ => rfl
theorem isGen_rename (ρ : Nat → Nat) (c : RCode) : isGen (c.rename ρ) = isGen c := by
  induction c generalizing ρ with
  | letObj q c ih => exact ih (Fml.up ρ)
  | _ => rfl
theorem isPack_rename (ρ : Nat → Nat) (c : RCode) : isPack (c.rename ρ) = isPack c := by
  induction c generalizing ρ with
  | letObj q c ih => exact ih (Fml.up ρ)
  | _ => rfl
theorem notLet_rename (ρ : Nat → Nat) (c : RCode) : notLet (c.rename ρ) = notLet c := by
  cases c <;> rfl
theorem pairFst_rename (ρ : Nat → Nat) (c : RCode) : pairFst (c.rename ρ) = (pairFst c).rename ρ := by
  induction c generalizing ρ with
  | letObj q c ih => exact show RCode.letObj _ _ = RCode.letObj _ _ from congrArg _ (ih (Fml.up ρ))
  | _ => rfl
theorem pairSnd_rename (ρ : Nat → Nat) (c : RCode) : pairSnd (c.rename ρ) = (pairSnd c).rename ρ := by
  induction c generalizing ρ with
  | letObj q c ih => exact show RCode.letObj _ _ = RCode.letObj _ _ from congrArg _ (ih (Fml.up ρ))
  | _ => rfl
theorem genBody_rename (ρ : Nat → Nat) (c : RCode) : genBody (c.rename ρ) = (genBody c).rename (Fml.up ρ) := by
  induction c generalizing ρ with
  | letObj q c ih =>
    show RCode.letObj _ (RCode.rename swap (genBody (c.rename (Fml.up ρ)))) = RCode.letObj _ _
    rw [ih (Fml.up ρ), RCode.swap_rename, Obj.lift_rename]
  | _ => rfl
theorem packObj_rename (ρ : Nat → Nat) (c : RCode) : packObj (c.rename ρ) = (packObj c).rename ρ := by
  induction c generalizing ρ with
  | letObj q c ih => exact show Obj.letVar _ _ = Obj.letVar _ _ from congrArg _ (ih (Fml.up ρ))
  | _ => rfl
theorem packBody_rename (ρ : Nat → Nat) (c : RCode) : packBody (c.rename ρ) = (packBody c).rename (Fml.up ρ) := by
  induction c generalizing ρ with
  | letObj q c ih =>
    show RCode.letObj _ (RCode.rename swap (packBody (c.rename (Fml.up ρ)))) = RCode.letObj _ _
    rw [ih (Fml.up ρ), RCode.swap_rename, Obj.lift_rename]
  | _ => rfl

/-! ### Reduction -/

/-- One-step reduction. Applications reduce in function position unless the function is a closure,
which pulls the argument inside. The β-rules read heads through closures. -/
inductive Step : RCode → RCode → Prop
  | k {a b} : Step (.app (.app .k a) b) a
  | s {a b c} : Step (.app (.app (.app .s a) b) c) (.app (.app a c) (.app b c))
  | fst {c} : isPair c = true → Step (.fst c) (pairFst c)
  | snd {c} : isPair c = true → Step (.snd c) (pairSnd c)
  | appL {c c' d} : notLet c = true → Step c c' → Step (.app c d) (.app c' d)
  | fstC {c c'} : Step c c' → Step (.fst c) (.fst c')
  | sndC {c c'} : Step c c' → Step (.snd c) (.snd c')
  | uinstC {q c c'} : Step c c' → Step (.uinstO q c) (.uinstO q c')
  | uinstβ {q c} : isGen c = true → Step (.uinstO q c) (.letObj q (genBody c))
  | exElimL {d d' c} : Step d d' → Step (.exElim d c) (.exElim d' c)
  | exElimR {d c c'} : isGen d = true → Step c c' → Step (.exElim d c) (.exElim d c')
  | exElimβ {d c} : isGen d = true → isPack c = true →
      Step (.exElim d c) (.letObj (packObj c) (.app (genBody d) (packBody c)))
  | letC {q c c'} : Step c c' → Step (.letObj q c) (.letObj q c')
  | letPull {q c d} : Step (.app (.letObj q c) d) (.letObj q (.app c d.lift))

inductive Reduces : RCode → RCode → Prop
  | refl (c) : Reduces c c
  | step {a b c} : Step a b → Reduces b c → Reduces a c

theorem Reduces.trans {a b c : RCode} (h1 : Reduces a b) (h2 : Reduces b c) : Reduces a c := by
  induction h1 with
  | refl => exact h2
  | step s _ ih => exact .step s (ih h2)

theorem Reduces.single {a b : RCode} (h : Step a b) : Reduces a b := .step h (.refl _)

theorem Reduces.fstC {c c' : RCode} (h : Reduces c c') : Reduces (.fst c) (.fst c') := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.fstC s) ih
theorem Reduces.sndC {c c' : RCode} (h : Reduces c c') : Reduces (.snd c) (.snd c') := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.sndC s) ih
theorem Reduces.uinstC {q : Obj} {c c' : RCode} (h : Reduces c c') : Reduces (.uinstO q c) (.uinstO q c') := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.uinstC s) ih
theorem Reduces.exElimL {d d' c : RCode} (h : Reduces d d') : Reduces (.exElim d c) (.exElim d' c) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.exElimL s) ih
theorem Reduces.exElimR {d c c' : RCode} (hd : isGen d = true) (h : Reduces c c') :
    Reduces (.exElim d c) (.exElim d c') := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.exElimR hd s) ih
theorem Reduces.letC {q : Obj} {c c' : RCode} (h : Reduces c c') : Reduces (.letObj q c) (.letObj q c') := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.letC s) ih

theorem step_k {r : RCode} (h : Step .k r) : False := by cases h
theorem step_s {r : RCode} (h : Step .s r) : False := by cases h
theorem step_tok {r : RCode} (h : Step .tok r) : False := by cases h
theorem step_gen {x r : RCode} (h : Step (.gen x) r) : False := by cases h
theorem step_pair {x y r : RCode} (h : Step (.pair x y) r) : False := by cases h
theorem step_pack {q : Obj} {x r : RCode} (h : Step (.pack q x) r) : False := by cases h

theorem pair_normal {r r' : RCode} (hp : isPair r = true) (h : Step r r') : False := by
  induction r generalizing r' with
  | letObj q c ih => cases h with | letC h' => exact ih hp h'
  | pair a b => cases h
  | _ => exact Bool.noConfusion hp
theorem gen_normal {r r' : RCode} (hp : isGen r = true) (h : Step r r') : False := by
  induction r generalizing r' with
  | letObj q c ih => cases h with | letC h' => exact ih hp h'
  | gen a => cases h
  | _ => exact Bool.noConfusion hp
theorem pack_normal {r r' : RCode} (hp : isPack r = true) (h : Step r r') : False := by
  induction r generalizing r' with
  | letObj q c ih => cases h with | letC h' => exact ih hp h'
  | pack q a => cases h
  | _ => exact Bool.noConfusion hp

theorem step_det {c r r' : RCode} (h : Step c r) (h' : Step c r') : r = r' := by
  induction h generalizing r' with
  | k => cases h' with
    | k => rfl
    | appL _ h2 => cases h2 with | appL _ h3 => exact (step_k h3).elim
  | s => cases h' with
    | s => rfl
    | appL _ h2 => cases h2 with | appL _ h3 => cases h3 with | appL _ h4 => exact (step_s h4).elim
  | fst hp => cases h' with
    | fst _ => rfl
    | fstC h2 => exact (pair_normal hp h2).elim
  | snd hp => cases h' with
    | snd _ => rfl
    | sndC h2 => exact (pair_normal hp h2).elim
  | appL hn h ih => cases h' with
    | k => cases h with | appL _ h3 => exact (step_k h3).elim
    | s => cases h with | appL _ h3 => cases h3 with | appL _ h4 => exact (step_s h4).elim
    | appL _ h2 => rw [ih h2]
    | letPull => exact Bool.noConfusion hn
  | fstC h ih => cases h' with
    | fst hp => exact (pair_normal hp h).elim
    | fstC h2 => rw [ih h2]
  | sndC h ih => cases h' with
    | snd hp => exact (pair_normal hp h).elim
    | sndC h2 => rw [ih h2]
  | uinstC h ih => cases h' with
    | uinstC h2 => rw [ih h2]
    | uinstβ hg => exact (gen_normal hg h).elim
  | uinstβ hg => cases h' with
    | uinstC h2 => exact (gen_normal hg h2).elim
    | uinstβ _ => rfl
  | exElimL h ih => cases h' with
    | exElimL h2 => rw [ih h2]
    | exElimR hg _ => exact (gen_normal hg h).elim
    | exElimβ hg _ => exact (gen_normal hg h).elim
  | exElimR hg h ih => cases h' with
    | exElimL h2 => exact (gen_normal hg h2).elim
    | exElimR _ h2 => rw [ih h2]
    | exElimβ _ hp => exact (pack_normal hp h).elim
  | exElimβ hg hp => cases h' with
    | exElimL h2 => exact (gen_normal hg h2).elim
    | exElimR _ h2 => exact (pack_normal hp h2).elim
    | exElimβ _ _ => rfl
  | letC h ih => cases h' with
    | letC h2 => rw [ih h2]
  | letPull => cases h' with
    | appL hn _ => exact Bool.noConfusion hn
    | letPull => rfl

/-- A normal reduct of `c` is a reduct of every reduct of `c`. -/
theorem reduces_normal_of_reduces {c c' h : RCode} (h1 : Reduces c c') (h2 : Reduces c h)
    (hn : ∀ r, Step h r → False) : Reduces c' h := by
  induction h1 with
  | refl => exact h2
  | step s _ ih =>
    cases h2 with
    | refl => exact (hn _ s).elim
    | step s' h2' => cases step_det s s'; exact ih h2'

/-- A code has at most one normal reduct. -/
theorem normal_unique {c h h' : RCode} (h1 : Reduces c h) (hn : ∀ r, Step h r → False)
    (h2 : Reduces c h') (hn' : ∀ r, Step h' r → False) : h = h' := by
  cases reduces_normal_of_reduces h1 h2 hn' with
  | refl => rfl
  | step s _ => exact (hn _ s).elim

theorem reduces_of_normal {c r : RCode} (hn : ∀ r, Step c r → False) (h : Reduces c r) : r = c := by
  cases h with
  | refl => rfl
  | step s _ => exact (hn _ s).elim

/-- Along a reduction from `a`, the unique step from `a` is either not taken or taken first. -/
theorem reduces_step_split {a y w : RCode} (h : Reduces a w) (s : Step a y) : w = a ∨ Reduces y w := by
  cases h with
  | refl => exact .inl rfl
  | step s' h' => cases step_det s s'; exact .inr h'

/-- Two reducts of one code are comparable. -/
theorem reduces_diamond {a b c : RCode} (h1 : Reduces a b) (h2 : Reduces a c) : Reduces b c ∨ Reduces c b := by
  induction h1 generalizing c with
  | refl => exact .inl h2
  | step s h1' ih =>
    cases h2 with
    | refl => exact .inr (.step s h1')
    | step s2 h2' => cases step_det s s2; exact ih h2'

/-- One step of the function joins under application. -/
theorem app_join1 : ∀ {c c1 : RCode}, Step c c1 → ∀ d, ∃ w, Reduces (.app c d) w ∧ Reduces (.app c1 d) w
  | .letObj q _, _, .letC s', d =>
    let ⟨w, h1, h2⟩ := app_join1 s' d.lift
    ⟨.letObj q w, .step .letPull (Reduces.letC h1), .step .letPull (Reduces.letC h2)⟩
  | .app _ _, _, s, _ => ⟨_, .single (.appL rfl s), .refl _⟩
  | .fst _, _, s, _ => ⟨_, .single (.appL rfl s), .refl _⟩
  | .snd _, _, s, _ => ⟨_, .single (.appL rfl s), .refl _⟩
  | .uinstO _ _, _, s, _ => ⟨_, .single (.appL rfl s), .refl _⟩
  | .exElim _ _, _, s, _ => ⟨_, .single (.appL rfl s), .refl _⟩
  | .tok, _, s, _ => (step_tok s).elim
  | .k, _, s, _ => (step_k s).elim
  | .s, _, s, _ => (step_s s).elim
  | .pair _ _, _, s, _ => (step_pair s).elim
  | .gen _, _, s, _ => (step_gen s).elim
  | .pack _ _, _, s, _ => (step_pack s).elim

/-- Reduction of the function joins under application. -/
theorem app_join {c z : RCode} (h : Reduces c z) (d : RCode) :
    ∃ w, Reduces (.app c d) w ∧ Reduces (.app z d) w := by
  induction h with
  | refl c => exact ⟨.app c d, .refl _, .refl _⟩
  | step s _ ih =>
    obtain ⟨w, hw1, hw2⟩ := ih
    obtain ⟨w1, h1, h2⟩ := app_join1 s d
    rcases reduces_diamond h2 hw1 with h | h
    · exact ⟨w, h1.trans h, hw2⟩
    · exact ⟨w1, h1, hw2.trans h⟩

theorem step_rename (ρ : Nat → Nat) {c c' : RCode} (h : Step c c') : Step (c.rename ρ) (c'.rename ρ) := by
  induction h generalizing ρ with
  | k => exact .k
  | s => exact .s
  | fst hp => show Step (.fst _) _; rw [← pairFst_rename]; exact .fst ((isPair_rename _ _).trans hp)
  | snd hp => show Step (.snd _) _; rw [← pairSnd_rename]; exact .snd ((isPair_rename _ _).trans hp)
  | appL hn _ ih => exact .appL ((notLet_rename _ _).trans hn) (ih ρ)
  | fstC _ ih => exact .fstC (ih ρ)
  | sndC _ ih => exact .sndC (ih ρ)
  | uinstC _ ih => exact .uinstC (ih ρ)
  | uinstβ hg =>
    show Step (.uinstO _ _) (.letObj _ (RCode.rename (Fml.up ρ) (genBody _)))
    rw [← genBody_rename]; exact .uinstβ ((isGen_rename _ _).trans hg)
  | exElimL _ ih => exact .exElimL (ih ρ)
  | exElimR hg _ ih => exact .exElimR ((isGen_rename _ _).trans hg) (ih ρ)
  | exElimβ hg hp =>
    show Step (.exElim _ _) (.letObj (Obj.rename ρ (packObj _))
      (.app (RCode.rename (Fml.up ρ) (genBody _)) (RCode.rename (Fml.up ρ) (packBody _))))
    rw [← genBody_rename, ← packBody_rename, ← packObj_rename]
    exact .exElimβ ((isGen_rename _ _).trans hg) ((isPack_rename _ _).trans hp)
  | letC _ ih => exact .letC (ih (Fml.up ρ))
  | letPull =>
    show Step (.app (.letObj _ _) _) (.letObj _ (.app _ (RCode.rename (Fml.up ρ) (RCode.lift _))))
    rw [RCode.lift_rename]; exact .letPull

theorem reduces_rename (ρ : Nat → Nat) {c c' : RCode} (h : Reduces c c') : Reduces (c.rename ρ) (c'.rename ρ) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (step_rename ρ s) ih

/-! ### Realizability -/

def Ready (I : Type) : Prop := ¬¬Nonempty I
abbrev Heads (c : RCode) (p : RCode → Bool) : Type := {r : RCode // Reduces c r ∧ p r = true}

/-- Structural on the formula. `σ` maps formula variables to slots of `e`; the readback never calls
`Realizes`. Implication is Kripke: closed under renamings that agree with the environment. -/
def Realizes : IFml → (Nat → Nat) → Env.{u} → RCode → Prop
  | .mem i j, σ, e, _ => e (σ i) ∈ e (σ j)
  | .eq i j, σ, e, _ => e (σ i) ≈ e (σ j)
  | .fls, _, _, _ => False
  | .imp a b, σ, e, c => ∀ (ρ : Nat → Nat) (e' : Env.{u}), Along ρ e e' →
      ∀ d, Realizes a (fun n => ρ (σ n)) e' d → Realizes b (fun n => ρ (σ n)) e' (.app (c.rename ρ) d)
  | .and a b, σ, e, c => Ready (Heads c isPair) ∧
      ∀ r : Heads c isPair, Realizes a σ e (pairFst r.1) ∧ Realizes b σ e (pairSnd r.1)
  | .all a, σ, e, c => ∀ x : PSet.{u}, Ready (Heads c isGen) ∧
      ∀ r : Heads c isGen, Realizes a (Fml.up σ) (Env.cons x e) (genBody r.1)
  | .ex a, σ, e, c => Ready (Heads c isPack) ∧
      ∀ r : Heads c isPack, Realizes a (Fml.up σ) (Env.cons (Obj.eval (packObj r.1) e) e) (packBody r.1)

theorem realizes_stable : ∀ (φ : IFml) (σ : Nat → Nat) (e : Env.{u}) (c : RCode), Stable (Realizes φ σ e c)
  | .mem _ _, _, _, _ => inferInstanceAs (Stable (_ ∈ _))
  | .eq _ _, _, _, _ => inferInstanceAs (Stable (_ ≈ _))
  | .fls, _, _, _ => inferInstanceAs (Stable False)
  | .imp _ b, σ, _, c =>
    ⟨fun h ρ e' ha d hd => (realizes_stable b (fun n => ρ (σ n)) e' (.app (c.rename ρ) d)).dne
      fun hn => h fun h' => hn (h' ρ e' ha d hd)⟩
  | .and a b, σ, e, c =>
    have := fun r => realizes_stable a σ e (pairFst r); have := fun r => realizes_stable b σ e (pairSnd r)
    have : Stable (Ready (Heads c isPair)) := inferInstanceAs (Stable (¬ _))
    inferInstanceAs (Stable (_ ∧ ∀ _, _ ∧ _))
  | .all a, σ, e, c =>
    have := fun x r => realizes_stable a (Fml.up σ) (Env.cons x e) (genBody r)
    have : Stable (Ready (Heads c isGen)) := inferInstanceAs (Stable (¬ _))
    inferInstanceAs (Stable (∀ _, _ ∧ ∀ _, _))
  | .ex a, σ, e, c =>
    have := fun (r : RCode) => realizes_stable a (Fml.up σ) (Env.cons (Obj.eval (packObj r) e) e) (packBody r)
    have : Stable (Ready (Heads c isPack)) := inferInstanceAs (Stable (¬ _))
    inferInstanceAs (Stable (_ ∧ ∀ _, _))

instance {φ : IFml} {σ : Nat → Nat} {e : Env.{u}} {c : RCode} : Stable (Realizes φ σ e c) := realizes_stable φ σ e c

theorem realizes_imp {a b : IFml} {σ : Nat → Nat} {e : Env.{u}} {c : RCode} : Realizes (.imp a b) σ e c ↔
    ∀ (ρ : Nat → Nat) (e' : Env.{u}), Along ρ e e' →
      ∀ d, Realizes a (fun n => ρ (σ n)) e' d → Realizes b (fun n => ρ (σ n)) e' (.app (c.rename ρ) d) := Iff.rfl
theorem realizes_and {a b : IFml} {σ : Nat → Nat} {e : Env.{u}} {c : RCode} : Realizes (.and a b) σ e c ↔
    Ready (Heads c isPair) ∧ ∀ r : Heads c isPair, Realizes a σ e (pairFst r.1) ∧ Realizes b σ e (pairSnd r.1) := Iff.rfl
theorem realizes_all {a : IFml} {σ : Nat → Nat} {e : Env.{u}} {c : RCode} : Realizes (.all a) σ e c ↔
    ∀ x : PSet.{u}, Ready (Heads c isGen) ∧ ∀ r : Heads c isGen, Realizes a (Fml.up σ) (Env.cons x e) (genBody r.1) := Iff.rfl
theorem realizes_ex {a : IFml} {σ : Nat → Nat} {e : Env.{u}} {c : RCode} : Realizes (.ex a) σ e c ↔
    Ready (Heads c isPack) ∧
      ∀ r : Heads c isPack, Realizes a (Fml.up σ) (Env.cons (Obj.eval (packObj r.1) e) e) (packBody r.1) := Iff.rfl

/-! ### Invariance under reduction -/

theorem ready_of_reduces {c c' : RCode} {p : RCode → Bool} (hn : ∀ r r', p r = true → Step r r' → False)
    (h : Reduces c c') : Ready (Heads c p) → Ready (Heads c' p) :=
  nn_map fun ⟨r⟩ => ⟨⟨r.1, reduces_normal_of_reduces h r.2.1 (fun _ hs => hn _ _ r.2.2 hs), r.2.2⟩⟩
theorem ready_back {c c' : RCode} {p : RCode → Bool} (h : Reduces c c') : Ready (Heads c' p) → Ready (Heads c p) :=
  nn_map fun ⟨r⟩ => ⟨⟨r.1, h.trans r.2.1, r.2.2⟩⟩

/-- Realizability is a property of the normal heads, so it is invariant under reduction in both
directions. -/
theorem realizes_of_reduces : ∀ (φ : IFml) {σ : Nat → Nat} {e : Env.{u}} {c c' : RCode},
    Reduces c c' → (Realizes φ σ e c ↔ Realizes φ σ e c')
  | .mem _ _, _, _, _, _, _ => Iff.rfl
  | .eq _ _, _, _, _, _, _ => Iff.rfl
  | .fls, _, _, _, _, _ => Iff.rfl
  | .imp _ b, _, _, _, _, h =>
    ⟨fun hc ρ e' ha d hd =>
      let ⟨_, h1, h2⟩ := app_join (reduces_rename ρ h) d
      (realizes_of_reduces b h2).2 ((realizes_of_reduces b h1).1 (hc ρ e' ha d hd)),
     fun hc ρ e' ha d hd =>
      let ⟨_, h1, h2⟩ := app_join (reduces_rename ρ h) d
      (realizes_of_reduces b h1).2 ((realizes_of_reduces b h2).1 (hc ρ e' ha d hd))⟩
  | .and _ _, _, _, _, _, h =>
    ⟨fun ⟨hr, hc⟩ => ⟨ready_of_reduces (fun _ _ hp hs => pair_normal hp hs) h hr,
        fun r => hc ⟨r.1, h.trans r.2.1, r.2.2⟩⟩,
     fun ⟨hr, hc⟩ => ⟨ready_back h hr,
        fun r => hc ⟨r.1, reduces_normal_of_reduces h r.2.1 (fun _ => pair_normal r.2.2), r.2.2⟩⟩⟩
  | .all _, _, _, _, _, h =>
    ⟨fun hc x => ⟨ready_of_reduces (fun _ _ hp hs => gen_normal hp hs) h (hc x).1,
        fun r => (hc x).2 ⟨r.1, h.trans r.2.1, r.2.2⟩⟩,
     fun hc x => ⟨ready_back h (hc x).1,
        fun r => (hc x).2 ⟨r.1, reduces_normal_of_reduces h r.2.1 (fun _ => gen_normal r.2.2), r.2.2⟩⟩⟩
  | .ex _, _, _, _, _, h =>
    ⟨fun ⟨hr, hc⟩ => ⟨ready_of_reduces (fun _ _ hp hs => pack_normal hp hs) h hr,
        fun r => hc ⟨r.1, h.trans r.2.1, r.2.2⟩⟩,
     fun ⟨hr, hc⟩ => ⟨ready_back h hr,
        fun r => hc ⟨r.1, reduces_normal_of_reduces h r.2.1 (fun _ => pack_normal r.2.2), r.2.2⟩⟩⟩

/-! ### Renaming and substitution -/

theorem up_along {σ σ' : Nat → Nat} {e : Env.{u}} (h : ∀ n, e (σ n) ≈ e (σ' n)) (x : PSet.{u}) :
    ∀ n, Env.cons x e (Fml.up σ n) ≈ Env.cons x e (Fml.up σ' n)
  | 0 => Equiv.refl x
  | n+1 => h n

/-- Realizability depends on `σ` only through the values `e (σ n)`. -/
theorem realizes_env_congr : ∀ (φ : IFml) {σ σ' : Nat → Nat} {e : Env.{u}} {c : RCode},
    (∀ n, e (σ n) ≈ e (σ' n)) → Realizes φ σ e c → Realizes φ σ' e c
  | .mem i j, _, _, _, _, h, hc => (mem_congr_left (h i)).1 ((mem_congr_right (h j)).1 hc)
  | .eq i j, _, _, _, _, h, hc => (h i).symm.trans (hc.trans (h j))
  | .fls, _, _, _, _, _, hc => hc.elim
  | .imp a b, σ, σ', _, _, h, hc => fun ρ e' ha d hd =>
    realizes_env_congr b (fun n => (ha (σ n)).symm.trans ((h n).trans (ha (σ' n))))
      (hc ρ e' ha d (realizes_env_congr a (fun n => (ha (σ' n)).symm.trans ((h n).symm.trans (ha (σ n)))) hd))
  | .and a b, _, _, _, _, h, hc =>
    ⟨hc.1, fun r => ⟨realizes_env_congr a h (hc.2 r).1, realizes_env_congr b h (hc.2 r).2⟩⟩
  | .all a, _, _, _, _, h, hc => fun x => ⟨(hc x).1, fun r => realizes_env_congr a (up_along h x) ((hc x).2 r)⟩
  | .ex a, _, _, _, _, h, hc => ⟨hc.1, fun r => realizes_env_congr a (up_along h _) (hc.2 r)⟩

theorem realizes_congr_σ (φ : IFml) {σ σ' : Nat → Nat} {e : Env.{u}} {c : RCode} (h : ∀ n, σ n = σ' n) :
    Realizes φ σ e c → Realizes φ σ' e c :=
  realizes_env_congr φ fun n => by rw [h n]; exact Equiv.refl _

/-- Monotonicity: a realizer at `e` renames to a realizer at any `e'` reached along `ρ`. -/
theorem realizes_mono : ∀ (φ : IFml) {σ : Nat → Nat} {e e' : Env.{u}} {ρ : Nat → Nat} {c : RCode},
    Along ρ e e' → Realizes φ σ e c → Realizes φ (fun n => ρ (σ n)) e' (c.rename ρ)
  | .mem i j, σ, _, _, _, _, h, hc => (mem_congr_left (h (σ i))).1 ((mem_congr_right (h (σ j))).1 hc)
  | .eq i j, σ, _, _, _, _, h, hc => (h (σ i)).symm.trans (hc.trans (h (σ j)))
  | .fls, _, _, _, _, _, _, hc => hc.elim
  | .imp _ b, _, _, _, ρ, _, h, hc => fun ρ' e'' h' d hd => by
    have := hc (fun n => ρ' (ρ n)) e'' (along_comp h h') d hd
    rw [RCode.rename_rename]; exact this
  | .and a b, _, _, _, ρ, _, h, hc => by
    refine ⟨nn_map (fun ⟨r⟩ => ⟨⟨r.1.rename ρ, reduces_rename ρ r.2.1, (isPair_rename _ _).trans r.2.2⟩⟩) hc.1,
      fun r' => ?_⟩
    refine Stable.of_nn hc.1 fun ⟨r⟩ => ?_
    have hr : r'.1 = r.1.rename ρ := normal_unique r'.2.1 (fun _ => pair_normal r'.2.2) (reduces_rename ρ r.2.1)
      (fun _ => pair_normal ((isPair_rename _ _).trans r.2.2))
    rw [hr, pairFst_rename, pairSnd_rename]
    exact ⟨realizes_mono a h (hc.2 r).1, realizes_mono b h (hc.2 r).2⟩
  | .all a, σ, _, _, ρ, _, h, hc => fun x => by
    refine ⟨nn_map (fun ⟨r⟩ => ⟨⟨r.1.rename ρ, reduces_rename ρ r.2.1, (isGen_rename _ _).trans r.2.2⟩⟩) (hc x).1,
      fun r' => ?_⟩
    refine Stable.of_nn (hc x).1 fun ⟨r⟩ => ?_
    have hr : r'.1 = r.1.rename ρ := normal_unique r'.2.1 (fun _ => gen_normal r'.2.2) (reduces_rename ρ r.2.1)
      (fun _ => gen_normal ((isGen_rename _ _).trans r.2.2))
    rw [hr, genBody_rename]
    exact realizes_congr_σ a (Fml.up_up ρ σ) (realizes_mono a (along_up (Equiv.refl x) h) ((hc x).2 r))
  | .ex a, σ, _, _, ρ, _, h, hc => by
    refine ⟨nn_map (fun ⟨r⟩ => ⟨⟨r.1.rename ρ, reduces_rename ρ r.2.1, (isPack_rename _ _).trans r.2.2⟩⟩) hc.1,
      fun r' => ?_⟩
    refine Stable.of_nn hc.1 fun ⟨r⟩ => ?_
    have hr : r'.1 = r.1.rename ρ := normal_unique r'.2.1 (fun _ => pack_normal r'.2.2) (reduces_rename ρ r.2.1)
      (fun _ => pack_normal ((isPack_rename _ _).trans r.2.2))
    rw [hr, packObj_rename, packBody_rename]
    exact realizes_congr_σ a (Fml.up_up ρ σ)
      (realizes_mono a (along_up (Obj.eval_rename _ h).symm h) (hc.2 r))

theorem along_swap {x x' y : PSet.{u}} {e : Env.{u}} (hx : x ≈ x') :
    Along swap (Env.cons y (Env.cons x e)) (Env.cons x' (Env.cons y e))
  | 0 => Equiv.refl y
  | 1 => hx
  | n+2 => Equiv.refl (e n)

/-- Object substitution: a closure binding `q` at variable `0` realizes at `e` what its body realizes
at `e` extended by the value of `q`. -/
theorem letObj_realizes : ∀ (B : IFml) {σ : Nat → Nat} {e : Env.{u}} {q : Obj} {d : RCode},
    Realizes B (fun n => Nat.succ (σ n)) (Env.cons (Obj.eval q e) e) d → Realizes B σ e (.letObj q d)
  | .mem _ _, _, _, _, _, h => h
  | .eq _ _, _, _, _, _, h => h
  | .fls, _, _, _, _, h => h
  | .imp a b, σ, _, q, _, hd => fun ρ e' ha d' hd' => by
    have h1 := hd (Fml.up ρ) (Env.cons (Obj.eval (q.rename ρ) e') e') (along_up (Obj.eval_rename q ha).symm ha)
      d'.lift (realizes_mono a (along_succ _ _) hd')
    have h2 := letObj_realizes b (σ := fun n => ρ (σ n)) (q := q.rename ρ) h1
    exact (realizes_of_reduces b (.single .letPull)).2 h2
  | .and a b, _, _, q, _, hd => by
    refine ⟨nn_map (fun ⟨r⟩ => ⟨⟨.letObj q r.1, Reduces.letC r.2.1, r.2.2⟩⟩) hd.1, fun r' => ?_⟩
    refine Stable.of_nn hd.1 fun ⟨r⟩ => ?_
    have hr : r'.1 = .letObj q r.1 :=
      normal_unique r'.2.1 (fun _ => pair_normal r'.2.2) (Reduces.letC r.2.1) (fun _ => pair_normal r.2.2)
    rw [hr]
    exact ⟨letObj_realizes a (hd.2 r).1, letObj_realizes b (hd.2 r).2⟩
  | .all a, σ, e, q, _, hd => fun y => by
    refine ⟨nn_map (fun ⟨r⟩ => ⟨⟨.letObj q r.1, Reduces.letC r.2.1, r.2.2⟩⟩) (hd y).1, fun r' => ?_⟩
    refine Stable.of_nn (hd y).1 fun ⟨r⟩ => ?_
    have hr : r'.1 = .letObj q r.1 :=
      normal_unique r'.2.1 (fun _ => gen_normal r'.2.2) (Reduces.letC r.2.1) (fun _ => gen_normal r.2.2)
    rw [hr]
    refine letObj_realizes a ?_
    have := realizes_mono a (along_swap (e := e) (y := y) (Obj.eval_rename q (along_succ y e)).symm) ((hd y).2 r)
    exact realizes_congr_σ a (fun n => by rcases n with _ | n <;> rfl) this
  | .ex a, σ, e, q, _, hd => by
    refine ⟨nn_map (fun ⟨r⟩ => ⟨⟨.letObj q r.1, Reduces.letC r.2.1, r.2.2⟩⟩) hd.1, fun r' => ?_⟩
    refine Stable.of_nn hd.1 fun ⟨r⟩ => ?_
    have hr : r'.1 = .letObj q r.1 :=
      normal_unique r'.2.1 (fun _ => pack_normal r'.2.2) (Reduces.letC r.2.1) (fun _ => pack_normal r.2.2)
    rw [hr]
    refine letObj_realizes a ?_
    have := realizes_mono a (along_swap (e := e) (y := Obj.eval (packObj r.1) (Env.cons (Obj.eval q e) e))
      (Obj.eval_rename q (along_succ (Obj.eval (packObj r.1) (Env.cons (Obj.eval q e) e)) e)).symm) (hd.2 r)
    exact realizes_congr_σ a (fun n => by rcases n with _ | n <;> rfl) this

/-- Renaming the formula is composing `σ`. -/
theorem realizes_rename : ∀ (φ : IFml) {ρ σ : Nat → Nat} {e : Env.{u}} {c : RCode},
    Realizes (φ.rename ρ) σ e c ↔ Realizes φ (fun n => σ (ρ n)) e c
  | .mem _ _, _, _, _, _ => Iff.rfl
  | .eq _ _, _, _, _, _ => Iff.rfl
  | .fls, _, _, _, _ => Iff.rfl
  | .imp a b, ρ, σ, _, _ =>
    ⟨fun h ρ' e' ha d hd => (realizes_rename b (ρ := ρ) (σ := fun n => ρ' (σ n))).1
        (h ρ' e' ha d ((realizes_rename a (ρ := ρ) (σ := fun n => ρ' (σ n))).2 hd)),
     fun h ρ' e' ha d hd => (realizes_rename b (ρ := ρ) (σ := fun n => ρ' (σ n))).2
        (h ρ' e' ha d ((realizes_rename a (ρ := ρ) (σ := fun n => ρ' (σ n))).1 hd))⟩
  | .and a b, _, _, _, _ =>
    ⟨fun ⟨h1, h2⟩ => ⟨h1, fun r => ⟨(realizes_rename a).1 (h2 r).1, (realizes_rename b).1 (h2 r).2⟩⟩,
     fun ⟨h1, h2⟩ => ⟨h1, fun r => ⟨(realizes_rename a).2 (h2 r).1, (realizes_rename b).2 (h2 r).2⟩⟩⟩
  | .all a, ρ, σ, _, _ =>
    ⟨fun h x => ⟨(h x).1, fun r => realizes_congr_σ a (Fml.up_up σ ρ) ((realizes_rename a).1 ((h x).2 r))⟩,
     fun h x => ⟨(h x).1, fun r =>
        (realizes_rename a).2 (realizes_congr_σ a (fun n => (Fml.up_up σ ρ n).symm) ((h x).2 r))⟩⟩
  | .ex a, ρ, σ, _, _ =>
    ⟨fun ⟨h1, h2⟩ => ⟨h1, fun r => realizes_congr_σ a (Fml.up_up σ ρ) ((realizes_rename a).1 (h2 r))⟩,
     fun ⟨h1, h2⟩ => ⟨h1, fun r =>
        (realizes_rename a).2 (realizes_congr_σ a (fun n => (Fml.up_up σ ρ n).symm) (h2 r))⟩⟩

/-! ### The rules -/

/-- Certification is preserved by application. -/
theorem imp_elim {a b : IFml} {σ : Nat → Nat} {e : Env.{u}} {c d : RCode}
    (hc : Realizes (.imp a b) σ e c) (hd : Realizes a σ e d) : Realizes b σ e (.app c d) := by
  have := hc (fun n => n) e (along_refl e) d hd
  rw [RCode.rename_id] at this
  exact this

theorem and_fst {a b : IFml} {σ : Nat → Nat} {e : Env.{u}} {c : RCode} (h : Realizes (.and a b) σ e c) :
    Realizes a σ e (.fst c) :=
  Stable.of_nn h.1 fun ⟨r⟩ =>
    (realizes_of_reduces a ((Reduces.fstC r.2.1).trans (.single (.fst r.2.2)))).2 (h.2 r).1
theorem and_snd {a b : IFml} {σ : Nat → Nat} {e : Env.{u}} {c : RCode} (h : Realizes (.and a b) σ e c) :
    Realizes b σ e (.snd c) :=
  Stable.of_nn h.1 fun ⟨r⟩ =>
    (realizes_of_reduces b ((Reduces.sndC r.2.1).trans (.single (.snd r.2.2)))).2 (h.2 r).2
theorem and_intro {a b : IFml} {σ : Nat → Nat} {e : Env.{u}} {c d : RCode}
    (hc : Realizes a σ e c) (hd : Realizes b σ e d) : Realizes (.and a b) σ e (.pair c d) :=
  ⟨nn_intro ⟨⟨_, .refl _, rfl⟩⟩, fun r => by
    have hr : r.1 = .pair c d := reduces_of_normal (fun _ h => step_pair h) r.2.1
    rw [hr]; exact ⟨hc, hd⟩⟩

/-- Unrestricted existential introduction at an object. -/
theorem ex_intro {a : IFml} {σ : Nat → Nat} {e : Env.{u}} (q : Obj) {b : RCode}
    (hb : Realizes a (Fml.up σ) (Env.cons (Obj.eval q e) e) b) : Realizes (.ex a) σ e (.pack q b) :=
  ⟨nn_intro ⟨⟨_, .refl _, rfl⟩⟩, fun r => by
    have hr : r.1 = .pack q b := reduces_of_normal (fun _ h => step_pack h) r.2.1
    rw [hr]; exact hb⟩

/-- `push m σ` sends variable `0` to slot `m` and shifts the rest along `σ`. -/
def push (m : Nat) (σ : Nat → Nat) : Nat → Nat
  | 0 => m
  | n+1 => σ n

/-- Existential introduction at the variable `m` of the environment. -/
theorem ex_intro_var {a : IFml} {σ : Nat → Nat} {e : Env.{u}} (m : Nat) {b : RCode}
    (hb : Realizes a (push m σ) e b) : Realizes (.ex a) σ e (.pack (.var m) b.lift) :=
  ex_intro (.var m) (realizes_env_congr a (fun n => by rcases n with _ | n <;> exact Equiv.refl _)
    (realizes_mono a (along_succ (e m) e) hb))

/-- Universal elimination at the variable `m` of the environment. -/
theorem all_elim_var {a : IFml} {σ : Nat → Nat} {e : Env.{u}} {c : RCode} (m : Nat)
    (hc : Realizes (.all a) σ e c) : Realizes a (push m σ) e (.uinstO (.var m) c) :=
  Stable.of_nn (hc (e m)).1 fun ⟨r⟩ =>
    (realizes_of_reduces a ((Reduces.uinstC r.2.1).trans (.single (.uinstβ r.2.2)))).2
      (letObj_realizes a (realizes_env_congr a (fun n => by rcases n with _ | n <;> exact Equiv.refl _)
        ((hc (e m)).2 r)))

/-- Universal elimination as syntactic instantiation `inst j`. -/
theorem all_elim_inst {a : IFml} {σ : Nat → Nat} {e : Env.{u}} {c : RCode} (j : Nat)
    (hc : Realizes (.all a) σ e c) : Realizes (a.rename (Fml.inst j)) σ e (.uinstO (.var (σ j)) c) :=
  (realizes_rename a).2 (realizes_congr_σ a (fun n => by rcases n with _ | n <;> rfl) (all_elim_var (σ j) hc))

/-- Universal elimination at an object `q`, stated in the environment extended by its value. -/
theorem all_elim_obj {a : IFml} {σ : Nat → Nat} {e : Env.{u}} {c : RCode} (q : Obj)
    (hc : Realizes (.all a) σ e c) :
    Realizes a (Fml.up σ) (Env.cons (Obj.eval q e) e) (.uinstO q.lift c.lift) := by
  have hc' := realizes_mono (.all a) (along_succ (Obj.eval q e) e) hc
  refine Stable.of_nn (hc' (Obj.eval q e)).1 fun ⟨r⟩ => ?_
  refine (realizes_of_reduces a ((Reduces.uinstC r.2.1).trans (.single (.uinstβ r.2.2)))).2 ?_
  refine letObj_realizes a ?_
  have hx := Obj.eval_rename q (along_succ (Obj.eval q e) e)
  exact realizes_env_congr a (fun n => by rcases n with _ | n; exact hx; exact Equiv.refl _)
    ((hc' (Obj.eval q.lift (Env.cons (Obj.eval q e) e))).2 r)

/-- Code-producing existential elimination: the witness variable is absent from `B`. -/
theorem ex_elim {A B : IFml} {σ : Nat → Nat} {e : Env.{u}} {d c : RCode}
    (hd : Realizes (.all (.imp A (IFml.lift B))) σ e d) (hc : Realizes (.ex A) σ e c) :
    Realizes B σ e (.exElim d c) :=
  Stable.of_nn (hd (e 0)).1 fun ⟨r⟩ => Stable.of_nn hc.1 fun ⟨r'⟩ =>
    have h3 := imp_elim ((hd (Obj.eval (packObj r'.1) e)).2 r) (hc.2 r')
    have h4 : Realizes B (fun n => Nat.succ (σ n)) (Env.cons (Obj.eval (packObj r'.1) e) e)
      (.app (genBody r.1) (packBody r'.1)) := (realizes_rename B (ρ := Nat.succ) (σ := Fml.up σ)).1 h3
    (realizes_of_reduces B ((Reduces.exElimL r.2.1).trans
      ((Reduces.exElimR r.2.2 r'.2.1).trans (.single (.exElimβ r.2.2 r'.2.2))))).2 (letObj_realizes B h4)

/-! ### Combinators -/

theorem k_realizes (a b : IFml) (σ : Nat → Nat) (e : Env.{u}) : Realizes (.imp a (.imp b a)) σ e .k :=
  fun _ _ _ _ hx _ _ h2 _ _ => (realizes_of_reduces a (.single .k)).2 (realizes_mono a h2 hx)

theorem s_realizes (a b c : IFml) (σ : Nat → Nat) (e : Env.{u}) :
    Realizes (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c))) σ e .s :=
  fun _ _ _ x hx ρ2 _ h2 y hy ρ3 e3 h3 z hz => by
    show Realizes c _ e3 (.app (.app (.app .s (RCode.rename ρ3 (RCode.rename ρ2 x))) (RCode.rename ρ3 y)) z)
    refine (realizes_of_reduces c (.single .s)).2 ?_
    have hxz := hx (fun n => ρ3 (ρ2 n)) e3 (along_comp h2 h3) z hz
    have hyz := hy ρ3 e3 h3 z hz
    have := hxz (fun n => n) e3 (along_refl e3) _ hyz
    rw [RCode.rename_id] at this
    rw [RCode.rename_rename]
    exact this

def I : RCode := .app (.app .s .k) .k
theorem reduces_I (x : RCode) : Reduces (.app I x) x := .step .s (.step .k (.refl _))
theorem I_realizes (a : IFml) (σ : Nat → Nat) (e : Env.{u}) : Realizes (.imp a a) σ e I :=
  fun _ _ _ d hd => (realizes_of_reduces a (reduces_I d)).2 hd

/-- `NN x f = f x`. -/
def NN : RCode := .app (.app .s (.app .k (.app .s I))) (.app (.app .s (.app .k .k)) I)
def Y (x f : RCode) : RCode := .app (.app (.app (.app .s (.app .k .k)) I) x) f
theorem reduces_NN (x f : RCode) : Reduces (.app (.app NN x) f) (.app f (Y x f)) :=
  .step (.appL rfl .s) (.step (.appL rfl (.appL rfl .k)) (.step .s
    (.step (.appL rfl .s) (.step (.appL rfl .k) (.refl _)))))
theorem reduces_Y (x f : RCode) : Reduces (Y x f) x :=
  .step (.appL rfl .s) (.step (.appL rfl (.appL rfl .k)) (.step .k (reduces_I x)))

/-- Double negation introduction. -/
theorem nn_realizes (a : IFml) (σ : Nat → Nat) (e : Env.{u}) :
    Realizes (.imp a (.imp (.imp a .fls) .fls)) σ e NN :=
  fun _ _ _ x hx ρ2 e2 h2 f hf => by
    show Realizes .fls _ e2 (.app (.app NN (RCode.rename ρ2 x)) f)
    refine (realizes_of_reduces .fls (reduces_NN _ _)).2 ?_
    have hy : Realizes a _ e2 (Y (RCode.rename ρ2 x) f) :=
      (realizes_of_reduces a (reduces_Y _ _)).2 (realizes_mono a h2 hx)
    exact hf (fun n => n) e2 (along_refl e2) _ hy

/-! ### The negative fragment -/

inductive Neg : IFml → Prop
  | mem (i j : Nat) : Neg (.mem i j)
  | eq (i j : Nat) : Neg (.eq i j)
  | fls : Neg .fls
  | imp {a b : IFml} : Neg a → Neg b → Neg (.imp a b)
  | and {a b : IFml} : Neg a → Neg b → Neg (.and a b)
  | all {a : IFml} : Neg a → Neg (.all a)

theorem Neg.rename {N : IFml} (h : Neg N) : ∀ ρ, Neg (N.rename ρ) := by
  induction h with
  | mem i j => exact fun ρ => .mem _ _
  | eq i j => exact fun ρ => .eq _ _
  | fls => exact fun _ => .fls
  | imp _ _ iha ihb => exact fun ρ => .imp (iha ρ) (ihb ρ)
  | and _ _ iha ihb => exact fun ρ => .and (iha ρ) (ihb ρ)
  | all _ ih => exact fun ρ => .all (ih _)

theorem cons_up_env (σ : Nat → Nat) (e : Env.{u}) (x : PSet.{u}) :
    ∀ n, Env.cons x e (Fml.up σ n) ≈ Env.cons x (fun n => e (σ n)) n
  | 0 => Equiv.refl x
  | n+1 => Equiv.refl (e (σ n))

/-- Negative soundness and canonical completeness: on the negative fragment every realizer implies
truth, and truth validates the canonical code. -/
theorem neg_reflect {N : IFml} (hN : Neg N) : ∀ (σ : Nat → Nat) (e : Env.{u}),
    (∀ c, Realizes N σ e c → Truth N (fun n => e (σ n))) ∧
    (Truth N (fun n => e (σ n)) → Realizes N σ e (canon N)) := by
  induction hN with
  | mem i j => exact fun _ _ => ⟨fun _ h => h, fun h => h⟩
  | eq i j => exact fun _ _ => ⟨fun _ h => h, fun h => h⟩
  | fls => exact fun _ _ => ⟨fun _ h => h, fun h => h⟩
  | imp _ _ iha ihb =>
    intro σ e
    refine ⟨fun c hc ht => (ihb σ e).1 _ (imp_elim hc ((iha σ e).2 ht)), fun ht ρ e' hρ d hd => ?_⟩
    have h1 := (iha _ e').1 d hd
    have h2 := ht ((truth_congr _ (fun n => (hρ (σ n)).symm)).1 h1)
    have h3 := (ihb _ e').2 ((truth_congr _ (fun n => hρ (σ n))).1 h2)
    show Realizes _ _ e' (.app (.app .k (RCode.rename ρ (canon _))) d)
    rw [canon_rename]
    exact (realizes_of_reduces _ (.single .k)).2 h3
  | and _ _ iha ihb =>
    intro σ e
    refine ⟨fun c hc => Stable.of_nn hc.1 fun ⟨r⟩ => ⟨(iha σ e).1 _ (hc.2 r).1, (ihb σ e).1 _ (hc.2 r).2⟩,
      fun ht => ⟨nn_intro ⟨⟨_, .refl _, rfl⟩⟩, fun r => ?_⟩⟩
    have hr : r.1 = .pair (canon _) (canon _) := reduces_of_normal (fun _ h => step_pair h) r.2.1
    rw [hr]; exact ⟨(iha σ e).2 ht.1, (ihb σ e).2 ht.2⟩
  | all _ ih =>
    intro σ e
    refine ⟨fun c hc x => ?_, fun ht x => ⟨nn_intro ⟨⟨_, .refl _, rfl⟩⟩, fun r => ?_⟩⟩
    · exact Stable.of_nn (hc x).1 fun ⟨r⟩ =>
        (truth_congr _ (cons_up_env σ e x)).1 ((ih (Fml.up σ) (Env.cons x e)).1 _ ((hc x).2 r))
    · have hr : r.1 = .gen (canon _) := reduces_of_normal (fun _ h => step_gen h) r.2.1
      rw [hr]; exact (ih _ _).2 ((truth_congr _ (cons_up_env σ e x)).2 (ht x))

/-- On the negative fragment, negative existence of a realizer is native truth. Scoped: it says
nothing about formulas with a positive existential. -/
theorem neg_truth_iff_realizer {N : IFml} (hN : Neg N) (σ : Nat → Nat) (e : Env.{u}) :
    Truth N (fun n => e (σ n)) ↔ ∃ c, Realizes N σ e c :=
  ⟨fun h => ⟨_, (neg_reflect hN σ e).2 h⟩, fun ⟨_, hc⟩ => (neg_reflect hN σ e).1 _ hc⟩

/-! ### Negative Separation -/

/-- Reindex a matrix over `(z, ambient)` to `(z, S, ambient)`. -/
def sepR : Nat → Nat
  | 0 => 0
  | n+1 => n+2

/-- `∃ S ∀ z ((z ∈ S → z ∈ a ∧ N) ∧ (z ∈ a ∧ N → z ∈ S))` with `a` the ambient variable `k` and
`N` over `(z, ambient)`. -/
def sepAx (k : Nat) (N : IFml) : IFml :=
  .ex (.all (.and (.imp (.mem 0 1) (.and (.mem 0 (k+2)) (N.rename sepR)))
    (.imp (.and (.mem 0 (k+2)) (N.rename sepR)) (.mem 0 1))))

/-- The witness is the object `{z ∈ a | N}`; the forward direction returns the canonical realizer of
`N`, the backward direction returns a token. -/
def sepCode (k : Nat) (N : IFml) : RCode :=
  .pack (.sepNeg (.var k) N) (.gen (.pair (.app .k (.pair .tok (canon N))) (.app .k .tok)))

/-- The body of the Separation realizer at the witness and an element `z`. -/
theorem neg_sep_body {N : IFml} (hN : Neg N) (k : Nat) (e : Env.{u}) (z : PSet.{u}) :
    Realizes (.and (.imp (.mem 0 1) (.and (.mem 0 (k+2)) (N.rename sepR)))
        (.imp (.and (.mem 0 (k+2)) (N.rename sepR)) (.mem 0 1)))
      (Fml.up (Fml.up fun n => n)) (Env.cons z (Env.cons (Obj.eval (.sepNeg (.var k) N) e) e))
      (.pair (.app .k (.pair .tok (canon N))) (.app .k .tok)) := by
  refine ⟨nn_intro ⟨⟨_, .refl _, rfl⟩⟩, fun r3 => ?_⟩
  have hr3 : r3.1 = .pair (.app .k (.pair .tok (canon N))) (.app .k .tok) :=
    reduces_of_normal (fun _ h => step_pair h) r3.2.1
  rw [hr3]
  refine ⟨fun ρ e' hρ d hd => ?_, fun ρ e' hρ d hd => ?_⟩
  · show Realizes _ _ e' (.app (.app .k (.pair .tok (RCode.rename ρ (canon N)))) d)
    rw [canon_rename]
    refine (realizes_of_reduces _ (.single .k)).2 ⟨nn_intro ⟨⟨_, .refl _, rfl⟩⟩, fun r4 => ?_⟩
    have hr4 : r4.1 = .pair .tok (canon N) := reduces_of_normal (fun _ h => step_pair h) r4.2.1
    rw [hr4]
    have hz : e' (ρ 0) ∈ sep (fun z => Truth N (Env.cons z e)) (e k) := (mem_congr_right (hρ 1).symm).1 hd
    have hs := (mem_sep (truth_cons_resp N e)).1 hz
    refine ⟨(mem_congr_right (hρ (k+2))).1 hs.1, ?_⟩
    refine (realizes_rename N).2 ((neg_reflect hN _ e').2 ?_)
    refine (truth_congr N (fun n => ?_)).1 hs.2
    rcases n with _ | n
    · exact Equiv.refl _
    · exact hρ (n+2)
  · show e' (ρ 0) ∈ e' (ρ 1)
    refine Stable.of_nn hd.1 fun ⟨r4⟩ => ?_
    have h1 : e' (ρ 0) ∈ e k := (mem_congr_right (hρ (k+2)).symm).1 (hd.2 r4).1
    have h2 := (neg_reflect (hN.rename sepR) _ e').1 _ (hd.2 r4).2
    have hal : Along sepR (Env.cons (e' (ρ 0)) e) (fun n => e' (ρ (Fml.up (Fml.up fun n => n) n))) := fun n => by
      rcases n with _ | n
      · exact Equiv.refl _
      · exact hρ (n+2)
    have h3 : Truth N (Env.cons (e' (ρ 0)) e) := (truth_rename N hal).1 h2
    exact (mem_congr_right (hρ 1)).1 ((mem_sep (truth_cons_resp N e)).2 ⟨h1, h3⟩)

/-- Negative Separation with a reconstructible witness. -/
theorem neg_sep {N : IFml} (hN : Neg N) (k : Nat) (e : Env.{u}) :
    Realizes (sepAx k N) (fun n => n) e (sepCode k N) := by
  refine ⟨nn_intro ⟨⟨_, .refl _, rfl⟩⟩, fun r => ?_⟩
  have hr : r.1 = sepCode k N := reduces_of_normal (fun _ h => step_pack h) r.2.1
  rw [hr]
  intro z
  refine ⟨nn_intro ⟨⟨_, .refl _, rfl⟩⟩, fun r2 => ?_⟩
  have hr2 : r2.1 = .gen (.pair (.app .k (.pair .tok (canon N))) (.app .k .tok)) :=
    reduces_of_normal (fun _ h => step_gen h) r2.2.1
  rw [hr2]
  exact neg_sep_body hN k e z

/-! ### Tests -/

/-- Existential elimination into an existential conclusion: the eliminated witness (variable `1`
inside the lifted conclusion) is absent from the conclusion. -/
theorem test_ex_elim_repack {σ : Nat → Nat} {e : Env.{u}} {c : RCode} (hc : Realizes (.ex (.mem 0 1)) σ e c) :
    Realizes (.ex (.mem 0 1)) σ e (.exElim (.gen (.app .k (.pack (.var 0) .tok))) c) := by
  refine ex_elim (B := .ex (.mem 0 1)) (fun _ => ⟨nn_intro ⟨⟨_, .refl _, rfl⟩⟩, fun r => ?_⟩) hc
  have hr : r.1 = .gen (.app .k (.pack (.var 0) .tok)) := reduces_of_normal (fun _ h => step_gen h) r.2.1
  rw [hr]
  intro ρ e' _ d hd
  refine (realizes_of_reduces _ (.single .k)).2 ⟨nn_intro ⟨⟨_, .refl _, rfl⟩⟩, fun r' => ?_⟩
  have hr' : r'.1 = .pack (.var (ρ 0)) .tok := reduces_of_normal (fun _ h => step_pack h) r'.2.1
  rw [hr']
  exact hd

/-- Projection through the actual pair head of the Separation body, applied to a membership
realizer, then projected again. -/
theorem test_sep_projection {N : IFml} (hN : Neg N) (k : Nat) (e : Env.{u}) (z : PSet.{u}) {d : RCode}
    (hd : Realizes (.mem 0 1) (fun n => n) (Env.cons z (Env.cons (Obj.eval (.sepNeg (.var k) N) e) e)) d) :
    Realizes (.mem 0 (k+2)) (fun n => n) (Env.cons z (Env.cons (Obj.eval (.sepNeg (.var k) N) e) e))
      (.fst (.app (.fst (.pair (.app .k (.pair .tok (canon N))) (.app .k .tok))) d)) := by
  have h2 := neg_sep_body hN k e z
  have h3 := imp_elim (and_fst h2) (realizes_congr_σ _ (fun n => by rcases n with _ | _ | n <;> rfl) hd)
  exact realizes_congr_σ _ (fun n => by rcases n with _ | _ | n <;> rfl) (and_fst h3)

/-- Universal elimination at a variable followed by existential introduction at the same variable. -/
theorem test_all_ex {a : IFml} {σ : Nat → Nat} {e : Env.{u}} {c : RCode} (m : Nat)
    (hc : Realizes (.all a) σ e c) : Realizes (.ex a) σ e (.pack (.var m) (RCode.lift (.uinstO (.var m) c))) :=
  ex_intro_var m (all_elim_var m hc)

/-- info: 'PSet.NegCore.step_det' does not depend on any axioms -/
#guard_msgs in #print axioms step_det
/-- info: 'PSet.NegCore.step_rename' does not depend on any axioms -/
#guard_msgs in #print axioms step_rename
/-- info: 'PSet.NegCore.realizes_of_reduces' does not depend on any axioms -/
#guard_msgs in #print axioms realizes_of_reduces
/-- info: 'PSet.NegCore.realizes_mono' does not depend on any axioms -/
#guard_msgs in #print axioms realizes_mono
/-- info: 'PSet.NegCore.letObj_realizes' does not depend on any axioms -/
#guard_msgs in #print axioms letObj_realizes
/-- info: 'PSet.NegCore.s_realizes' does not depend on any axioms -/
#guard_msgs in #print axioms s_realizes
/-- info: 'PSet.NegCore.nn_realizes' does not depend on any axioms -/
#guard_msgs in #print axioms nn_realizes
/-- info: 'PSet.NegCore.ex_intro_var' does not depend on any axioms -/
#guard_msgs in #print axioms ex_intro_var
/-- info: 'PSet.NegCore.all_elim_inst' does not depend on any axioms -/
#guard_msgs in #print axioms all_elim_inst
/-- info: 'PSet.NegCore.all_elim_obj' does not depend on any axioms -/
#guard_msgs in #print axioms all_elim_obj
/-- info: 'PSet.NegCore.ex_elim' does not depend on any axioms -/
#guard_msgs in #print axioms ex_elim
/-- info: 'PSet.NegCore.neg_reflect' does not depend on any axioms -/
#guard_msgs in #print axioms neg_reflect
/-- info: 'PSet.NegCore.neg_sep' does not depend on any axioms -/
#guard_msgs in #print axioms neg_sep
/-- info: 'PSet.NegCore.test_ex_elim_repack' does not depend on any axioms -/
#guard_msgs in #print axioms test_ex_elim_repack
/-- info: 'PSet.NegCore.test_sep_projection' does not depend on any axioms -/
#guard_msgs in #print axioms test_sep_projection
/-- info: 'PSet.NegCore.test_all_ex' does not depend on any axioms -/
#guard_msgs in #print axioms test_all_ex

end PSet.NegCore
