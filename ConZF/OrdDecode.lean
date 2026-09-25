import ConZF.Assign
import ConZF.Reflection
/-!
The Σ₁ ordinal decoder. A *diagram* is a pair `⟨A, r⟩` of a set and a relation; the decoder says
that an ordinal `α` is order-isomorphic to `⟨A, r⟩` by an onto pure map `f : α → A`. The formula
`decodeF` has free variables `d = 0` (the diagram) and `α = 1` (the ordinal) and one unbounded
existential, over the isomorphism graph `f`; every other quantifier is membership-bounded. This is
recorded by the certificate `BForm`, a syntax of bounded formulas compiled into `Fml`.

* `BForm.absolute`: a bounded formula is absolute between any transitive class and the universe,
  with parameters in the class; only transitivity is used.
* `BForm.read`: its exact reading `BForm.eval`, so that the compiled formula is read back into
  ordinary statements about `PSet`.
* `decode_read`: the exact reading of `decodeF` in any transitive class `M`, as `DecodedIn M`,
  with the class guards on the three existential witnesses `A`, `r`, `f` kept explicit.
* `decoded_unique`, `graphs_unique`: the decoded ordinal and even the isomorphism graph are
  unique (stable membership induction; injectivity of `f` follows from order reflection).
* `decode_upward`: Σ₁ upward absoluteness of this formula between transitive classes.

The class of diagrams over a base `U` is `diagrams U = 𝒫 U × 𝒫 (U × U)`. Nothing here assumes a
model, Replacement, or accessibility. What is *not* proved: arbitrary-formula completeness (only
this one formula is read), and any common bound on the decoded ordinals.
-/
universe u

namespace PSet.OrdDecode
open Fml

/-! ### Bounded formulas -/

/-- Membership-bounded formulas. In `allIn a p` and `exIn a p`, the bound `a` is an index in the
environment *before* the bound variable is introduced. -/
inductive BForm : Type
  | mem (i j : Nat)
  | eq (i j : Nat)
  | fls
  | imp (p q : BForm)
  | conj (p q : BForm)
  | disj (p q : BForm)
  | biimp (p q : BForm)
  | allIn (a : Nat) (p : BForm)
  | exIn (a : Nat) (p : BForm)

namespace BForm

def compile : BForm → Fml
  | .mem i j => .mem i j
  | .eq i j => .eq i j
  | .fls => .fls
  | .imp p q => .imp p.compile q.compile
  | .conj p q => Fml.and p.compile q.compile
  | .disj p q => Fml.or p.compile q.compile
  | .biimp p q => Fml.iff p.compile q.compile
  | .allIn a p => .all (.imp (.mem 0 (a+1)) p.compile)
  | .exIn a p => Fml.ex (Fml.and (.mem 0 (a+1)) p.compile)

/-- All free variables below `k`. -/
def Scoped : Nat → BForm → Prop
  | k, .mem i j => i < k ∧ j < k
  | k, .eq i j => i < k ∧ j < k
  | _, .fls => True
  | k, .imp p q => Scoped k p ∧ Scoped k q
  | k, .conj p q => Scoped k p ∧ Scoped k q
  | k, .disj p q => Scoped k p ∧ Scoped k q
  | k, .biimp p q => Scoped k p ∧ Scoped k q
  | k, .allIn a p => a < k ∧ Scoped (k+1) p
  | k, .exIn a p => a < k ∧ Scoped (k+1) p

def decScoped : ∀ (k : Nat) (b : BForm), Decidable (Scoped k b)
  | _, .mem _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | _, .eq _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | _, .fls => inferInstanceAs (Decidable True)
  | k, .imp p q => have := decScoped k p; have := decScoped k q
    inferInstanceAs (Decidable (Scoped k p ∧ Scoped k q))
  | k, .conj p q => have := decScoped k p; have := decScoped k q
    inferInstanceAs (Decidable (Scoped k p ∧ Scoped k q))
  | k, .disj p q => have := decScoped k p; have := decScoped k q
    inferInstanceAs (Decidable (Scoped k p ∧ Scoped k q))
  | k, .biimp p q => have := decScoped k p; have := decScoped k q
    inferInstanceAs (Decidable (Scoped k p ∧ Scoped k q))
  | k, .allIn a p => have := decScoped (k+1) p
    inferInstanceAs (Decidable (a < k ∧ Scoped (k+1) p))
  | k, .exIn a p => have := decScoped (k+1) p
    inferInstanceAs (Decidable (a < k ∧ Scoped (k+1) p))

instance {k : Nat} {b : BForm} : Decidable (Scoped k b) := decScoped k b

theorem compile_bound : ∀ {b : BForm} {k : Nat}, Scoped k b → Bound k b.compile
  | .mem _ _, _, h => h
  | .eq _ _, _, h => h
  | .fls, _, h => h
  | .imp _ _, _, h => ⟨compile_bound h.1, compile_bound h.2⟩
  | .conj _ _, _, h => (compile_bound h.1).and (compile_bound h.2)
  | .disj _ _, _, h => (compile_bound h.1).or (compile_bound h.2)
  | .biimp _ _, _, h => (compile_bound h.1).iff (compile_bound h.2)
  | .allIn _ _, _, h => ⟨⟨Nat.zero_lt_succ _, Nat.succ_lt_succ h.1⟩, compile_bound h.2⟩
  | .exIn a _, k, h =>
    ((show Bound (k+1) (.mem 0 (a+1)) from ⟨Nat.zero_lt_succ _, Nat.succ_lt_succ h.1⟩).and
      (compile_bound h.2)).ex

/-- Bounded absoluteness: only transitivity of the class and membership of the parameters. -/
theorem absolute {M : PSet.{u} → Prop} (tr : ∀ {a x}, M a → x ∈ a → M x) :
    ∀ b : BForm, ∀ E : Nat → PSet.{u}, (∀ i, M (E i)) →
      (Sat M b.compile E ↔ Sat (fun _ => True) b.compile E)
  | .mem _ _, _, _ => Iff.rfl
  | .eq _ _, _, _ => Iff.rfl
  | .fls, _, _ => Iff.rfl
  | .imp p q, E, hE =>
    have hp := absolute tr p E hE
    have hq := absolute tr q E hE
    ⟨fun h a => hq.1 (h (hp.2 a)), fun h a => hq.2 (h (hp.1 a))⟩
  | .conj p q, E, hE =>
    sat_and.trans ((and_congr (absolute tr p E hE) (absolute tr q E hE)).trans sat_and.symm)
  | .disj p q, E, hE =>
    sat_or.trans ((nn_congr (or_congr (absolute tr p E hE) (absolute tr q E hE))).trans
      sat_or.symm)
  | .biimp p q, E, hE =>
    have hp := absolute tr p E hE
    have hq := absolute tr q E hE
    sat_iff.trans (.trans
      ⟨fun h => ⟨fun a => hq.1 (h.1 (hp.2 a)), fun a => hp.1 (h.2 (hq.2 a))⟩,
       fun h => ⟨fun a => hq.2 (h.1 (hp.1 a)), fun a => hp.2 (h.2 (hq.1 a))⟩⟩ sat_iff.symm)
  | .allIn a p, E, hE =>
    ⟨fun h x _ hx => (absolute tr p (Env.cons x E) (Env.cons_mem (tr (hE a) hx) hE)).1
        (h x (tr (hE a) hx) hx),
     fun h x hxM hx => (absolute tr p (Env.cons x E) (Env.cons_mem hxM hE)).2 (h x trivial hx)⟩
  | .exIn a p, E, hE =>
    ⟨fun h => sat_ex.2 (nn_map (fun ⟨x, hxM, hs⟩ =>
        have hpair := sat_and.1 hs
        ⟨x, trivial, sat_and.2 ⟨hpair.1,
          (absolute tr p (Env.cons x E) (Env.cons_mem hxM hE)).1 hpair.2⟩⟩) (sat_ex.1 h)),
     fun h => sat_ex.2 (nn_map (fun ⟨x, _, hs⟩ =>
        have hpair := sat_and.1 hs
        have hxM := tr (hE a) hpair.1
        ⟨x, hxM, sat_and.2 ⟨hpair.1,
          (absolute tr p (Env.cons x E) (Env.cons_mem hxM hE)).2 hpair.2⟩⟩) (sat_ex.1 h))⟩

/-- The intended reading of a bounded formula. -/
def eval : BForm → (Nat → PSet.{u}) → Prop
  | .mem i j, E => E i ∈ E j
  | .eq i j, E => E i ≈ E j
  | .fls, _ => False
  | .imp p q, E => p.eval E → q.eval E
  | .conj p q, E => p.eval E ∧ q.eval E
  | .disj p q, E => ¬¬(p.eval E ∨ q.eval E)
  | .biimp p q, E => p.eval E ↔ q.eval E
  | .allIn a p, E => ∀ x, x ∈ E a → p.eval (Env.cons x E)
  | .exIn a p, E => ¬¬∃ x, x ∈ E a ∧ p.eval (Env.cons x E)

theorem eval_stable : ∀ b : BForm, ∀ E : Nat → PSet.{u}, Stable (b.eval E)
  | .mem _ _, _ => inferInstanceAs (Stable (_ ∈ _))
  | .eq _ _, _ => inferInstanceAs (Stable (_ ≈ _))
  | .fls, _ => inferInstanceAs (Stable False)
  | .imp _ q, E => have := eval_stable q E; inferInstanceAs (Stable (_ → _))
  | .conj p q, E => have := eval_stable p E; have := eval_stable q E
    inferInstanceAs (Stable (_ ∧ _))
  | .disj _ _, _ => inferInstanceAs (Stable (¬ _))
  | .biimp p q, E => have := eval_stable p E; have := eval_stable q E
    inferInstanceAs (Stable (_ ↔ _))
  | .allIn _ p, E => have := fun x => eval_stable p (Env.cons x E)
    inferInstanceAs (Stable (∀ _, _ → _))
  | .exIn _ _, _ => inferInstanceAs (Stable (¬ _))

instance {b : BForm} {E : Nat → PSet.{u}} : Stable (b.eval E) := eval_stable b E

theorem all_read : ∀ b : BForm, ∀ E : Nat → PSet.{u},
    Sat (fun _ => True) b.compile E ↔ b.eval E
  | .mem _ _, _ => Iff.rfl
  | .eq _ _, _ => Iff.rfl
  | .fls, _ => Iff.rfl
  | .imp p q, E =>
    have hp := all_read p E
    have hq := all_read q E
    ⟨fun h a => hq.1 (h (hp.2 a)), fun h a => hq.2 (h (hp.1 a))⟩
  | .conj p q, E => sat_and.trans (and_congr (all_read p E) (all_read q E))
  | .disj p q, E => sat_or.trans (nn_congr (or_congr (all_read p E) (all_read q E)))
  | .biimp p q, E =>
    have hp := all_read p E
    have hq := all_read q E
    sat_iff.trans
      ⟨fun h => ⟨fun a => hq.1 (h.1 (hp.2 a)), fun a => hp.1 (h.2 (hq.2 a))⟩,
       fun h => ⟨fun a => hq.2 (h.1 (hp.1 a)), fun a => hp.2 (h.2 (hq.1 a))⟩⟩
  | .allIn _ p, E =>
    ⟨fun h x hx => (all_read p (Env.cons x E)).1 (h x trivial hx),
     fun h x _ hx => (all_read p (Env.cons x E)).2 (h x hx)⟩
  | .exIn _ p, E =>
    sat_ex.trans (nn_congr
      ⟨fun ⟨x, _, h⟩ => ⟨x, (sat_and.1 h).1, (all_read p (Env.cons x E)).1 (sat_and.1 h).2⟩,
       fun ⟨x, hx, h⟩ => ⟨x, trivial, sat_and.2 ⟨hx, (all_read p (Env.cons x E)).2 h⟩⟩⟩)

/-- Exact reading in a transitive class. -/
theorem read {M : PSet.{u} → Prop} (tr : ∀ {a x}, M a → x ∈ a → M x) (b : BForm)
    (E : Nat → PSet.{u}) (hE : ∀ i, M (E i)) : Sat M b.compile E ↔ b.eval E :=
  (absolute tr b E hE).trans (all_read b E)

end BForm

/-! ### The decoder -/

namespace B
open BForm

def sing (s x : Nat) : BForm := .conj (.mem x s) (.allIn s (.eq 0 (x+1)))

def upair (s x y : Nat) : BForm :=
  .conj (.mem x s) (.conj (.mem y s) (.allIn s (.disj (.eq 0 (x+1)) (.eq 0 (y+1)))))

/-- Kuratowski pair `p = ⟨x, y⟩`, every quantifier bounded by `p`. -/
def pair (p x y : Nat) : BForm :=
  .exIn p (.conj (sing 0 (x+1))
    (.exIn (p+1) (.conj (upair 0 (x+2) (y+2)) (.allIn (p+2) (.disj (.eq 0 2) (.eq 0 1))))))

def edge (f x y : Nat) : BForm := .exIn f (pair 0 (x+1) (y+1))

def trans (a : Nat) : BForm := .allIn a (.allIn 0 (.mem 0 (a+2)))

def ordinal (a : Nat) : BForm := .conj (trans a) (.allIn a (trans 0))

def typed (f a A : Nat) : BForm := .allIn f (.exIn (a+1) (.exIn (A+2) (pair 2 1 0)))

def total (f a A : Nat) : BForm := .allIn a (.exIn (A+1) (edge (f+2) 1 0))

def functional (f a A : Nat) : BForm :=
  .allIn a (.allIn (A+1) (.allIn (A+2)
    (.imp (edge (f+3) 2 1) (.imp (edge (f+3) 2 0) (.eq 1 0)))))

def map (f a A : Nat) : BForm := .conj (typed f a A) (.conj (total f a A) (functional f a A))

def onto (f a A : Nat) : BForm := .allIn A (.exIn (a+1) (edge (f+2) 0 1))

def relationPure (r A : Nat) : BForm := .allIn r (.exIn (A+1) (.exIn (A+2) (pair 2 1 0)))

def order (f r a A : Nat) : BForm :=
  .allIn a (.allIn (a+1) (.allIn (A+2) (.allIn (A+3)
    (.imp (edge (f+4) 3 1) (.imp (edge (f+4) 2 0) (.biimp (edge (r+4) 1 0) (.mem 3 2)))))))

/-- Environment `[f, d, α]`. Four bounded binders extract `A` and `r` from `d`, giving the
environment `[r, T, A, S, f, d, α]` for the matrix. -/
def body : BForm :=
  .exIn 1 (.exIn 0 (.exIn 3 (.exIn 0
    (.conj (pair 5 2 0)
      (.conj (ordinal 6)
        (.conj (map 4 6 2)
          (.conj (onto 4 6 2)
            (.conj (relationPure 0 2) (order 4 0 6 2)))))))))

set_option maxRecDepth 200000 in
theorem body_scoped : BForm.Scoped 3 body := by decide

end B

/-- The decoder: free variables `d = 0`, `α = 1`; the only unbounded quantifier is over `f`. -/
def decodeF : Fml := Fml.ex B.body.compile

theorem bound_decodeF : Bound 2 decodeF := (BForm.compile_bound B.body_scoped).ex

/-- Σ₁ upward absoluteness of this formula between transitive classes. -/
theorem decode_upward {M N : PSet.{u} → Prop} (trM : ∀ {a x}, M a → x ∈ a → M x)
    (trN : ∀ {a x}, N a → x ∈ a → N x) (inc : ∀ x, M x → N x) (E : Nat → PSet.{u})
    (hE : ∀ i, M (E i)) (h : Sat M decodeF E) : Sat N decodeF E := by
  refine sat_ex.2 (nn_map (fun ⟨f, hf, hs⟩ => ?_) (sat_ex.1 h))
  have hm := Env.cons_mem hf hE
  have hn := Env.cons_mem (inc f hf) (fun i => inc (E i) (hE i))
  exact ⟨f, inc f hf, (BForm.absolute trN B.body (Env.cons f E) hn).2
    ((BForm.absolute trM B.body (Env.cons f E) hm).1 hs)⟩

/-! ### Semantics -/

/-- `f` is an onto pure map from the ordinal `a` to `A` carrying `∈` to `r` exactly. Injectivity is
not assumed: it follows (`OrderedSurjection.injective`). -/
structure OrderedSurjection (r A a f : PSet.{u}) : Prop where
  map : IsPureFun A f a
  onto : ∀ v, v ∈ A → ¬¬∃ i, pair i v ∈ f
  pure : ∀ q, q ∈ r → ¬¬∃ v w, v ∈ A ∧ w ∈ A ∧ q ≈ pair v w
  order : ∀ i j v w, pair i v ∈ f → pair j w ∈ f → (pair v w ∈ r ↔ i ∈ j)

instance {r A a f : PSet.{u}} : Stable (OrderedSurjection r A a f) :=
  ⟨fun h => ⟨Stable.of_nn h fun z => z.map, fun v hv => Stable.of_nn h fun z => z.onto v hv,
    fun q hq => Stable.of_nn h fun z => z.pure q hq,
    fun i j v w hi hj => Stable.of_nn h fun z => z.order i j v w hi hj⟩⟩

theorem map_edge_typed {f a A i v : PSet.{u}} (hf : IsPureFun A f a) (h : pair i v ∈ f) :
    i ∈ a ∧ v ∈ A :=
  Stable.of_nn (hf.1 _ h) fun ⟨_, _, hj, hw, e⟩ =>
    ⟨(mem_congr_left (pair_inj e).1).2 hj, (mem_congr_left (pair_inj e).2).2 hw⟩

theorem OrderedSurjection.injective {r A a f : PSet.{u}} (ha : IsOrd a)
    (hf : OrderedSurjection r A a f) :
    ∀ i j v w, pair i v ∈ f → pair j w ∈ f → v ≈ w → i ≈ j := by
  intro i j v w hi hj evw
  have noij : ¬ i ∈ j := fun hij => not_mem_self i ((hf.order i i v v hi hi).1
    ((mem_congr_left (pair_congr (Equiv.refl v) evw.symm)).1 ((hf.order i j v w hi hj).2 hij)))
  have noji : ¬ j ∈ i := fun hji => not_mem_self i ((hf.order i i v v hi hi).1
    ((mem_congr_left (pair_congr evw.symm (Equiv.refl v))).1 ((hf.order j i w v hj hi).2 hji)))
  refine Stable.of_nn ((ha.mem (map_edge_typed hf.map hi).1).trichotomy
    (ha.mem (map_edge_typed hf.map hj).1)) fun
    | .inl hij => (noij hij).elim
    | .inr (.inl e) => e
    | .inr (.inr hji) => (noji hji).elim

/-- Two ordered surjections onto the same diagram agree at common image points. -/
theorem agree {r A a b f g : PSet.{u}} (ha : IsOrd a) (hb : IsOrd b)
    (hf : OrderedSurjection r A a f) (hg : OrderedSurjection r A b g) :
    ∀ i j v w, pair i v ∈ f → pair j w ∈ g → v ≈ w → i ≈ j := by
  refine mem_induction (P := fun i => ∀ j v w, pair i v ∈ f → pair j w ∈ g → v ≈ w → i ≈ j) ?_
  intro i ih j v w hiv hjw evw
  refine ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · have hza := ha.trans i (map_edge_typed hf.map hiv).1 z hz
    refine Stable.of_nn (hf.map.2.1 z hza) fun ⟨v', hzv⟩ => ?_
    refine Stable.of_nn (hg.onto v' (map_edge_typed hf.map hzv).2) fun ⟨j', hj'⟩ => ?_
    have hr : pair v' w ∈ r := (mem_congr_left (pair_congr (Equiv.refl _) evw)).1
      ((hf.order z i v' v hzv hiv).2 hz)
    have hjj : j' ∈ j := (hg.order j' j v' w hj' hjw).1 hr
    exact (mem_congr_left (ih z hz j' v' v' hzv hj' (Equiv.refl _))).2 hjj
  · have hzb := hb.trans j (map_edge_typed hg.map hjw).1 z hz
    refine Stable.of_nn (hg.map.2.1 z hzb) fun ⟨w', hzw⟩ => ?_
    refine Stable.of_nn (hf.onto w' (map_edge_typed hg.map hzw).2) fun ⟨i', hi'⟩ => ?_
    have hr : pair w' v ∈ r := (mem_congr_left (pair_congr (Equiv.refl _) evw)).2
      ((hg.order z j w' w hzw hjw).2 hz)
    have hii : i' ∈ i := (hf.order i' i w' v hi' hiv).1 hr
    exact (mem_congr_left (ih i' hii z w' w' hi' hzw (Equiv.refl _))).1 hii

theorem domains_unique {r A a b f g : PSet.{u}} (ha : IsOrd a) (hb : IsOrd b)
    (hf : OrderedSurjection r A a f) (hg : OrderedSurjection r A b g) : a ≈ b := by
  refine ext fun i => ⟨fun hi => ?_, fun hi => ?_⟩
  · refine Stable.of_nn (hf.map.2.1 i hi) fun ⟨v, hiv⟩ => ?_
    refine Stable.of_nn (hg.onto v (map_edge_typed hf.map hiv).2) fun ⟨j, hjv⟩ => ?_
    exact (mem_congr_left (agree ha hb hf hg i j v v hiv hjv (Equiv.refl _))).2
      (map_edge_typed hg.map hjv).1
  · refine Stable.of_nn (hg.map.2.1 i hi) fun ⟨v, hiv⟩ => ?_
    refine Stable.of_nn (hf.onto v (map_edge_typed hg.map hiv).2) fun ⟨j, hjv⟩ => ?_
    exact (mem_congr_left (agree ha hb hf hg j i v v hjv hiv (Equiv.refl _))).1
      (map_edge_typed hf.map hjv).1

/-- The isomorphism graph itself is unique. -/
theorem graphs_unique {r A a b f g : PSet.{u}} (ha : IsOrd a) (hb : IsOrd b)
    (hf : OrderedSurjection r A a f) (hg : OrderedSurjection r A b g) : f ≈ g := by
  refine ext fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · refine Stable.of_nn (hf.map.1 q hq) fun ⟨i, v, _, hv, e⟩ => ?_
    have hiv : pair i v ∈ f := (mem_congr_left e).1 hq
    refine Stable.of_nn (hg.onto v hv) fun ⟨j, hjv⟩ => ?_
    have eij := agree ha hb hf hg i j v v hiv hjv (Equiv.refl _)
    exact (mem_congr_left (e.trans (pair_congr eij (Equiv.refl _)))).2 hjv
  · refine Stable.of_nn (hg.map.1 q hq) fun ⟨j, v, _, hv, e⟩ => ?_
    have hjv : pair j v ∈ g := (mem_congr_left e).1 hq
    refine Stable.of_nn (hf.onto v hv) fun ⟨i, hiv⟩ => ?_
    have eij := agree ha hb hf hg i j v v hiv hjv (Equiv.refl _)
    exact (mem_congr_left (e.trans (pair_congr eij.symm (Equiv.refl _)))).2 hiv

/-- The ambient meaning of the decoder: `a` is an ordinal isomorphic to the diagram `d`. -/
def Decoded (d a : PSet.{u}) : Prop :=
  IsOrd a ∧ ¬¬∃ A r f, d ≈ pair A r ∧ OrderedSurjection r A a f

instance {d a : PSet.{u}} : Stable (Decoded d a) := inferInstanceAs (Stable (_ ∧ ¬ _))

theorem change_diagram {r r' A A' a f : PSet.{u}} (er : r ≈ r') (eA : A ≈ A')
    (h : OrderedSurjection r' A' a f) : OrderedSurjection r A a f := by
  refine ⟨⟨fun q hq => ?_, h.map.2.1, h.map.2.2⟩, fun v hv => h.onto v ((mem_congr_right eA).1 hv),
    fun q hq => ?_, fun i j v w hi hj => (mem_congr_right er).trans (h.order i j v w hi hj)⟩
  · exact nn_map (fun ⟨i, v, hi, hv, e⟩ => ⟨i, v, hi, (mem_congr_right eA).2 hv, e⟩) (h.map.1 q hq)
  · exact nn_map (fun ⟨v, w, hv, hw, e⟩ =>
      ⟨v, w, (mem_congr_right eA).2 hv, (mem_congr_right eA).2 hw, e⟩)
      (h.pure q ((mem_congr_right er).1 hq))

theorem OrderedSurjection.congr_dom {r A a a' f : PSet.{u}} (e : a ≈ a')
    (h : OrderedSurjection r A a f) : OrderedSurjection r A a' f := by
  refine ⟨⟨fun q hq => ?_, fun i hi => h.map.2.1 i ((mem_congr_right e).2 hi), h.map.2.2⟩,
    h.onto, h.pure, h.order⟩
  exact nn_map (fun ⟨i, v, hi, hv, e'⟩ => ⟨i, v, (mem_congr_right e).1 hi, hv, e'⟩) (h.map.1 q hq)

theorem decoded_unique {d a b : PSet.{u}} (ha : Decoded d a) (hb : Decoded d b) : a ≈ b := by
  refine Stable.of_nn ha.2 fun ⟨A, r, f, e, hf⟩ => Stable.of_nn hb.2 fun ⟨A', r', g, e', hg⟩ => ?_
  have ee := pair_inj (e.symm.trans e')
  exact domains_unique ha.1 hb.1 hf (change_diagram ee.2 ee.1 hg)

theorem decoded_congr {d d' a a' : PSet.{u}} (ed : d ≈ d') (ea : a ≈ a') (h : Decoded d a) :
    Decoded d' a' :=
  ⟨h.1.resp ea, nn_map (fun ⟨A, r, f, hd, hf⟩ => ⟨A, r, f, ed.symm.trans hd, hf.congr_dom ea⟩) h.2⟩

/-- The set of pairs `⟨a, b⟩`, `a ∈ A`, `b ∈ B`. -/
def product (A B : PSet.{u}) : PSet.{u} :=
  range (ι := A.Idx × B.Idx) fun p => pair (A.Func p.1) (B.Func p.2)

theorem mem_product {A B q : PSet.{u}} : q ∈ product A B ↔ ¬¬∃ a b, a ∈ A ∧ b ∈ B ∧ q ≈ pair a b := by
  constructor
  · exact nn_map fun ⟨p, e⟩ => ⟨A.Func p.1, B.Func p.2, func_mem A p.1, func_mem B p.2, e⟩
  · intro h
    refine nn_bind h fun ⟨a, b, ha, hb, e⟩ => nn_bind ha fun ⟨i, ei⟩ => ?_
    exact nn_map (fun ⟨j, ej⟩ => ⟨(i, j), e.trans (pair_congr ei ej)⟩) hb

/-- The diagrams over `U`: `𝒫 U × 𝒫 (U × U)`. -/
def diagrams (U : PSet.{u}) : PSet.{u} := product (powerset U) (powerset (product U U))

/-! ### Exact readback of the compiled formula -/

open BForm

theorem sing_read (E : Nat → PSet.{u}) (s x : Nat) :
    (B.sing s x).eval E ↔ E s ≈ singleton (E x) := by
  constructor
  · rintro ⟨hx, hs⟩
    exact ext fun z => ⟨fun hz => mem_singleton.2 (hs z hz),
      fun hz => (mem_congr_left (mem_singleton.1 hz)).2 hx⟩
  · intro e
    exact ⟨(mem_congr_right e).2 (self_mem_singleton _),
      fun z hz => mem_singleton.1 ((mem_congr_right e).1 hz)⟩

theorem upair_read (E : Nat → PSet.{u}) (s x y : Nat) :
    (B.upair s x y).eval E ↔ E s ≈ upair (E x) (E y) := by
  constructor
  · rintro ⟨hx, hy, hs⟩
    refine ext fun z => ⟨fun hz => mem_upair.2 (hs z hz), fun hz => ?_⟩
    exact Stable.of_nn (mem_upair.1 hz) fun
      | .inl e => (mem_congr_left e).2 hx
      | .inr e => (mem_congr_left e).2 hy
  · intro e
    exact ⟨(mem_congr_right e).2 (mem_upair_left _ _), (mem_congr_right e).2 (mem_upair_right _ _),
      fun z hz => mem_upair.1 ((mem_congr_right e).1 hz)⟩

theorem pair_read (E : Nat → PSet.{u}) (p x y : Nat) :
    (B.pair p x y).eval E ↔ E p ≈ pair (E x) (E y) := by
  constructor
  · intro h
    refine Stable.of_nn h fun ⟨s, hsp, hs, ht⟩ => Stable.of_nn ht fun ⟨t, htp, ht, hall⟩ => ?_
    have es := (sing_read (Env.cons s E) 0 (x+1)).1 hs
    have et := (upair_read (Env.cons t (Env.cons s E)) 0 (x+2) (y+2)).1 ht
    have ep : E p ≈ upair s t := by
      refine ext fun z => ⟨fun hz => mem_upair.2 (hall z hz), fun hz => ?_⟩
      exact Stable.of_nn (mem_upair.1 hz) fun
        | .inl e => (mem_congr_left e).2 hsp
        | .inr e => (mem_congr_left e).2 htp
    exact ep.trans (upair_congr es et)
  · intro ep
    have hs : singleton (E x) ∈ E p := (mem_congr_right ep).2 (mem_upair_left _ _)
    have ht : upair (E x) (E y) ∈ E p := (mem_congr_right ep).2 (mem_upair_right _ _)
    refine nn_intro ⟨_, hs, (sing_read (Env.cons _ E) 0 (x+1)).2 (Equiv.refl _), ?_⟩
    exact nn_intro ⟨_, ht, (upair_read (Env.cons _ (Env.cons _ E)) 0 (x+2) (y+2)).2 (Equiv.refl _),
      fun z hz => mem_upair.1 ((mem_congr_right ep).1 hz)⟩

theorem edge_read (E : Nat → PSet.{u}) (f x y : Nat) :
    (B.edge f x y).eval E ↔ pair (E x) (E y) ∈ E f := by
  constructor
  · intro h
    exact Stable.of_nn h fun ⟨p, hp, he⟩ =>
      (mem_congr_left ((pair_read (Env.cons p E) 0 (x+1) (y+1)).1 he)).1 hp
  · intro h
    exact nn_intro ⟨pair (E x) (E y), h,
      (pair_read (Env.cons (pair (E x) (E y)) E) 0 (x+1) (y+1)).2 (Equiv.refl _)⟩

theorem trans_read (E : Nat → PSet.{u}) (a : Nat) : (B.trans a).eval E ↔ Trans (E a) := Iff.rfl

theorem ordinal_read (E : Nat → PSet.{u}) (a : Nat) : (B.ordinal a).eval E ↔ IsOrd (E a) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.trans, h.mem_trans⟩⟩

theorem typed_read (E : Nat → PSet.{u}) (f a A : Nat) :
    (B.typed f a A).eval E ↔ ∀ q, q ∈ E f → ¬¬∃ i v, i ∈ E a ∧ v ∈ E A ∧ q ≈ pair i v := by
  constructor
  · intro h q hq
    refine nn_bind (h q hq) fun ⟨i, hi, hv⟩ => ?_
    exact nn_map (fun ⟨v, hv, he⟩ => ⟨i, v, hi, hv,
      (pair_read (Env.cons v (Env.cons i (Env.cons q E))) 2 1 0).1 he⟩) hv
  · intro h q hq
    exact nn_map (fun ⟨i, v, hi, hv, he⟩ => ⟨i, hi, nn_intro ⟨v, hv,
      (pair_read (Env.cons v (Env.cons i (Env.cons q E))) 2 1 0).2 he⟩⟩) (h q hq)

theorem map_read (E : Nat → PSet.{u}) (f a A : Nat) :
    (B.map f a A).eval E ↔ IsPureFun (E A) (E f) (E a) := by
  constructor
  · rintro ⟨ht, he, hf⟩
    have typed := (typed_read E f a A).1 ht
    refine ⟨typed, fun i hi => nn_map (fun ⟨v, _, hp⟩ =>
      ⟨v, (edge_read (Env.cons v (Env.cons i E)) (f+2) 1 0).1 hp⟩) (he i hi), ?_⟩
    intro i v w hiv hiw
    have h1 : i ∈ E a ∧ v ∈ E A := Stable.of_nn (typed _ hiv) fun ⟨_, _, hj, hz, ee⟩ =>
      ⟨(mem_congr_left (pair_inj ee).1).2 hj, (mem_congr_left (pair_inj ee).2).2 hz⟩
    have h2 : i ∈ E a ∧ w ∈ E A := Stable.of_nn (typed _ hiw) fun ⟨_, _, hj, hz, ee⟩ =>
      ⟨(mem_congr_left (pair_inj ee).1).2 hj, (mem_congr_left (pair_inj ee).2).2 hz⟩
    exact hf i h1.1 v h1.2 w h2.2
      ((edge_read (Env.cons w (Env.cons v (Env.cons i E))) (f+3) 2 1).2 hiv)
      ((edge_read (Env.cons w (Env.cons v (Env.cons i E))) (f+3) 2 0).2 hiw)
  · intro h
    refine ⟨(typed_read E f a A).2 h.1, fun i hi => ?_, fun i _ v _ w _ h1 h2 => ?_⟩
    · exact nn_map (fun ⟨v, hp⟩ => ⟨v, (map_edge_typed h hp).2,
        (edge_read (Env.cons v (Env.cons i E)) (f+2) 1 0).2 hp⟩) (h.2.1 i hi)
    · exact h.2.2 i v w ((edge_read (Env.cons w (Env.cons v (Env.cons i E))) (f+3) 2 1).1 h1)
        ((edge_read (Env.cons w (Env.cons v (Env.cons i E))) (f+3) 2 0).1 h2)

theorem onto_read (E : Nat → PSet.{u}) (f a A : Nat) (hf : IsPureFun (E A) (E f) (E a)) :
    (B.onto f a A).eval E ↔ ∀ v, v ∈ E A → ¬¬∃ i, pair i v ∈ E f := by
  constructor
  · intro h v hv
    exact nn_map (fun ⟨i, _, hp⟩ => ⟨i, (edge_read (Env.cons i (Env.cons v E)) (f+2) 0 1).1 hp⟩)
      (h v hv)
  · intro h v hv
    exact nn_map (fun ⟨i, hp⟩ => ⟨i, (map_edge_typed hf hp).1,
      (edge_read (Env.cons i (Env.cons v E)) (f+2) 0 1).2 hp⟩) (h v hv)

theorem order_read (E : Nat → PSet.{u}) (f r a A : Nat) (hf : IsPureFun (E A) (E f) (E a)) :
    (B.order f r a A).eval E ↔
      ∀ i j v w, pair i v ∈ E f → pair j w ∈ E f → (pair v w ∈ E r ↔ i ∈ j) := by
  constructor
  · intro h i j v w hi hj
    have ti := map_edge_typed hf hi
    have tj := map_edge_typed hf hj
    exact (edge_read (Env.cons w (Env.cons v (Env.cons j (Env.cons i E)))) (r+4) 1 0).symm.trans
      (h i ti.1 j tj.1 v ti.2 w tj.2
        ((edge_read (Env.cons w (Env.cons v (Env.cons j (Env.cons i E)))) (f+4) 3 1).2 hi)
        ((edge_read (Env.cons w (Env.cons v (Env.cons j (Env.cons i E)))) (f+4) 2 0).2 hj))
  · intro h i _ j _ v _ w _ hi hj
    exact (edge_read (Env.cons w (Env.cons v (Env.cons j (Env.cons i E)))) (r+4) 1 0).trans
      (h i j v w
        ((edge_read (Env.cons w (Env.cons v (Env.cons j (Env.cons i E)))) (f+4) 3 1).1 hi)
        ((edge_read (Env.cons w (Env.cons v (Env.cons j (Env.cons i E)))) (f+4) 2 0).1 hj))

/-- The matrix, with the witness `f` in slot `0`, `d` in slot `1`, `α` in slot `2`. -/
theorem body_read (E : Nat → PSet.{u}) :
    B.body.eval E ↔ ¬¬∃ A r, E 1 ≈ pair A r ∧ IsOrd (E 2) ∧ OrderedSurjection r A (E 2) (E 0) := by
  constructor
  · intro h
    refine nn_bind h fun ⟨S, _, hA⟩ => nn_bind hA fun ⟨A, _, hT⟩ =>
      nn_bind hT fun ⟨T, _, hr⟩ => nn_map (fun ⟨r, _, hh⟩ => ?_) hr
    have hm := (map_read (Env.cons r (Env.cons T (Env.cons A (Env.cons S E)))) 4 6 2).1 hh.2.2.1
    exact ⟨A, r, (pair_read (Env.cons r (Env.cons T (Env.cons A (Env.cons S E)))) 5 2 0).1 hh.1,
      (ordinal_read (Env.cons r (Env.cons T (Env.cons A (Env.cons S E)))) 6).1 hh.2.1,
      ⟨hm, (onto_read (Env.cons r (Env.cons T (Env.cons A (Env.cons S E)))) 4 6 2 hm).1 hh.2.2.2.1,
        (typed_read (Env.cons r (Env.cons T (Env.cons A (Env.cons S E)))) 0 2 2).1 hh.2.2.2.2.1,
        (order_read (Env.cons r (Env.cons T (Env.cons A (Env.cons S E)))) 4 0 6 2 hm).1
          hh.2.2.2.2.2⟩⟩
  · intro h
    refine nn_map (fun ⟨A, r, ed, ha, hf⟩ => ?_) h
    have hSd : singleton A ∈ E 1 := (mem_congr_right ed).2 (mem_upair_left _ _)
    have hTd : upair A r ∈ E 1 := (mem_congr_right ed).2 (mem_upair_right _ _)
    exact ⟨_, hSd, nn_intro ⟨A, self_mem_singleton A, nn_intro ⟨_, hTd,
      nn_intro ⟨r, mem_upair_right A r,
        (pair_read (Env.cons r (Env.cons _ (Env.cons A (Env.cons _ E)))) 5 2 0).2 ed,
        (ordinal_read (Env.cons r (Env.cons _ (Env.cons A (Env.cons _ E)))) 6).2 ha,
        (map_read (Env.cons r (Env.cons _ (Env.cons A (Env.cons _ E)))) 4 6 2).2 hf.map,
        (onto_read (Env.cons r (Env.cons _ (Env.cons A (Env.cons _ E)))) 4 6 2 hf.map).2 hf.onto,
        (typed_read (Env.cons r (Env.cons _ (Env.cons A (Env.cons _ E)))) 0 2 2).2 hf.pure,
        (order_read (Env.cons r (Env.cons _ (Env.cons A (Env.cons _ E)))) 4 0 6 2 hf.map).2
          hf.order⟩⟩⟩⟩

/-- The reading of `decodeF` in a class `M`: the three witnesses are guarded by `M`. -/
def DecodedIn (M : PSet.{u} → Prop) (d a : PSet.{u}) : Prop :=
  IsOrd a ∧ ¬¬∃ A r f, M A ∧ M r ∧ M f ∧ d ≈ pair A r ∧ OrderedSurjection r A a f

instance {M : PSet.{u} → Prop} {d a : PSet.{u}} : Stable (DecodedIn M d a) :=
  inferInstanceAs (Stable (_ ∧ ¬ _))

theorem DecodedIn.forget {M : PSet.{u} → Prop} {d a : PSet.{u}} (h : DecodedIn M d a) :
    Decoded d a :=
  ⟨h.1, nn_map (fun ⟨A, r, f, _, _, _, e, hf⟩ => ⟨A, r, f, e, hf⟩) h.2⟩

theorem decodedIn_unique {M : PSet.{u} → Prop} {d a b : PSet.{u}} (ha : DecodedIn M d a)
    (hb : DecodedIn M d b) : a ≈ b :=
  decoded_unique ha.forget hb.forget

theorem decodedIn_congr {M : PSet.{u} → Prop} {d d' a a' : PSet.{u}} (ed : d ≈ d') (ea : a ≈ a')
    (h : DecodedIn M d a) : DecodedIn M d' a' :=
  ⟨h.1.resp ea, nn_map (fun ⟨A, r, f, hA, hr, hf, e, hi⟩ =>
    ⟨A, r, f, hA, hr, hf, ed.symm.trans e, hi.congr_dom ea⟩) h.2⟩

/-- **Exact reading** of `decodeF` in any transitive class, environment in the class. -/
theorem decode_read {M : PSet.{u} → Prop} (tr : ∀ {a x}, M a → x ∈ a → M x) (E : Nat → PSet.{u})
    (hE : ∀ i, M (E i)) : Sat M decodeF E ↔ DecodedIn M (E 0) (E 1) := by
  have forward : Sat M decodeF E → ¬¬∃ A r f, M A ∧ M r ∧ M f ∧ E 0 ≈ pair A r ∧ IsOrd (E 1) ∧
      OrderedSurjection r A (E 1) f := by
    intro h
    refine nn_bind (sat_ex.1 h) fun ⟨f, hf, hb⟩ => ?_
    have hev := (BForm.read tr B.body (Env.cons f E) (Env.cons_mem hf hE)).1 hb
    refine nn_map (fun ⟨A, r, ed, ha, hi⟩ => ?_) ((body_read _).1 hev)
    have hS : M (singleton A) := tr (hE 0) ((mem_congr_right ed).2 (mem_upair_left _ _))
    have hT : M (upair A r) := tr (hE 0) ((mem_congr_right ed).2 (mem_upair_right _ _))
    exact ⟨A, r, f, tr hS (self_mem_singleton A), tr hT (mem_upair_right A r), hf, ed, ha, hi⟩
  constructor
  · intro h
    have h' := forward h
    exact ⟨Stable.of_nn h' fun ⟨_, _, _, _, _, _, _, ha, _⟩ => ha,
      nn_map (fun ⟨A, r, f, hA, hr, hf, ed, _, hi⟩ => ⟨A, r, f, hA, hr, hf, ed, hi⟩) h'⟩
  · intro h
    refine sat_ex.2 (nn_map (fun ⟨A, r, f, hA, hr, hf, ed, hi⟩ => ?_) h.2)
    exact ⟨f, hf, (BForm.read tr B.body (Env.cons f E) (Env.cons_mem hf hE)).2
      ((body_read _).2 (nn_intro ⟨A, r, ed, h.1, hi⟩))⟩

/-- Satisfaction of `decodeF` depends only on slots `0` and `1`. -/
theorem sat_decodeF_tail {M : PSet.{u} → Prop} {d a : PSet.{u}} (e e' : Nat → PSet.{u}) :
    Sat M decodeF (Env.cons d (Env.cons a e)) ↔ Sat M decodeF (Env.cons d (Env.cons a e')) :=
  sat_bound bound_decodeF fun i hi => by
    rcases i with _ | _ | i
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi))).elim

/-- info: 'PSet.OrdDecode.decode_read' does not depend on any axioms -/
#guard_msgs in #print axioms decode_read
/-- info: 'PSet.OrdDecode.graphs_unique' does not depend on any axioms -/
#guard_msgs in #print axioms graphs_unique
/-- info: 'PSet.OrdDecode.bound_decodeF' does not depend on any axioms -/
#guard_msgs in #print axioms bound_decodeF
/-- info: 'PSet.OrdDecode.decode_upward' does not depend on any axioms -/
#guard_msgs in #print axioms decode_upward

end PSet.OrdDecode
