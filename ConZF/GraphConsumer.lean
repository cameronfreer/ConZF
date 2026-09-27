import ConZF.Graph.Hartogs
import ConZF.Graph.Pair
import ConZF.Graph.Sat
import ConZF.Collection
import ConZF.OrdDecode
/-!
The graph interpretation of the literal decoder Collection instance (nc3), and a sound consumer of
source proofs using it. The source syntax `PSet.Fml` and its proof calculus `PSet.Prf` are
unchanged; the semantic domain is `GSet`, through the ambient specialization of the existing
`GSet.Sat`. Source existentials keep their negative reading. `NegCore` and its audits are untouched
and remain valid: nothing here reconstructs a positive witness descriptor.

* **Soundness** (`gsoundness`): every `Prf` constructor is validated over graph sets, so a theory
  whose axioms are graph-valid is consistent (`Con.of_gvalid`).
* **The base axioms.** Extensionality, Foundation (by stable membership induction), Pairing, Union,
  Power Set (the graph powerset law quantifies over all graph subsets), Infinity (graph finite
  ordinals as a small range), and **every** source Separation instance (`sep_gvalid`, by the exact
  graph Separation law at the stable, congruent satisfaction predicate).
* **The decoder adapter** (`gdec_injRel`): reading the existing bounded decoder body over graph sets
  (`evalG`, `evalG_read`), a successful decoding `d ∈ a`, `D_g(d, α)` gives `IsOrd α` and an
  injection relation `α → ⋃⋃⋃a`: the isomorphism graph's images lie in the triple union, and its
  inverse uniqueness follows from the order clause and ordinal trichotomy. Hence `α` lies in the
  relational Hartogs bound of the triple union. No decoder uniqueness and no representative is used.
* **The Collection instance** (`gvalid_coll_decodeF`): the explicit collector
  `relHartogs (⋃⋃⋃a) ∪ {a}` contains `a` and every decoded output, so the literal
  `coll (totalize decodeF)` holds at every environment, its conclusion outright.
* **The scoped consumer.** `TDec` is the theory with the base axioms, all Separation, and this one
  Collection formula; `con_tdec : Con TDec`. With the bridge factored through an arbitrary theory,
  `TDec` also proves the Replacement instance for the decoder (`prf_tdec_repl_decodeF`).

Not claimed: `Con ZF`, validity of unrestricted Collection, or any native (`PSet`) barrier. The
exact remaining theorem for full source adequacy is graph Collection for an arbitrary matrix.
-/
universe u

namespace GSet.Consumer
open PSet.Fml PSet.OrdDecode

/-! ### Soundness over graph sets -/

/-- Ambient graph validity. -/
def GValid (φ : PSet.Fml) : Prop := ∀ e : Nat → GSet.{u}, Sat (fun _ => True) φ e

theorem gsoundness {T : PSet.Fml → Prop} (hT : ∀ φ, T φ → GValid.{u} φ) {φ : PSet.Fml}
    (h : PSet.Prf T φ) : GValid.{u} φ := by
  induction h with
  | ax h => exact hT _ h
  | k => exact fun _ a _ => a
  | s => exact fun _ f g a => f a (g a)
  | dne => exact fun _ h => Stable.dne h
  | mp _ _ ih1 ih2 => exact fun e => ih1 e (ih2 e)
  | gen _ ih => exact fun e x _ => ih _
  | @inst φ j =>
    intro e h
    refine (sat_rename φ (PSet.Fml.inst j) e).2 (Sat.resp φ (fun i => ?_) (h (e j) trivial))
    cases i <;> exact Equiv.refl _
  | @dist φ ψ =>
    intro e h a x _
    refine h x trivial ((sat_rename φ Nat.succ (Env.cons x e)).2 ?_)
    exact Sat.resp φ (fun _ => Equiv.refl _) a
  | refl i => exact fun e => Equiv.refl (e i)
  | eq_mem_l => exact fun _ h1 h2 => (mem_congr_left h1).1 h2
  | eq_mem_r => exact fun _ h1 h2 => (mem_congr_right h1).1 h2
  | eq_eq => exact fun _ h1 h2 => h1.symm.trans h2

/-- The empty graph set. -/
def gempty : GSet.{u} := range fun i : PEmpty.{u+1} => i.elim

theorem not_mem_gempty (K : GSet.{u}) : ¬ Mem K gempty := fun h => (mem_range _).1 h fun ⟨i, _⟩ => i.elim

/-- A theory whose axioms are graph-valid is consistent. -/
theorem Con.of_gvalid {T : PSet.Fml → Prop} (hT : ∀ φ, T φ → GValid.{u} φ) : PSet.Con T :=
  fun h => gsoundness hT h fun _ => gempty

/-! ### The base axioms -/

theorem exists_minimal (x : GSet.{u}) :
    ∀ z, Mem z x → ¬¬∃ y, Mem y x ∧ ∀ w, Mem w y → ¬ Mem w x :=
  mem_induction (F := fun z => Mem z x → ¬¬∃ y, Mem y x ∧ ∀ w, Mem w y → ¬ Mem w x) fun z ih hz =>
    Stable.by_cases (∃ w, Mem w z ∧ Mem w x) (fun ⟨w, hw, hwx⟩ => ih w hw hwx)
      fun h => nn_intro ⟨z, hz, fun w hw hwx => h ⟨w, hw, hwx⟩⟩

def gsucc (x : GSet.{u}) : GSet.{u} := union x (single x)

theorem mem_gsucc (x z : GSet.{u}) : Mem z (gsucc x) ↔ ¬¬(Mem z x ∨ Equiv z x) :=
  (mem_union _ _).trans (nn_congr (or_congr Iff.rfl (mem_single _)))

def gOfNat : Nat → GSet.{u}
  | 0 => gempty
  | n+1 => gsucc (gOfNat n)

/-- Graph `ω`: the small range of the graph finite ordinals. -/
def gomega : GSet.{u} := range fun n : ULift.{u} Nat => gOfNat n.down

theorem gOfNat_mem_gomega (n : Nat) : Mem (gOfNat.{u} n) gomega :=
  (mem_range _).2 (nn_intro ⟨⟨n⟩, Equiv.refl _⟩)

theorem ext_gvalid : GValid.{u} PSet.ZFAx.ext := fun _ h =>
  ext fun z => ⟨fun hz => (sat_iff.1 (h z trivial)).1 hz, fun hz => (sat_iff.1 (h z trivial)).2 hz⟩

theorem found_gvalid : GValid.{u} PSet.ZFAx.found := by
  intro e h
  refine Stable.of_nn (sat_ex.1 h) fun ⟨z, _, hz⟩ => ?_
  refine Stable.of_nn (exists_minimal (e 0) z hz) fun ⟨y, hy, hmin⟩ => ?_
  exact sat_ex.2 (nn_intro ⟨y, trivial, sat_and.2 ⟨hy, fun w _ hw hwx => hmin w hw hwx⟩⟩)

theorem pair_gvalid : GValid.{u} PSet.ZFAx.pair := fun e =>
  sat_ex.2 (nn_intro ⟨pair (e 0) (e 1), trivial, sat_and.2 ⟨mem_pair_left _ _, mem_pair_right _ _⟩⟩)

theorem union_gvalid : GValid.{u} PSet.ZFAx.union := fun e =>
  sat_ex.2 (nn_intro ⟨sUnion (e 0), trivial, fun y _ _ _ hz hy => (mem_sUnion _).2 (nn_intro ⟨y, hy, hz⟩)⟩)

theorem power_gvalid : GValid.{u} PSet.ZFAx.power := fun e =>
  sat_ex.2 (nn_intro ⟨powerset (e 0), trivial, fun _ _ h => (mem_powerset _).2 fun z hz => h z trivial hz⟩)

theorem inf_gvalid : GValid.{u} PSet.ZFAx.inf := by
  intro e
  refine sat_ex.2 (nn_intro ⟨gomega, trivial, sat_and.2 ⟨?_, fun y _ hy => ?_⟩⟩)
  · exact sat_ex.2 (nn_intro ⟨gempty, trivial,
      sat_and.2 ⟨gOfNat_mem_gomega 0, fun z _ hz => not_mem_gempty z hz⟩⟩)
  · refine Stable.of_nn ((mem_range _).1 hy) fun ⟨n, e'⟩ => ?_
    refine sat_ex.2 (nn_intro ⟨gOfNat (n.down+1), trivial,
      sat_and.2 ⟨gOfNat_mem_gomega _, fun z _ => sat_iff.2 ?_⟩⟩)
    refine (mem_gsucc _ _).trans <| .trans (nn_congr ?_) sat_or.symm
    exact or_congr (mem_congr_right e').symm ⟨fun h => h.trans e'.symm, fun h => h.trans e'⟩

/-- **Every** source Separation instance is graph-valid. -/
theorem sep_gvalid (ψ : PSet.Fml) : GValid.{u} (PSet.ZFAx.sep ψ) := by
  intro e
  let P : GSet.{u} → Prop := fun z => Sat (fun _ => True) ψ (Env.cons z e)
  have hP : ∀ z z' : GSet.{u}, Equiv z z' → P z → P z' := fun _ _ ez h =>
    Sat.resp ψ (Env.cons_resp ez fun _ => Equiv.refl _) h
  have : ∀ z, Stable (P z) := fun z => Sat.stable ψ _
  refine sat_ex.2 (nn_intro ⟨sep P (e 0), trivial, fun z _ => sat_iff.2 ?_⟩)
  have hPz : P z ↔ Sat (fun _ => True) (rename PSet.ZFAx.sepR ψ) (Env.cons z (Env.cons (sep P (e 0)) e)) :=
    .trans (Sat.resp_iff (fun _ => Iff.rfl) ψ fun i => by cases i <;> exact Equiv.refl _)
      (sat_rename ψ PSet.ZFAx.sepR _).symm
  refine (mem_sep P (e 0) hP).trans ⟨fun ⟨a, b⟩ => sat_and.2 ⟨a, hPz.1 b⟩, fun h => ?_⟩
  have ⟨a, b⟩ := sat_and.1 h
  exact ⟨a, hPz.2 b⟩

/-! ### Reading the bounded decoder body over graph sets -/

/-- The graph reading of a bounded formula. -/
def evalG : BForm → (Nat → GSet.{u}) → Prop
  | .mem i j, E => Mem (E i) (E j)
  | .eq i j, E => Equiv (E i) (E j)
  | .fls, _ => False
  | .imp p q, E => evalG p E → evalG q E
  | .conj p q, E => evalG p E ∧ evalG q E
  | .disj p q, E => ¬¬(evalG p E ∨ evalG q E)
  | .biimp p q, E => evalG p E ↔ evalG q E
  | .allIn a p, E => ∀ x, Mem x (E a) → evalG p (Env.cons x E)
  | .exIn a p, E => ¬¬∃ x, Mem x (E a) ∧ evalG p (Env.cons x E)

theorem evalG_read : ∀ (b : BForm) (E : Nat → GSet.{u}), Sat (fun _ => True) b.compile E ↔ evalG b E
  | .mem _ _, _ => Iff.rfl
  | .eq _ _, _ => Iff.rfl
  | .fls, _ => Iff.rfl
  | .imp p q, E =>
    have hp := evalG_read p E
    have hq := evalG_read q E
    ⟨fun h a => hq.1 (h (hp.2 a)), fun h a => hq.2 (h (hp.1 a))⟩
  | .conj p q, E => sat_and.trans (and_congr (evalG_read p E) (evalG_read q E))
  | .disj p q, E => sat_or.trans (nn_congr (or_congr (evalG_read p E) (evalG_read q E)))
  | .biimp p q, E =>
    have hp := evalG_read p E
    have hq := evalG_read q E
    sat_iff.trans
      ⟨fun h => ⟨fun a => hq.1 (h.1 (hp.2 a)), fun a => hp.1 (h.2 (hq.2 a))⟩,
       fun h => ⟨fun a => hq.2 (h.1 (hp.1 a)), fun a => hp.2 (h.2 (hq.1 a))⟩⟩
  | .allIn _ p, E =>
    ⟨fun h x hx => (evalG_read p (Env.cons x E)).1 (h x trivial hx),
     fun h x _ hx => (evalG_read p (Env.cons x E)).2 (h x hx)⟩
  | .exIn _ p, E =>
    sat_ex.trans (nn_congr
      ⟨fun ⟨x, _, h⟩ => ⟨x, (sat_and.1 h).1, (evalG_read p (Env.cons x E)).1 (sat_and.1 h).2⟩,
       fun ⟨x, hx, h⟩ => ⟨x, trivial, sat_and.2 ⟨hx, (evalG_read p (Env.cons x E)).2 h⟩⟩⟩)

theorem sing_readG (E : Nat → GSet.{u}) (s x : Nat) : evalG (B.sing s x) E ↔ Equiv (E s) (single (E x)) := by
  constructor
  · rintro ⟨hx, hs⟩
    exact ext fun z => ⟨fun hz => (mem_single _).2 (hs z hz),
      fun hz => Mem.congr_left ((mem_single _).1 hz).symm hx⟩
  · intro e
    exact ⟨Mem.congr_right e.symm ((mem_single _).2 (Equiv.refl _)),
      fun z hz => (mem_single _).1 (Mem.congr_right e hz)⟩

theorem upair_readG (E : Nat → GSet.{u}) (s x y : Nat) :
    evalG (B.upair s x y) E ↔ Equiv (E s) (pair (E x) (E y)) := by
  constructor
  · rintro ⟨hx, hy, hs⟩
    refine ext fun z => ⟨fun hz => (mem_pair _ _).2 (hs z hz), fun hz => ?_⟩
    exact Stable.of_nn ((mem_pair _ _).1 hz) fun
      | .inl e => Mem.congr_left e.symm hx
      | .inr e => Mem.congr_left e.symm hy
  · intro e
    exact ⟨Mem.congr_right e.symm (mem_pair_left _ _), Mem.congr_right e.symm (mem_pair_right _ _),
      fun z hz => (mem_pair _ _).1 (Mem.congr_right e hz)⟩

theorem pair_readG (E : Nat → GSet.{u}) (p x y : Nat) :
    evalG (B.pair p x y) E ↔ Equiv (E p) (opair (E x) (E y)) := by
  constructor
  · intro h
    refine Stable.of_nn h fun ⟨s, hsp, hs, ht⟩ => Stable.of_nn ht fun ⟨t, htp, ht, hall⟩ => ?_
    have es := (sing_readG (Env.cons s E) 0 (x+1)).1 hs
    have et := (upair_readG (Env.cons t (Env.cons s E)) 0 (x+2) (y+2)).1 ht
    have ep : Equiv (E p) (pair s t) := by
      refine ext fun z => ⟨fun hz => (mem_pair _ _).2 (hall z hz), fun hz => ?_⟩
      exact Stable.of_nn ((mem_pair _ _).1 hz) fun
        | .inl e => Mem.congr_left e.symm hsp
        | .inr e => Mem.congr_left e.symm htp
    exact ep.trans (pair_congr _ _ es et)
  · intro ep
    have hs : Mem (single (E x)) (E p) := Mem.congr_right ep.symm (mem_pair_left _ _)
    have ht : Mem (pair (E x) (E y)) (E p) := Mem.congr_right ep.symm (mem_pair_right _ _)
    refine nn_intro ⟨_, hs, (sing_readG (Env.cons _ E) 0 (x+1)).2 (Equiv.refl _), ?_⟩
    exact nn_intro ⟨_, ht, (upair_readG (Env.cons _ (Env.cons _ E)) 0 (x+2) (y+2)).2 (Equiv.refl _),
      fun z hz => (mem_pair _ _).1 (Mem.congr_right ep hz)⟩

theorem edge_readG (E : Nat → GSet.{u}) (f x y : Nat) :
    evalG (B.edge f x y) E ↔ Mem (opair (E x) (E y)) (E f) := by
  constructor
  · intro h
    exact Stable.of_nn h fun ⟨p, hp, he⟩ =>
      Mem.congr_left ((pair_readG (Env.cons p E) 0 (x+1) (y+1)).1 he) hp
  · intro h
    exact nn_intro ⟨opair (E x) (E y), h,
      (pair_readG (Env.cons (opair (E x) (E y)) E) 0 (x+1) (y+1)).2 (Equiv.refl _)⟩

theorem ordinal_readG (E : Nat → GSet.{u}) (a : Nat) : evalG (B.ordinal a) E ↔ IsOrd (E a) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Edges are typed pairs. -/
def TypedG (f α A : GSet.{u}) : Prop := ∀ q, Mem q f → ¬¬∃ i v, Mem i α ∧ Mem v A ∧ Equiv q (opair i v)
/-- Every domain element has an image. -/
def TotalG (f α A : GSet.{u}) : Prop := ∀ i, Mem i α → ¬¬∃ v, Mem v A ∧ Mem (opair i v) f
/-- Edges transport membership on the domain to `r`. -/
def OrderG (f r α A : GSet.{u}) : Prop := ∀ i j v w, Mem i α → Mem j α → Mem v A → Mem w A →
  Mem (opair i v) f → Mem (opair j w) f → (Mem (opair v w) r ↔ Mem i j)

theorem typed_readG (E : Nat → GSet.{u}) (f a A : Nat) (h : evalG (B.typed f a A) E) : TypedG (E f) (E a) (E A) := by
  intro q hq
  refine nn_bind (h q hq) fun ⟨i, hi, hv⟩ => ?_
  exact nn_map (fun ⟨v, hv, he⟩ => ⟨i, v, hi, hv, (pair_readG (Env.cons v (Env.cons i (Env.cons q E))) 2 1 0).1 he⟩) hv

theorem total_readG (E : Nat → GSet.{u}) (f a A : Nat) (h : evalG (B.total f a A) E) : TotalG (E f) (E a) (E A) :=
  fun i hi => nn_map (fun ⟨v, hv, hp⟩ => ⟨v, hv, (edge_readG (Env.cons v (Env.cons i E)) (f+2) 1 0).1 hp⟩) (h i hi)

theorem order_readG (E : Nat → GSet.{u}) (f r a A : Nat) (h : evalG (B.order f r a A) E) :
    OrderG (E f) (E r) (E a) (E A) := fun i j v w hi hj hv hw h1 h2 =>
  (edge_readG (Env.cons w (Env.cons v (Env.cons j (Env.cons i E)))) (r+4) 1 0).symm.trans
    (h i hi j hj v hv w hw
      ((edge_readG (Env.cons w (Env.cons v (Env.cons j (Env.cons i E)))) (f+4) 3 1).2 h1)
      ((edge_readG (Env.cons w (Env.cons v (Env.cons j (Env.cons i E)))) (f+4) 2 0).2 h2))

theorem edge_typed {f α A ξ v : GSet.{u}} (ht : TypedG f α A) (h : Mem (opair ξ v) f) : Mem ξ α ∧ Mem v A :=
  Stable.of_nn (ht _ h) fun ⟨_, _, hi, hv, e⟩ =>
    ⟨Mem.congr_left (opair_inj _ _ e).1.symm hi, Mem.congr_left (opair_inj _ _ e).2.symm hv⟩

/-- The forward reading of the decoder body at `[f, d, α, …]`. -/
theorem body_readG (E : Nat → GSet.{u}) (h : evalG B.body E) :
    ¬¬∃ A r, Equiv (E 1) (opair A r) ∧ IsOrd (E 2) ∧ TypedG (E 0) (E 2) A ∧ TotalG (E 0) (E 2) A ∧
      OrderG (E 0) r (E 2) A := by
  refine nn_bind h fun ⟨S, _, hA⟩ => nn_bind hA fun ⟨A, _, hT⟩ =>
    nn_bind hT fun ⟨T, _, hr⟩ => nn_map (fun ⟨r, _, hh⟩ => ?_) hr
  exact ⟨A, r, (pair_readG (Env.cons r (Env.cons T (Env.cons A (Env.cons S E)))) 5 2 0).1 hh.1,
    (ordinal_readG (Env.cons r (Env.cons T (Env.cons A (Env.cons S E)))) 6).1 hh.2.1,
    typed_readG (Env.cons r (Env.cons T (Env.cons A (Env.cons S E)))) 4 6 2 hh.2.2.1.1,
    total_readG (Env.cons r (Env.cons T (Env.cons A (Env.cons S E)))) 4 6 2 hh.2.2.1.2.1,
    order_readG (Env.cons r (Env.cons T (Env.cons A (Env.cons S E)))) 4 0 6 2 hh.2.2.2.2.2⟩

/-! ### The decoder adapter -/

/-- The graph reading of the literal decoder: `d` decodes to `α`. -/
def GDec (d α : GSet.{u}) (e : Nat → GSet.{u}) : Prop :=
  Sat (fun _ => True) decodeF (Env.cons d (Env.cons α e))

theorem gdec_read (d α : GSet.{u}) (e : Nat → GSet.{u}) :
    GDec d α e ↔ ¬¬∃ f, evalG B.body (Env.cons f (Env.cons d (Env.cons α e))) :=
  sat_ex.trans (nn_congr ⟨fun ⟨f, _, h⟩ => ⟨f, (evalG_read _ _).1 h⟩,
    fun ⟨f, h⟩ => ⟨f, trivial, (evalG_read _ _).2 h⟩⟩)

/-- `⋃⋃⋃a`. -/
def base3 (a : GSet.{u}) : GSet.{u} := sUnion (sUnion (sUnion a))

theorem mem_base3 {a d A r v : GSet.{u}} (hd : Mem d a) (ed : Equiv d (opair A r)) (hv : Mem v A) :
    Mem v (base3 a) := by
  have h1 : Mem (pair A r) (sUnion a) :=
    (mem_sUnion _).2 (nn_intro ⟨d, hd, Mem.congr_right ed.symm (mem_pair_right _ _)⟩)
  have h2 : Mem A (sUnion (sUnion a)) := (mem_sUnion _).2 (nn_intro ⟨pair A r, h1, mem_pair_left _ _⟩)
  exact (mem_sUnion _).2 (nn_intro ⟨A, h2, hv⟩)

/-- **The adapter**: a successful decoding of a diagram in `a` is an ordinal with an injection
relation into `⋃⋃⋃a`. -/
theorem gdec_injRel {a d α : GSet.{u}} {e : Nat → GSet.{u}} (hd : Mem d a) (h : GDec d α e) :
    IsOrd α ∧ InjRel α (base3 a) := by
  refine Stable.of_nn ((gdec_read d α e).1 h) fun ⟨f, hb⟩ => ?_
  refine Stable.of_nn (body_readG _ hb) fun ⟨A, r, ed, hα, ht, hto, ho⟩ => ?_
  refine ⟨hα, nn_intro ⟨fun ξ i => Mem (opair ξ ((base3 a).at' i)) f, ⟨fun _ _ => inferInstance,
    fun e' h => Mem.congr_left (opair_congr _ _ e' (Equiv.refl _)) h,
    fun e' h => Mem.congr_left (opair_congr _ _ (Equiv.refl _) e') h, ?_, ?_⟩⟩⟩
  · intro ξ hξ
    refine nn_bind (hto ξ hξ) fun ⟨v, hv, hf⟩ => ?_
    exact nn_map (fun ⟨i, hi, ev⟩ => ⟨i, hi, Mem.congr_left (opair_congr _ _ (Equiv.refl _) ev) hf⟩)
      (mem_base3 hd ed hv)
  · intro ξ ξ' i hξ hξ' h1 h2
    have hu : Mem ((base3 a).at' i) A := (edge_typed ht h1).2
    have noij : ¬ Mem ξ ξ' := fun hm => not_mem_self ξ
      ((ho ξ ξ _ _ hξ hξ hu hu h1 h1).1 ((ho ξ ξ' _ _ hξ hξ' hu hu h1 h2).2 hm))
    have noji : ¬ Mem ξ' ξ := fun hm => not_mem_self ξ'
      ((ho ξ' ξ' _ _ hξ' hξ' hu hu h2 h2).1 ((ho ξ' ξ _ _ hξ' hξ hu hu h2 h1).2 hm))
    exact Stable.of_nn ((hα.mem hξ).trichotomy (hα.mem hξ')) fun
      | .inl h => (noij h).elim
      | .inr (.inl e) => e
      | .inr (.inr h) => (noji h).elim

/-- Coverage: every decoded output from `a` lies in the relational Hartogs bound of `⋃⋃⋃a`. -/
theorem gdec_mem_relHartogs {a d α : GSet.{u}} {e : Nat → GSet.{u}} (hd : Mem d a) (h : GDec d α e) :
    Mem α (relHartogs (base3 a)) :=
  mem_relHartogs.2 (gdec_injRel hd h)

/-! ### The Collection instance -/

/-- The explicit collector: the Hartogs bound of the triple union, with `a` adjoined for the default. -/
def collector (a : GSet.{u}) : GSet.{u} := union (relHartogs (base3 a)) (single a)

theorem a_mem_collector (a : GSet.{u}) : Mem a (collector a) :=
  (mem_union _ _).2 (nn_intro (.inr ((mem_single _).2 (Equiv.refl _))))

theorem gdec_mem_collector {a d α : GSet.{u}} {e : Nat → GSet.{u}} (hd : Mem d a) (h : GDec d α e) :
    Mem α (collector a) :=
  (mem_union _ _).2 (nn_intro (.inl (gdec_mem_relHartogs hd h)))

theorem env_concl (y d b : GSet.{u}) (e : Nat → GSet.{u}) :
    ∀ i, Equiv (Env.cons d (Env.cons y e) i) (Env.cons y (Env.cons d (Env.cons b e)) (PSet.ZFAx.cB i)) := by
  intro i; rcases i with _ | _ | i <;> exact Equiv.refl _

theorem env_inner (d y z : GSet.{u}) (e : Nat → GSet.{u}) :
    ∀ i, Equiv (Env.cons z (Env.cons d (Env.cons y e)) (PSet.ZFAx.cB i)) (Env.cons d (Env.cons z e) i) := by
  intro i; rcases i with _ | _ | i <;> exact Equiv.refl _

/-- **The literal Collection instance for the totalized decoder is graph-valid**, its conclusion
outright: neither the premise nor decoder functionality is used. -/
theorem gvalid_coll_decodeF : GValid.{u} (PSet.ZFAx.coll (PSet.ZFAx.totalize decodeF)) := by
  intro e _
  refine sat_ex.2 (nn_intro ⟨collector (e 0), trivial, fun d _ hd => ?_⟩)
  refine sat_ex.2 fun hn => ?_
  have hall : ∀ y, ¬ GDec d y e := fun y hy => hn ⟨y, trivial, sat_and.2 ⟨gdec_mem_collector hd hy,
    (sat_rename _ PSet.ZFAx.cB _).2 (Sat.resp _ (env_concl y d _ e) fun hnd => (hnd hy).elim)⟩⟩
  refine hn ⟨e 0, trivial, sat_and.2 ⟨a_mem_collector (e 0),
    (sat_rename _ PSet.ZFAx.cB _).2 (Sat.resp _ (env_concl (e 0) d _ e) fun _ => sat_and.2 ⟨Equiv.refl _, fun hex => ?_⟩)⟩⟩
  exact sat_ex.1 hex fun ⟨z, _, hz⟩ =>
    hall z (Sat.resp decodeF (env_inner d (e 0) z e) ((sat_rename decodeF PSet.ZFAx.cB _).1 hz))

/-! ### The scoped consumer -/

/-- The base axioms with every Separation instance, plus the one decoder Collection formula. -/
inductive TDec : PSet.Fml → Prop
  | ext : TDec PSet.ZFAx.ext
  | found : TDec PSet.ZFAx.found
  | pair : TDec PSet.ZFAx.pair
  | union : TDec PSet.ZFAx.union
  | power : TDec PSet.ZFAx.power
  | inf : TDec PSet.ZFAx.inf
  | sep (ψ : PSet.Fml) : TDec (PSet.ZFAx.sep ψ)
  | coll : TDec (PSet.ZFAx.coll (PSet.ZFAx.totalize decodeF))

theorem tdec_valid : ∀ φ, TDec φ → GValid.{u} φ
  | _, .ext => ext_gvalid
  | _, .found => found_gvalid
  | _, .pair => pair_gvalid
  | _, .union => union_gvalid
  | _, .power => power_gvalid
  | _, .inf => inf_gvalid
  | _, .sep ψ => sep_gvalid ψ
  | _, .coll => gvalid_coll_decodeF

/-- **Consistency of the scoped theory.** -/
theorem con_tdec : PSet.Con TDec := Con.of_gvalid tdec_valid.{0}

/-- `TDec` is a subtheory of `ZFCollection`. -/
theorem tdec_sub : ∀ {φ}, TDec φ → PSet.ZFCollection φ
  | _, .ext => .ext
  | _, .found => .found
  | _, .pair => .pair
  | _, .union => .union
  | _, .power => .power
  | _, .inf => .inf
  | _, .sep ψ => .sep ψ
  | _, .coll => .coll _

/-- The Replacement instance for the decoder is a theorem of `TDec`, by the bridge factored through
its one Collection instance. -/
theorem prf_tdec_repl_decodeF : PSet.Prf TDec (PSet.ZFAx.repl decodeF) :=
  PSet.ZFAx.repl_of_collection_of decodeF (PSet.Prf.ax TDec.coll)

/-- info: 'GSet.Consumer.gsoundness' does not depend on any axioms -/
#guard_msgs in #print axioms gsoundness
/-- info: 'GSet.Consumer.sep_gvalid' does not depend on any axioms -/
#guard_msgs in #print axioms sep_gvalid
/-- info: 'GSet.Consumer.inf_gvalid' does not depend on any axioms -/
#guard_msgs in #print axioms inf_gvalid
/-- info: 'GSet.Consumer.evalG_read' does not depend on any axioms -/
#guard_msgs in #print axioms evalG_read
/-- info: 'GSet.Consumer.gdec_injRel' does not depend on any axioms -/
#guard_msgs in #print axioms gdec_injRel
/-- info: 'GSet.Consumer.gvalid_coll_decodeF' does not depend on any axioms -/
#guard_msgs in #print axioms gvalid_coll_decodeF
/-- info: 'GSet.Consumer.con_tdec' does not depend on any axioms -/
#guard_msgs in #print axioms con_tdec
/-- info: 'GSet.Consumer.prf_tdec_repl_decodeF' does not depend on any axioms -/
#guard_msgs in #print axioms prf_tdec_repl_decodeF

end GSet.Consumer
