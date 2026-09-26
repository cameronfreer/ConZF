import ConZF.DecodeSpectrum
import ConZF.Collection
import ConZF.NegCore
/-!
Decoder localization (con73, newcon1), ambient and native. Nothing here changes `NegCore`, adds a
forcing interpretation, or supplies a Collection realizer; the results are checked reductions.

* **Graph box.** The isomorphism graph `f` of the ordinal decoder at a diagram `d` and an ordinal
  `α` lies in `G(d, α) = 𝒫³(⋃{α, ⋃⋃d})` (`graph_mem_box`, `body_graph_bound`). The box has the
  descriptor `graphDesc` in `NegCore.Obj` with the exact readback law `graphDesc_eval`. So the
  decoder is equivalent to the bounded matrix `boxedDecode`, a genuine `BForm` whose only extra
  quantifier is bounded by the box, read in an environment that carries the box
  (`decoded_iff_boxed`). The environment adapter is explicit: `BForm` bounds are variable slots, so
  the box is placed in slot `2` and never written as a term. `Bound 2 decodeF` remains a free-variable
  bound, not a bounded-quantifier certificate.
* **Injection box.** A pure injection `κ → U` lies in `𝒫³(⋃{κ, U})` (`inj_mem_box`), and `inj0` is a
  bounded matrix with the exact `OInj` reading including functionality and purity (`inj0_read`);
  `Emb κ U` is the bounded existential `boxedEmb` over that box (`emb_iff_boxed`). Absence of a
  negatively existing ambient barrier for `U` is `∀ κ, IsOrd κ → Emb κ U` (`no_barrier_iff`), whose
  matrix `J0` is bounded once the box is supplied (`J0_read`).
* **Normalization.** The native reading of the literal `ZFAx.totalize decodeF` at `[d, y, a, …]` is
  `T a d y := (¬Decoded d y → y ≈ a) ∧ ∀ z, Decoded d z → Decoded d y` (`totalize_read`), where the
  unbounded universal is positive with a bounded antecedent; the premise of the Collection instance is
  negatively provable (`neg_total`, `sat_coll_prem`); and the instance itself reads as
  `¬¬∃ b, a ∈ b ∧ ∀ d ∈ a, ∀ α, Decoded d α → α ∈ b` (`sat_coll_decodeF`), using decoder uniqueness.
  The audit lemma `localAbsence_iff_bound` says that "absence within a candidate set implies global
  absence" is exactly "the candidate set contains every decoded output". A native `↔` is not a
  forcing equivalence and proves no source adequacy.
* **Source adapter.** Outputs decoded from any source `a` inject into `⋃⋃⋃a`
  (`emb_base_of_decoded`), so a barrier for that base bounds the decoder on `a`, with `a` adjoined
  for the default (`cplus_of_barrier`); for `diagrams U` the collecting bound is equivalent to a
  barrier for `U` (`cplus_diagrams_iff_barrier`), reusing the checked spectrum results. The existence
  of these barriers remains open.

Class discipline: everything is ambient (`M = fun _ => True`). A transitive class need not contain
the powerset boxes, so no class-relative form is claimed.
-/
universe u

namespace PSet.DecoderLocal
open OrdDecode Fml

/-! ### Binary unions as `⋃{a, b}` -/

theorem mem_sUnion_upair {a b x : PSet.{u}} : x ∈ sUnion (upair a b) ↔ ¬¬(x ∈ a ∨ x ∈ b) := by
  refine mem_sUnion.trans ⟨fun h => nn_bind h fun ⟨y, hy, hx⟩ => ?_, nn_map fun h => ?_⟩
  · exact nn_map (fun
      | .inl e => .inl ((mem_congr_right e).1 hx)
      | .inr e => .inr ((mem_congr_right e).1 hx)) (mem_upair.1 hy)
  · rcases h with h | h
    · exact ⟨a, mem_upair_left _ _, h⟩
    · exact ⟨b, mem_upair_right _ _, h⟩

/-! ### The graph box -/

/-- `𝒫³(⋃{α, ⋃⋃d})`. -/
def graphBox (d α : PSet.{u}) : PSet.{u} :=
  powerset (powerset (powerset (sUnion (upair α (sUnion (sUnion d))))))

/-- The box as a descriptor, in an environment `[d, α, …]`. -/
def graphDesc : NegCore.Obj :=
  .pow (.pow (.pow (.sUnion (.upair (.var 1) (.sUnion (.sUnion (.var 0)))))))

theorem graphDesc_eval (e : NegCore.Env.{u}) : NegCore.Obj.eval graphDesc e = graphBox (e 0) (e 1) := rfl

/-- An ordered surjection onto the diagram `d ≈ ⟨A, r⟩` has its graph in the box. -/
theorem graph_mem_box {d A r α f : PSet.{u}} (ed : d ≈ pair A r) (hf : OrderedSurjection r A α f) :
    f ∈ graphBox d α := by
  refine mem_powerset.2 fun q hq => ?_
  refine Stable.of_nn (hf.map.1 q hq) fun ⟨i, v, hi, hv, e⟩ => ?_
  have hA : A ∈ sUnion d := mem_sUnion.2 (nn_intro
    ⟨upair A r, (mem_congr_right ed).2 (mem_upair_right _ _), mem_upair_left _ _⟩)
  have hv' : v ∈ sUnion (sUnion d) := mem_sUnion.2 (nn_intro ⟨A, hA, hv⟩)
  exact (mem_congr_left e).2 (pair_mem_powerset_powerset
    (mem_sUnion_upair.2 (nn_intro (.inl hi))) (mem_sUnion_upair.2 (nn_intro (.inr hv'))))

/-- The matrix at `[f, d, α, …]` puts `f` in the box. -/
theorem body_graph_bound (E : Nat → PSet.{u}) (h : B.body.eval E) : E 0 ∈ graphBox (E 1) (E 2) :=
  Stable.of_nn ((body_read E).1 h) fun ⟨_, _, ed, _, hf⟩ => graph_mem_box ed hf

/-- The decoder as a bounded matrix in the environment `[d, α, G, …]`: the graph is bounded by the
slot `2`, which the adapter fills with the box. -/
def boxedDecode : BForm := .exIn 2 B.body

set_option maxRecDepth 200000 in
theorem boxedDecode_scoped : BForm.Scoped 3 boxedDecode := by decide

theorem boxedDecode_read (d α G : PSet.{u}) (e : Nat → PSet.{u}) :
    boxedDecode.eval (Env.cons d (Env.cons α (Env.cons G e))) ↔
      ¬¬∃ f, f ∈ G ∧ B.body.eval (Env.cons f (Env.cons d (Env.cons α (Env.cons G e)))) := Iff.rfl

/-- **Localization**: the ambient decoder is the bounded matrix with the box supplied. -/
theorem decoded_iff_boxed (d α : PSet.{u}) (e : Nat → PSet.{u}) :
    Decoded d α ↔ boxedDecode.eval (Env.cons d (Env.cons α (Env.cons (graphBox d α) e))) := by
  constructor
  · intro h
    exact nn_map (fun ⟨A, r, f, ed, hf⟩ =>
      ⟨f, graph_mem_box ed hf, (body_read _).2 (nn_intro ⟨A, r, ed, h.1, hf⟩)⟩) h.2
  · intro h
    refine Stable.of_nn h fun ⟨f, _, hb⟩ => Stable.of_nn ((body_read _).1 hb) fun ⟨A, r, ed, ha, hf⟩ => ?_
    exact ⟨ha, nn_intro ⟨A, r, f, ed, hf⟩⟩

theorem decodedIn_true {d α : PSet.{u}} : DecodedIn (fun _ => True) d α ↔ Decoded d α :=
  ⟨DecodedIn.forget, fun h => ⟨h.1, nn_map (fun ⟨A, r, f, e, hf⟩ =>
    ⟨A, r, f, trivial, trivial, trivial, e, hf⟩) h.2⟩⟩

/-- Ambient satisfaction of the literal decoder. -/
theorem sat_decodeF_true (d α : PSet.{u}) (e : Nat → PSet.{u}) :
    Sat (fun _ => True) decodeF (Env.cons d (Env.cons α e)) ↔ Decoded d α :=
  (decode_read (fun _ _ => trivial) _ (fun _ => trivial)).trans decodedIn_true

/-- The compiled bounded matrix, satisfied ambiently, is the decoder. -/
theorem sat_boxedDecode (d α : PSet.{u}) (e : Nat → PSet.{u}) :
    Sat (fun _ => True) boxedDecode.compile (Env.cons d (Env.cons α (Env.cons (graphBox d α) e))) ↔
      Decoded d α :=
  (BForm.all_read _ _).trans (decoded_iff_boxed d α e).symm

/-! ### The injection box -/

/-- `𝒫³(⋃{κ, U})`. -/
def injBox (κ U : PSet.{u}) : PSet.{u} := powerset (powerset (powerset (sUnion (upair κ U))))

/-- The box as a descriptor, in an environment `[κ, U, …]`. -/
def injDesc : NegCore.Obj := .pow (.pow (.pow (.sUnion (.upair (.var 0) (.var 1)))))

theorem injDesc_eval (e : NegCore.Env.{u}) : NegCore.Obj.eval injDesc e = injBox (e 0) (e 1) := rfl

theorem inj_mem_box {f κ U : PSet.{u}} (h : OInj f κ U) : f ∈ injBox κ U := by
  refine mem_powerset.2 fun q hq => ?_
  refine Stable.of_nn (h.1.1 q hq) fun ⟨i, v, hi, hv, e⟩ => ?_
  exact (mem_congr_left e).2 (pair_mem_powerset_powerset
    (mem_sUnion_upair.2 (nn_intro (.inl hi))) (mem_sUnion_upair.2 (nn_intro (.inr hv))))

/-- A bounded pure-injection matrix: a pure map `κ → U` with bounded inverse uniqueness. -/
def inj0 (f κ U : Nat) : BForm :=
  .conj (B.map f κ U)
    (.allIn κ (.allIn (κ+1) (.allIn (U+2)
      (.imp (B.edge (f+3) 2 0) (.imp (B.edge (f+3) 1 0) (.eq 2 1))))))

/-- Exact reading, including functionality and purity through `map_read`. -/
theorem inj0_read (E : Nat → PSet.{u}) (f κ U : Nat) : (inj0 f κ U).eval E ↔ OInj (E f) (E κ) (E U) := by
  constructor
  · intro h
    have hm := (map_read E f κ U).1 h.1
    refine ⟨hm, fun i j v w hiv hjw evw => ?_⟩
    have hjv : pair j v ∈ E f := (mem_congr_left (pair_congr (Equiv.refl j) evw.symm)).1 hjw
    exact h.2 i (map_edge_typed hm hiv).1 j (map_edge_typed hm hjw).1 v (map_edge_typed hm hiv).2
      ((edge_read _ (f+3) 2 0).2 hiv) ((edge_read _ (f+3) 1 0).2 hjv)
  · intro h
    exact ⟨(map_read E f κ U).2 h.1, fun i _ j _ v _ h1 h2 =>
      h.2 i j v v ((edge_read _ (f+3) 2 0).1 h1) ((edge_read _ (f+3) 1 0).1 h2) (Equiv.refl v)⟩

/-- `Emb κ U` as a bounded existential in the environment `[κ, U, G, …]`. -/
def boxedEmb : BForm := .exIn 2 (inj0 0 1 2)

theorem boxedEmb_scoped : BForm.Scoped 3 boxedEmb := by decide

theorem emb_iff_boxed (κ U : PSet.{u}) (e : Nat → PSet.{u}) :
    Emb κ U ↔ boxedEmb.eval (Env.cons κ (Env.cons U (Env.cons (injBox κ U) e))) :=
  ⟨nn_map fun ⟨f, hf⟩ => ⟨f, inj_mem_box hf, (inj0_read _ 0 1 2).2 hf⟩,
   nn_map fun ⟨f, _, hf⟩ => ⟨f, (inj0_read _ 0 1 2).1 hf⟩⟩

/-- The bounded no-barrier matrix `Ord κ → Emb κ U` in the environment `[κ, U, G, …]`. -/
def J0 : BForm := .imp (B.ordinal 0) boxedEmb

theorem J0_read (κ U : PSet.{u}) (e : Nat → PSet.{u}) :
    J0.eval (Env.cons κ (Env.cons U (Env.cons (injBox κ U) e))) ↔ (IsOrd κ → Emb κ U) :=
  imp_congr (ordinal_read _ 0) (emb_iff_boxed κ U e).symm

/-- Absence of a negatively existing ambient barrier is the universal bounded condition. -/
theorem no_barrier_iff (U : PSet.{u}) :
    ¬(¬¬∃ k, Barrier (fun _ => True) U k) ↔ ∀ κ, IsOrd κ → Emb κ U := by
  constructor
  · intro h κ hκ hn
    exact h (nn_intro ⟨κ, hκ, fun f _ hf => hn ⟨f, hf⟩⟩)
  · intro h hb
    exact hb fun ⟨k, hk⟩ => h k hk.1 fun ⟨f, hf⟩ => hk.2 f trivial hf

/-! ### Normalization of the totalized decoder -/

/-- The normalized totalization: `(¬D(d,y) → y ≈ a) ∧ ∀ z (D(d,z) → D(d,y))`. -/
def T (a d y : PSet.{u}) : Prop := (¬Decoded d y → y ≈ a) ∧ ∀ z, Decoded d z → Decoded d y

/-- `a ∈ b` and `b` contains every decoded output from `a`. -/
def CPlus (a b : PSet.{u}) : Prop := a ∈ b ∧ ∀ d, d ∈ a → ∀ α, Decoded d α → α ∈ b

def BoundD (a b : PSet.{u}) : Prop := ∀ d, d ∈ a → ∀ α, Decoded d α → α ∈ b

/-- Absence of decoded outputs within `b` implies global absence. -/
def LocalAbsence (a b : PSet.{u}) : Prop :=
  ∀ d, d ∈ a → (∀ z, z ∈ b → ¬Decoded d z) → ∀ z, ¬Decoded d z

theorem T_of_decoded {a d z : PSet.{u}} (hz : Decoded d z) : T a d z :=
  ⟨fun hn => (hn hz).elim, fun _ _ => hz⟩

/-- Negative totality, with the default `a`. -/
theorem neg_total (a d : PSet.{u}) : ¬¬∃ y, T a d y := fun hn =>
  hn ⟨a, fun _ => Equiv.refl a, fun z hz => (hn ⟨z, T_of_decoded hz⟩).elim⟩

theorem env_cB (d y a : PSet.{u}) (e : Nat → PSet.{u}) (z : PSet.{u}) :
    ∀ i, Env.cons z (Env.cons d (Env.cons y (Env.cons a e))) (ZFAx.cB i) ≈
      Env.cons d (Env.cons z (Env.cons a e)) i := by
  intro i; rcases i with _ | _ | i <;> exact Equiv.refl _

/-- **Normalization**: the native reading of the literal totalization at `[d, y, a, …]`. -/
theorem totalize_read (d y a : PSet.{u}) (e : Nat → PSet.{u}) :
    Sat (fun _ => True) (ZFAx.totalize decodeF) (Env.cons d (Env.cons y (Env.cons a e))) ↔ T a d y := by
  have hψ := sat_decodeF_true d y (Env.cons a e)
  have hex : Sat (fun _ => True) (Fml.ex (Fml.rename ZFAx.cB decodeF))
      (Env.cons d (Env.cons y (Env.cons a e))) ↔ ¬¬∃ z, Decoded d z := by
    refine sat_ex.trans (nn_congr ⟨fun ⟨z, _, hz⟩ => ⟨z, ?_⟩, fun ⟨z, hz⟩ => ⟨z, trivial, ?_⟩⟩)
    · exact (sat_decodeF_true d z _).1 ((Sat.resp_iff (fun _ => Iff.rfl) decodeF (env_cB d y a e z)).1
        ((sat_rename decodeF ZFAx.cB _).1 hz))
    · exact (sat_rename decodeF ZFAx.cB _).2 ((Sat.resp_iff (fun _ => Iff.rfl) decodeF (env_cB d y a e z)).2
        ((sat_decodeF_true d z _).2 hz))
  show (¬ Sat (fun _ => True) decodeF _ → Sat (fun _ => True)
    (Fml.and (Fml.eq 1 2) (Fml.neg (Fml.ex (Fml.rename ZFAx.cB decodeF)))) _) ↔ _
  constructor
  · intro h
    refine ⟨fun hn => (sat_and.1 (h fun hd => hn (hψ.1 hd))).1, fun z hz => ?_⟩
    exact Stable.dne fun hn => (sat_and.1 (h fun hd => hn (hψ.1 hd))).2 (hex.2 (nn_intro ⟨z, hz⟩))
  · intro h hn
    refine sat_and.2 ⟨h.1 fun hd => hn (hψ.2 hd), fun hx => hn (hψ.2 ?_)⟩
    exact Stable.dne fun hnd => hex.1 hx fun ⟨z, hz⟩ => hnd (h.2 z hz)

theorem env_cA (d y a : PSet.{u}) (e : Nat → PSet.{u}) :
    ∀ i, Env.cons y (Env.cons d (Env.cons a e)) (ZFAx.cA i) ≈ Env.cons d (Env.cons y (Env.cons a e)) i := by
  intro i; rcases i with _ | _ | i <;> exact Equiv.refl _

/-- The premise of the Collection instance holds ambiently at any `a`. -/
theorem sat_coll_prem (a : PSet.{u}) (e : Nat → PSet.{u}) :
    Sat (fun _ => True) (all (imp (mem 0 1) (ex (rename ZFAx.cA (ZFAx.totalize decodeF))))) (Env.cons a e) := by
  intro d _ _
  refine sat_ex.2 (nn_map (fun ⟨y, hy⟩ => ⟨y, trivial, ?_⟩) (neg_total a d))
  exact (sat_rename _ ZFAx.cA _).2 ((Sat.resp_iff (fun _ => Iff.rfl) _ (env_cA d y a e)).2
    ((totalize_read d y a e).2 hy))

theorem env_cB' (d y b a : PSet.{u}) (e : Nat → PSet.{u}) :
    ∀ i, Env.cons y (Env.cons d (Env.cons b (Env.cons a e))) (ZFAx.cB i) ≈
      Env.cons d (Env.cons y (Env.cons a e)) i := by
  intro i; rcases i with _ | _ | i <;> exact Equiv.refl _

theorem inner_read (a b d : PSet.{u}) (e : Nat → PSet.{u}) :
    Sat (fun _ => True) (ex (and (mem 0 2) (rename ZFAx.cB (ZFAx.totalize decodeF))))
      (Env.cons d (Env.cons b (Env.cons a e))) ↔ ¬¬∃ y, y ∈ b ∧ T a d y :=
  sat_ex.trans (nn_congr
    ⟨fun ⟨y, _, h⟩ => ⟨y, (sat_and.1 h).1, (totalize_read d y a e).1
        ((Sat.resp_iff (fun _ => Iff.rfl) _ (env_cB' d y b a e)).1 ((sat_rename _ ZFAx.cB _).1 (sat_and.1 h).2))⟩,
     fun ⟨y, hy, hT⟩ => ⟨y, trivial, sat_and.2 ⟨hy, (sat_rename _ ZFAx.cB _).2
        ((Sat.resp_iff (fun _ => Iff.rfl) _ (env_cB' d y b a e)).2 ((totalize_read d y a e).2 hT))⟩⟩⟩)

/-- The conclusion of the Collection instance, read natively. -/
theorem sat_coll_concl (a : PSet.{u}) (e : Nat → PSet.{u}) :
    Sat (fun _ => True) (ex (all (imp (mem 0 2) (ex (and (mem 0 2) (rename ZFAx.cB (ZFAx.totalize decodeF)))))))
      (Env.cons a e) ↔ ¬¬∃ b : PSet.{u}, ∀ d, d ∈ a → ¬¬∃ y, y ∈ b ∧ T a d y :=
  sat_ex.trans (nn_congr
    ⟨fun ⟨b, _, hb⟩ => ⟨b, fun d hd => (inner_read a b d e).1 (hb d trivial hd)⟩,
     fun ⟨b, hb⟩ => ⟨b, trivial, fun d _ hd => (inner_read a b d e).2 (hb d hd)⟩⟩)

/-- At the negative-existence level, the totalized conclusion is a collecting bound with `a` adjoined,
by decoder uniqueness. -/
theorem collConcl_iff_cplus (a : PSet.{u}) :
    (¬¬∃ b : PSet.{u}, ∀ d, d ∈ a → ¬¬∃ y, y ∈ b ∧ T a d y) ↔ ¬¬∃ b, CPlus a b := by
  constructor
  · refine nn_map fun ⟨b, hb⟩ => ⟨union b (singleton a),
      mem_union.2 (nn_intro (.inr (self_mem_singleton a))), fun d hd α hα => ?_⟩
    refine Stable.of_nn (hb d hd) fun ⟨y, hy, hT⟩ => ?_
    exact mem_union.2 (nn_intro (.inl ((mem_congr_left (decoded_unique (hT.2 α hα) hα)).1 hy)))
  · refine nn_map fun ⟨b, hab, hb⟩ => ⟨b, fun d hd hn => ?_⟩
    exact hn ⟨a, hab, fun _ => Equiv.refl a, fun z hz => (hn ⟨z, hb d hd z hz, T_of_decoded hz⟩).elim⟩

/-- **The exact native content of the Collection instance used by the bridge**: at `[a, …]`, the
literal `ZFAx.coll (ZFAx.totalize decodeF)` holds iff some set contains `a` and every decoded output
from `a`. -/
theorem sat_coll_decodeF (a : PSet.{u}) (e : Nat → PSet.{u}) :
    Sat (fun _ => True) (ZFAx.coll (ZFAx.totalize decodeF)) (Env.cons a e) ↔ ¬¬∃ b, CPlus a b :=
  ⟨fun h => (collConcl_iff_cplus a).1 ((sat_coll_concl a e).1 (h (sat_coll_prem a e))),
   fun h _ => (sat_coll_concl a e).2 ((collConcl_iff_cplus a).2 h)⟩

/-- **The audit lemma**: local absence within `b` is exactly coverage of all decoded outputs. -/
theorem localAbsence_iff_bound (a b : PSet.{u}) : LocalAbsence a b ↔ BoundD a b := by
  constructor
  · intro h d hd α hα
    exact Stable.dne fun hn => h d hd
      (fun z hz hz' => hn ((mem_congr_left (decoded_unique hz' hα)).1 hz)) α hα
  · intro h d hd hb z hz
    exact hb z (h d hd z hz) hz

/-! ### Arbitrary sources reduce to barriers for their bases -/

/-- `⋃⋃⋃a`: contains every element of every domain of every diagram in `a`. -/
def base (a : PSet.{u}) : PSet.{u} := sUnion (sUnion (sUnion a))

theorem emb_base_of_decoded {a d α : PSet.{u}} (hd : d ∈ a) (h : Decoded d α) : Emb α (base a) := by
  refine nn_map (fun ⟨A, r, f, ed, hf⟩ => ⟨f, OInj.mono (fun v hv => ?_) ⟨hf.map, hf.injective h.1⟩⟩) h.2
  have h1 : upair A r ∈ sUnion a := mem_sUnion.2 (nn_intro ⟨d, hd, (mem_congr_right ed).2 (mem_upair_right _ _)⟩)
  have h2 : A ∈ sUnion (sUnion a) := mem_sUnion.2 (nn_intro ⟨upair A r, h1, mem_upair_left _ _⟩)
  exact mem_sUnion.2 (nn_intro ⟨A, h2, hv⟩)

theorem source_bound_of_barrier {a k d α : PSet.{u}} (hk : Barrier (fun _ => True) (base a) k)
    (hd : d ∈ a) (h : Decoded d α) : α ∈ k :=
  injected_lt_barrier hk h.1 (emb_base_of_decoded hd h)

/-- A barrier for the base gives the collecting bound of the Collection instance, `a` adjoined. -/
theorem cplus_of_barrier {a k : PSet.{u}} (hk : Barrier (fun _ => True) (base a) k) :
    CPlus a (union k (singleton a)) :=
  ⟨mem_union.2 (nn_intro (.inr (self_mem_singleton a))),
   fun _ hd _ h => mem_union.2 (nn_intro (.inl (source_bound_of_barrier hk hd h)))⟩

theorem sat_coll_decodeF_of_barrier {a : PSet.{u}} (e : Nat → PSet.{u})
    (h : ¬¬∃ k, Barrier (fun _ => True) (base a) k) :
    Sat (fun _ => True) (ZFAx.coll (ZFAx.totalize decodeF)) (Env.cons a e) :=
  (sat_coll_decodeF a e).2 (nn_map (fun ⟨_, hk⟩ => ⟨_, cplus_of_barrier hk⟩) h)

/-- For the diagram source, the collecting bound is exactly a barrier for `U`. -/
theorem cplus_diagrams_iff_barrier (U : PSet.{u}) :
    (¬¬∃ b, CPlus (diagrams U) b) ↔ ¬¬∃ k, Barrier (fun _ => True) U k :=
  ⟨nn_map fun ⟨b, _, hb⟩ => ⟨rank b, collecting_set_barrier U b fun d α hd h => hb d hd α h⟩,
   nn_map fun ⟨k, hk⟩ => ⟨union k (singleton (diagrams U)),
     mem_union.2 (nn_intro (.inr (self_mem_singleton _))),
     fun _ hd _ h => mem_union.2 (nn_intro (.inl (injected_lt_barrier hk h.1 (emb_of_decoded hd h))))⟩⟩

/-- info: 'PSet.DecoderLocal.graph_mem_box' does not depend on any axioms -/
#guard_msgs in #print axioms graph_mem_box
/-- info: 'PSet.DecoderLocal.decoded_iff_boxed' does not depend on any axioms -/
#guard_msgs in #print axioms decoded_iff_boxed
/-- info: 'PSet.DecoderLocal.sat_boxedDecode' does not depend on any axioms -/
#guard_msgs in #print axioms sat_boxedDecode
/-- info: 'PSet.DecoderLocal.inj0_read' does not depend on any axioms -/
#guard_msgs in #print axioms inj0_read
/-- info: 'PSet.DecoderLocal.emb_iff_boxed' does not depend on any axioms -/
#guard_msgs in #print axioms emb_iff_boxed
/-- info: 'PSet.DecoderLocal.J0_read' does not depend on any axioms -/
#guard_msgs in #print axioms J0_read
/-- info: 'PSet.DecoderLocal.no_barrier_iff' does not depend on any axioms -/
#guard_msgs in #print axioms no_barrier_iff
/-- info: 'PSet.DecoderLocal.totalize_read' does not depend on any axioms -/
#guard_msgs in #print axioms totalize_read
/-- info: 'PSet.DecoderLocal.sat_coll_decodeF' does not depend on any axioms -/
#guard_msgs in #print axioms sat_coll_decodeF
/-- info: 'PSet.DecoderLocal.localAbsence_iff_bound' does not depend on any axioms -/
#guard_msgs in #print axioms localAbsence_iff_bound
/-- info: 'PSet.DecoderLocal.sat_coll_decodeF_of_barrier' does not depend on any axioms -/
#guard_msgs in #print axioms sat_coll_decodeF_of_barrier
/-- info: 'PSet.DecoderLocal.cplus_diagrams_iff_barrier' does not depend on any axioms -/
#guard_msgs in #print axioms cplus_diagrams_iff_barrier

end PSet.DecoderLocal
