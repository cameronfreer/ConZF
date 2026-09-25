import ConZF.OrdDecode
import ConZF.CofinalCut
/-!
The exact spectrum of the decoder and the barrier equivalence, **for this one formula**.

* `decoded_spectrum`: over any base `U`, the ordinals decoded from some diagram in `diagrams U`
  are exactly the ordinals with a pure injection into `U` (`Emb`). From an injection `f : a → U`
  the diagram is `⟨active U f, orderGraph U f⟩`, both by Separation inside supplied sets, and
  the *same* `f` is the isomorphism; conversely an isomorphism onto a diagram over `U` is an
  injection into `U`. Restricting an injection to a smaller ordinal is Separation in `b × U`.
* `Barrier M U k`: `k` is an ordinal and no `f` in `M` is a pure injection `k → U`. For the
  ambient class a barrier is exactly a strict cap on the decoded spectrum
  (`barrier_iff_cap`), and its negative existence is exactly the existence of an exact
  collecting set for the decoder (`barrier_iff_exact_image`).
* Over `HG` (a base `U` in `HG`): the reading of `decodeF` in `HG` is `DecodedIn HG`
  (`sat_decodeF_HG`), the `HG` output spectrum is exactly `CanInject HG`
  (`hg_spectrum_exact`), and the instancewise rank-bound obligation of the model's
  Replacement clause for this formula is exactly negative existence of an `HG`-relative barrier
  (`barrier_iff_rankBounded`). This is a reduction, not a producer of the barrier.

Nothing here assumes Replacement, a model, or accessibility; `HG` is used only through its
closure under subsets, unions, powersets and pairs, all proved before its model theorem.
-/
universe u

namespace PSet.OrdDecode

/-! ### Pure injections -/

/-- A pure injection `f : a → U`: a pure function with inverse uniqueness. Both forward
functionality and inverse uniqueness are required. -/
def OInj (f a U : PSet.{u}) : Prop :=
  IsPureFun U f a ∧ ∀ i j v w, pair i v ∈ f → pair j w ∈ f → v ≈ w → i ≈ j

instance {f a U : PSet.{u}} : Stable (OInj f a U) := inferInstanceAs (Stable (_ ∧ _))

theorem OInj.mono {f a U U' : PSet.{u}} (sub : ∀ z, z ∈ U → z ∈ U') (h : OInj f a U) :
    OInj f a U' :=
  ⟨⟨fun q hq => nn_map (fun ⟨i, v, hi, hv, e⟩ => ⟨i, v, hi, sub v hv, e⟩) (h.1.1 q hq),
    h.1.2.1, h.1.2.2⟩, h.2⟩

theorem OInj.congr_dom {f a a' U : PSet.{u}} (e : a ≈ a') (h : OInj f a U) : OInj f a' U :=
  ⟨⟨fun q hq => nn_map (fun ⟨i, v, hi, hv, e'⟩ => ⟨i, v, (mem_congr_right e).1 hi, hv, e'⟩)
      (h.1.1 q hq),
    fun i hi => h.1.2.1 i ((mem_congr_right e).2 hi), h.1.2.2⟩, h.2⟩

/-- Negative existence of a pure injection `a → U`. -/
def Emb (a U : PSet.{u}) : Prop := ¬¬∃ f, OInj f a U

instance {a U : PSet.{u}} : Stable (Emb a U) := inferInstanceAs (Stable (¬ _))

theorem Emb.congr {a a' U : PSet.{u}} (e : a ≈ a') (h : Emb a U) : Emb a' U :=
  nn_map (fun ⟨f, hf⟩ => ⟨f, hf.congr_dom e⟩) h

/-- The restriction of `f` to `b`, by Separation in `b × U`. -/
def restricted (f b U : PSet.{u}) : PSet.{u} := sep (fun q => q ∈ f) (product b U)

theorem mem_restricted {f b U q : PSet.{u}} : q ∈ restricted f b U ↔ q ∈ product b U ∧ q ∈ f :=
  mem_sep fun _ _ e h => (mem_congr_left e).1 h

theorem restrict_inj {f a b U : PSet.{u}} (h : OInj f a U) (sub : ∀ z, z ∈ b → z ∈ a) :
    OInj (restricted f b U) b U := by
  refine ⟨⟨fun q hq => mem_product.1 (mem_restricted.1 hq).1, fun i hi => ?_,
    fun i v w hiv hiw => h.1.2.2 i v w (mem_restricted.1 hiv).2 (mem_restricted.1 hiw).2⟩,
    fun i j v w hiv hjw evw => h.2 i j v w (mem_restricted.1 hiv).2 (mem_restricted.1 hjw).2 evw⟩
  refine nn_map (fun ⟨v, hv⟩ => ?_) (h.1.2.1 i (sub i hi))
  exact ⟨v, mem_restricted.2 ⟨mem_product.2 (nn_intro
    ⟨i, v, hi, (map_edge_typed h.1 hv).2, Equiv.refl _⟩), hv⟩⟩

theorem Emb.down {a b U : PSet.{u}} (ha : IsOrd a) (hb : b ∈ a) (h : Emb a U) : Emb b U :=
  nn_map (fun ⟨f, hf⟩ => ⟨restricted f b U, restrict_inj hf fun z hz => ha.trans b hb z hz⟩) h

theorem Emb.le {a b U : PSet.{u}} (ha : IsOrd a) (hb : b ∈ succ a) (h : Emb a U) : Emb b U :=
  Stable.of_nn (mem_succ.1 hb) fun
    | .inl hb => Emb.down ha hb h
    | .inr e => Emb.congr e.symm h

/-! ### The diagram of an injection -/

/-- The active range of `f` inside `U`. -/
def active (U f : PSet.{u}) : PSet.{u} := sep (fun v => ¬¬∃ i, pair i v ∈ f) U

/-- The order transported along `f`, inside `U × U`. -/
def orderGraph (U f : PSet.{u}) : PSet.{u} :=
  sep (fun q => ¬¬∃ i j v w, pair i v ∈ f ∧ pair j w ∈ f ∧ i ∈ j ∧ q ≈ pair v w) (product U U)

theorem mem_active {U f v : PSet.{u}} : v ∈ active U f ↔ v ∈ U ∧ ¬¬∃ i, pair i v ∈ f :=
  mem_sep fun _ _ e h => nn_map (fun ⟨i, hi⟩ =>
    ⟨i, (mem_congr_left (pair_congr (Equiv.refl _) e)).1 hi⟩) h

theorem mem_orderGraph {U f q : PSet.{u}} : q ∈ orderGraph U f ↔ q ∈ product U U ∧
    ¬¬∃ i j v w, pair i v ∈ f ∧ pair j w ∈ f ∧ i ∈ j ∧ q ≈ pair v w :=
  mem_sep fun _ _ e h => nn_map (fun ⟨i, j, v, w, hi, hj, hij, eq⟩ =>
    ⟨i, j, v, w, hi, hj, hij, e.symm.trans eq⟩) h

/-- The injection itself is an ordered surjection onto its diagram. -/
theorem ordered_injection {f a U : PSet.{u}} (h : OInj f a U) :
    OrderedSurjection (orderGraph U f) (active U f) a f := by
  have hm : IsPureFun (active U f) f a :=
    ⟨fun q hq => nn_map (fun ⟨i, v, hi, hv, e⟩ =>
      ⟨i, v, hi, mem_active.2 ⟨hv, nn_intro ⟨i, (mem_congr_left e).1 hq⟩⟩, e⟩) (h.1.1 q hq),
     h.1.2.1, h.1.2.2⟩
  refine ⟨hm, fun v hv => (mem_active.1 hv).2, fun q hq => ?_, fun i j v w hi hj => ⟨?_, ?_⟩⟩
  · exact nn_map (fun ⟨_, _, v, w, hi, hj, _, e⟩ =>
      ⟨v, w, (map_edge_typed hm hi).2, (map_edge_typed hm hj).2, e⟩) (mem_orderGraph.1 hq).2
  · intro he
    refine Stable.of_nn (mem_orderGraph.1 he).2 fun ⟨i', j', v', w', hi', hj', hij, e⟩ => ?_
    have ei := h.2 i i' v v' hi hi' (pair_inj e).1
    have ej := h.2 j j' w w' hj hj' (pair_inj e).2
    exact (mem_congr_right ej).2 ((mem_congr_left ei).2 hij)
  · intro hij
    exact mem_orderGraph.2 ⟨mem_product.2 (nn_intro
      ⟨v, w, (map_edge_typed h.1 hi).2, (map_edge_typed h.1 hj).2, Equiv.refl _⟩),
      nn_intro ⟨i, j, v, w, hi, hj, hij, Equiv.refl _⟩⟩

theorem diagram_of_emb {a U : PSet.{u}} (ha : IsOrd a) (h : Emb a U) :
    ¬¬∃ d, d ∈ diagrams U ∧ Decoded d a :=
  nn_map (fun ⟨f, hf⟩ => ⟨pair (active U f) (orderGraph U f), mem_product.2 (nn_intro
    ⟨active U f, orderGraph U f, mem_powerset.2 fun _ hv => (mem_active.1 hv).1,
      mem_powerset.2 fun _ hq => (mem_orderGraph.1 hq).1, Equiv.refl _⟩),
    ha, nn_intro ⟨active U f, orderGraph U f, f, Equiv.refl _, ordered_injection hf⟩⟩) h

theorem emb_of_decoded {U d a : PSet.{u}} (hd : d ∈ diagrams U) (h : Decoded d a) : Emb a U := by
  refine Stable.of_nn (mem_product.1 hd) fun ⟨A, _, hA, _, e⟩ =>
    nn_map (fun ⟨A', _, f, e', hf⟩ => ?_) h.2
  have eA := (pair_inj (e.symm.trans e')).1
  exact ⟨f, ⟨⟨fun q hq => nn_map (fun ⟨i, v, hi, hv, eq⟩ =>
      ⟨i, v, hi, mem_powerset.1 hA v ((mem_congr_right eA).2 hv), eq⟩) (hf.map.1 q hq),
    hf.map.2.1, hf.map.2.2⟩, hf.injective h.1⟩⟩

/-- **The exact spectrum** of the decoder over `U`. -/
theorem decoded_spectrum (U a : PSet.{u}) :
    (¬¬∃ d, d ∈ diagrams U ∧ Decoded d a) ↔ IsOrd a ∧ Emb a U :=
  ⟨fun h => Stable.of_nn h fun ⟨_, hd, hh⟩ => ⟨hh.1, emb_of_decoded hd hh⟩,
   fun ⟨ha, hi⟩ => diagram_of_emb ha hi⟩

/-! ### Barriers -/

/-- `k` is an ordinal and no `f` in `M` is a pure injection `k → U`. Membership of `k` or `U` in
`M` is not asserted. -/
def Barrier (M : PSet.{u} → Prop) (U k : PSet.{u}) : Prop := IsOrd k ∧ ∀ f, M f → ¬ OInj f k U

instance {M : PSet.{u} → Prop} {U k : PSet.{u}} : Stable (Barrier M U k) :=
  inferInstanceAs (Stable (_ ∧ _))

/-- Negative existence of a pure injection with graph in `M`. -/
def CanInject (M : PSet.{u} → Prop) (a U : PSet.{u}) : Prop := ¬¬∃ f, M f ∧ OInj f a U

instance {M : PSet.{u} → Prop} {a U : PSet.{u}} : Stable (CanInject M a U) :=
  inferInstanceAs (Stable (¬ _))

/-- An ambient barrier is a strict bound on every embeddable ordinal. -/
theorem injected_lt_barrier {U k a : PSet.{u}} (hk : Barrier (fun _ => True) U k) (ha : IsOrd a)
    (hi : Emb a U) : a ∈ k := by
  refine Stable.of_nn (ha.trichotomy hk.1) fun
    | .inl h => h
    | .inr (.inl e) => Stable.of_nn (hi.congr e) fun ⟨f, hf⟩ => (hk.2 f trivial hf).elim
    | .inr (.inr h) => Stable.of_nn (hi.down ha h) fun ⟨f, hf⟩ => (hk.2 f trivial hf).elim

theorem barrier_iff_cap {U k : PSet.{u}} :
    Barrier (fun _ => True) U k ↔ IsOrd k ∧ ∀ a, IsOrd a → Emb a U → a ∈ k :=
  ⟨fun h => ⟨h.1, fun _ ha hi => injected_lt_barrier h ha hi⟩,
   fun ⟨hk, h⟩ => ⟨hk, fun f _ hf => not_mem_self k (h k hk (nn_intro ⟨f, hf⟩))⟩⟩

/-- A collecting set for the decoder, even with junk, gives a barrier: its rank. -/
theorem collecting_set_barrier (U B : PSet.{u})
    (hB : ∀ d a, d ∈ diagrams U → Decoded d a → a ∈ B) : Barrier (fun _ => True) U (rank B) := by
  refine ⟨isOrd_rank B, fun f _ hf => ?_⟩
  have hrB : rank B ∈ B := Stable.of_nn (diagram_of_emb (isOrd_rank B) (nn_intro ⟨f, hf⟩))
    fun ⟨d, hd, hh⟩ => hB d (rank B) hd hh
  exact not_mem_self (rank B) ((mem_congr_left (isOrd_rank B).rank_equiv).1 (rank_mem hrB))

/-- The exact spectrum below a supplied barrier, by Separation. -/
def spectrumCut (U k : PSet.{u}) : PSet.{u} := sep (fun a => IsOrd a ∧ Emb a U) k

theorem spectrumCut_exact {U k : PSet.{u}} (hk : Barrier (fun _ => True) U k) (a : PSet.{u}) :
    a ∈ spectrumCut U k ↔ ¬¬∃ d, d ∈ diagrams U ∧ Decoded d a := by
  refine (mem_sep fun _ _ e h => ⟨h.1.resp e, h.2.congr e⟩).trans ?_
  exact ⟨fun h => (decoded_spectrum U a).2 h.2, fun h =>
    have hh := (decoded_spectrum U a).1 h
    ⟨injected_lt_barrier hk hh.1 hh.2, hh⟩⟩

/-- An ambient barrier is exactly an exact collecting set for the decoder's outputs. -/
theorem barrier_iff_exact_image (U : PSet.{u}) :
    (¬¬∃ k, Barrier (fun _ => True) U k) ↔
      ¬¬∃ B : PSet.{u}, ∀ a : PSet.{u}, a ∈ B ↔ ¬¬∃ d, d ∈ diagrams U ∧ Decoded d a :=
  ⟨nn_map fun ⟨k, hk⟩ => ⟨spectrumCut U k, spectrumCut_exact hk⟩,
   nn_map fun ⟨B, hB⟩ => ⟨rank B, collecting_set_barrier U B
     fun d a hd hh => (hB a).2 (nn_intro ⟨d, hd, hh⟩)⟩⟩

/-! ### Over `HG` -/

section HG
variable [Budget.{u}]

theorem hg_subclosed {x y : PSet.{u}} (hy : HG y) (sub : ∀ z, z ∈ x → z ∈ y) : HG x :=
  HG.of_bound hy fun z hz => rank_mem (sub z hz)

theorem hg_sUnion {x : PSet.{u}} (hx : HG x) : HG (sUnion x) :=
  HG.of_bound hx fun _ hz => Stable.of_nn (mem_sUnion.1 hz) fun ⟨_, hy, hzy⟩ =>
    (isOrd_rank x).trans _ (rank_mem hy) _ (rank_mem hzy)

theorem hg_union {a b : PSet.{u}} (ha : HG a) (hb : HG b) : HG (union a b) :=
  hg_subclosed (hg_sUnion (HG.upair ha hb)) fun _ hz => mem_sUnion.2 (nn_map (fun
    | .inl h => ⟨a, mem_upair_left a b, h⟩
    | .inr h => ⟨b, mem_upair_right a b, h⟩) (mem_union.1 hz))

theorem hg_powerset {x : PSet.{u}} (hx : HG x) : HG (powerset x) :=
  HG.of_bound (Cls.succ hx) fun _ hz =>
    rank_mem_succ (isOrd_rank x) fun w hw => rank_mem (mem_powerset.1 hz w hw)

theorem hg_product {A B : PSet.{u}} (ha : HG A) (hb : HG B) : HG (product A B) := by
  refine hg_subclosed (hg_powerset (hg_powerset (hg_union ha hb))) fun q hq => ?_
  refine Stable.of_nn (mem_product.1 hq) fun ⟨a, b, ha, hb, e⟩ => (mem_congr_left e).2 ?_
  exact pair_mem_powerset_powerset (mem_union.2 (nn_intro (.inl ha)))
    (mem_union.2 (nn_intro (.inr hb)))

theorem hg_diagrams {U : PSet.{u}} (hU : HG U) : HG (diagrams U) :=
  hg_product (hg_powerset hU) (hg_powerset (hg_product hU hU))

omit [Budget.{u}] in
/-- The domain of a total pure graph is a subset of its double union. -/
theorem injection_domain_subset {f a U : PSet.{u}} (hf : OInj f a U) :
    ∀ i, i ∈ a → i ∈ sUnion (sUnion f) := fun i hi =>
  Stable.of_nn (hf.1.2.1 i hi) fun ⟨v, hv⟩ => mem_sUnion.2 (nn_intro ⟨singleton i,
    mem_sUnion.2 (nn_intro ⟨pair i v, hv, mem_upair_left _ _⟩), self_mem_singleton i⟩)

/-- The domain of an `HG` injection is `HG`: no reachability of the domain is needed. -/
theorem hg_injection_domain {f a U : PSet.{u}} (hf : HG f) (hi : OInj f a U) : HG a :=
  hg_subclosed (hg_sUnion (hg_sUnion hf)) (injection_domain_subset hi)

theorem canInject_HG_restrict {a U k : PSet.{u}} (sub : ∀ i, i ∈ k → i ∈ a)
    (h : CanInject HG a U) : CanInject HG k U :=
  nn_map (fun ⟨f, hf, hi⟩ => ⟨restricted f k U,
    hg_subclosed hf fun _ hq => (mem_restricted.1 hq).2, restrict_inj hi sub⟩) h

theorem injected_lt_HG_barrier {U k a : PSet.{u}} (hk : Barrier HG U k) (ha : IsOrd a)
    (hi : CanInject HG a U) : a ∈ k := by
  refine Stable.of_nn (ha.trichotomy hk.1) fun
    | .inl h => h
    | .inr (.inl e) => Stable.of_nn hi fun ⟨f, hf, hfi⟩ => (hk.2 f hf (hfi.congr_dom e)).elim
    | .inr (.inr h) => Stable.of_nn (canInject_HG_restrict (fun z hz => ha.trans k h z hz) hi)
        fun ⟨f, hf, hfi⟩ => (hk.2 f hf hfi).elim

omit [Budget.{u}] in
theorem decodedIn_sound {M : PSet.{u} → Prop} {U d a : PSet.{u}} (hd : d ∈ diagrams U)
    (h : DecodedIn M d a) : CanInject M a U := by
  refine Stable.of_nn (mem_product.1 hd) fun ⟨A, _, hA, _, e⟩ =>
    nn_map (fun ⟨A', _, f, _, _, hf, e', hi⟩ => ?_) h.2
  have eA := (pair_inj (e.symm.trans e')).1
  exact ⟨f, hf, ⟨⟨fun q hq => nn_map (fun ⟨i, v, hi, hv, eq⟩ =>
      ⟨i, v, hi, mem_powerset.1 hA v ((mem_congr_right eA).2 hv), eq⟩) (hi.map.1 q hq),
    hi.map.2.1, hi.map.2.2⟩, hi.injective h.1⟩⟩

/-- An `HG` injection into an `HG` base has an `HG` diagram with `HG` witnesses. -/
theorem decodedIn_complete {U a : PSet.{u}} (hU : HG U) (ha : IsOrd a) (h : CanInject HG a U) :
    ¬¬∃ d, d ∈ diagrams U ∧ HG d ∧ HG a ∧ DecodedIn HG d a := by
  refine nn_map (fun ⟨f, hf, hi⟩ => ?_) h
  have hA : HG (active U f) := hg_subclosed hU fun v hv => (mem_active.1 hv).1
  have hr : HG (orderGraph U f) := hg_subclosed (hg_product hU hU) fun q hq => (mem_orderGraph.1 hq).1
  exact ⟨pair (active U f) (orderGraph U f), mem_product.2 (nn_intro
    ⟨active U f, orderGraph U f, mem_powerset.2 fun v hv => (mem_active.1 hv).1,
      mem_powerset.2 fun q hq => (mem_orderGraph.1 hq).1, Equiv.refl _⟩),
    HG.pair hA hr, hg_injection_domain hf hi,
    ha, nn_intro ⟨active U f, orderGraph U f, f, hA, hr, hf, Equiv.refl _, ordered_injection hi⟩⟩

/-- The reading of `decodeF` in `HG`, with the unused tail arbitrary. -/
theorem sat_decodeF_HG {U d a : PSet.{u}} (hU : HG U) (hd : HG d) (ha : HG a)
    (e : Nat → PSet.{u}) :
    Sat HG decodeF (Env.cons d (Env.cons a e)) ↔ DecodedIn HG d a :=
  (sat_decodeF_tail e fun _ => U).trans (decode_read (fun h hz => HG.mem h hz) _
    (Env.cons_mem hd (Env.cons_mem ha fun _ => hU)))

/-- **The `HG` output spectrum** of this formula: exactly the ordinals with an `HG` injection
into `U`. -/
theorem hg_spectrum_exact {U : PSet.{u}} (hU : HG U) (e : Nat → PSet.{u}) (a : PSet.{u}) :
    (¬¬∃ d, d ∈ diagrams U ∧ HG a ∧ Sat HG decodeF (Env.cons d (Env.cons a e))) ↔
      IsOrd a ∧ CanInject HG a U := by
  constructor
  · intro h
    exact Stable.of_nn h fun ⟨d, hd, ha, hs⟩ =>
      have hh := (sat_decodeF_HG hU (HG.mem (hg_diagrams hU) hd) ha e).1 hs
      ⟨hh.1, decodedIn_sound hd hh⟩
  · rintro ⟨ha, hi⟩
    exact nn_map (fun ⟨d, hd, hdM, haM, hh⟩ => ⟨d, hd, haM, (sat_decodeF_HG hU hdM haM e).2 hh⟩)
      (decodedIn_complete hU ha hi)

/-- **The barrier equivalence for this decoder.** The rank-bound obligation of the model's
Replacement clause at `decodeF` and `diagrams U` is exactly negative existence of an
`HG`-relative barrier at `U`. A reduction, not a producer. -/
theorem barrier_iff_rankBounded {U : PSet.{u}} (hU : HG U) (e : Nat → PSet.{u}) :
    (¬¬∃ k, Barrier HG U k) ↔ RankBounded decodeF e (diagrams U) := by
  constructor
  · refine nn_map fun ⟨k, hk⟩ => ⟨k, hk.1, fun d a hd ha hs => ?_⟩
    have hh := (sat_decodeF_HG hU (HG.mem (hg_diagrams hU) hd) ha e).1 hs
    exact (mem_congr_left hh.1.rank_equiv).2 (injected_lt_HG_barrier hk hh.1 (decodedIn_sound hd hh))
  · refine nn_map fun ⟨k, hko, hk⟩ => ⟨k, hko, fun f hf hi => ?_⟩
    have bad : rank k ∈ k := Stable.of_nn (decodedIn_complete hU hko (nn_intro ⟨f, hf, hi⟩))
      fun ⟨d, hd, hdM, hkM, hh⟩ => hk d k hd hkM ((sat_decodeF_HG hU hdM hkM e).2 hh)
    exact not_mem_self k ((mem_congr_left hko.rank_equiv).1 bad)

theorem decodeF_HG_functional {U : PSet.{u}} (hU : HG U) (e : Nat → PSet.{u}) {d a b : PSet.{u}}
    (hd : d ∈ diagrams U) (ha : HG a) (hb : HG b)
    (h1 : Sat HG decodeF (Env.cons d (Env.cons a e)))
    (h2 : Sat HG decodeF (Env.cons d (Env.cons b e))) : a ≈ b :=
  decodedIn_unique ((sat_decodeF_HG hU (HG.mem (hg_diagrams hU) hd) ha e).1 h1)
    ((sat_decodeF_HG hU (HG.mem (hg_diagrams hU) hd) hb e).1 h2)

/-- With a barrier supplied, the unchanged Replacement consumer returns an `HG` collecting set. -/
theorem collecting_of_barrier {U : PSet.{u}} (hU : HG U) (e : Nat → PSet.{u}) (he : ∀ i, HG (e i))
    (hbar : ¬¬∃ k, Barrier HG U k) :
    ¬¬∃ b, HG b ∧ ∀ d a, d ∈ diagrams U → HG a →
      Sat HG decodeF (Env.cons d (Env.cons a e)) → a ∈ b :=
  nn_bind ((barrier_iff_rankBounded hU e).1 hbar) fun ⟨_, hk, hbound⟩ =>
    hg_replacement_of_rank_bound hk (hg_diagrams hU) he
      (fun _ _ _ hd ha ha' h1 h2 => decodeF_HG_functional hU e hd ha ha' h1 h2) hbound

/-- An external barrier improves to an `HG` barrier: the rank of the collecting set. -/
theorem internal_barrier_of_barrier {U : PSet.{u}} (hU : HG U) (h : ¬¬∃ k, Barrier HG U k) :
    ¬¬∃ k, HG k ∧ Barrier HG U k := by
  refine nn_map (fun ⟨B, hBM, hB⟩ => ⟨rank B, HG.rank hBM, isOrd_rank B, fun f hf hfi => ?_⟩)
    (collecting_of_barrier hU (fun _ => U) (fun _ => hU) h)
  have hm : rank B ∈ B := Stable.of_nn (decodedIn_complete hU (isOrd_rank B) (nn_intro ⟨f, hf, hfi⟩))
    fun ⟨d, hd, hdM, haM, hh⟩ => hB d (rank B) hd haM ((sat_decodeF_HG hU hdM haM _).2 hh)
  exact not_mem_self (rank B) ((mem_congr_left (isOrd_rank B).rank_equiv).1 (rank_mem hm))

end HG

/-- info: 'PSet.OrdDecode.decoded_spectrum' does not depend on any axioms -/
#guard_msgs in #print axioms decoded_spectrum
/-- info: 'PSet.OrdDecode.barrier_iff_exact_image' does not depend on any axioms -/
#guard_msgs in #print axioms barrier_iff_exact_image
/-- info: 'PSet.OrdDecode.hg_spectrum_exact' does not depend on any axioms -/
#guard_msgs in #print axioms hg_spectrum_exact
/-- info: 'PSet.OrdDecode.barrier_iff_rankBounded' does not depend on any axioms -/
#guard_msgs in #print axioms barrier_iff_rankBounded
/-- info: 'PSet.OrdDecode.internal_barrier_of_barrier' does not depend on any axioms -/
#guard_msgs in #print axioms internal_barrier_of_barrier

end PSet.OrdDecode
