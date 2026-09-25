import ConZF.DecodeSpectrum
import ConZF.SetSat
/-!
Cofinal label capacity of the fixed decoder, for the actual definability rule `ISat`.

* **Rank stages.** At a successor-closed ordinal `η`, `V_η` is closed under pairs, unions,
  powersets, products and subsets of its members, so a decoded pair `d, α ∈ V_η` already has its
  isomorphism graph in `V_η`: `sat_decode_at_limit` reads `decodeF` at `V_η` exactly as
  `Decoded`. This is downward absoluteness of this one Σ₁ formula at such stages, not a general
  principle.
* **Reaching.** Every successor `δ + 1` is reached from `0` by the parameter-free formula
  `maxOrdF` ("`y` is the largest ordinal") on the source `{∅}` (`successor_reach_zero`); every
  successor-closed `η` above `λ U := rank (diagrams U)` that embeds in `U` is reached from
  `λ U` by `decodeF` on the source `diagrams U` (`decoder_reach`). In both, the original outputs
  are kept: the values are `δ` and the ordinals `β < η` themselves.
* **The controller cap.** For every ordinal `η` embeddable in `U`, the least controller
  `Gν ISat η` is at most `λ U` (`controller_le`): no bound on the decoder's outputs is assumed.
  Hence one native library `D (succ (λ U))` and a fixed small label type `SmallLabel` cover every
  label available at every such `η` (`label_coverage`), and the children so labelled remain
  cofinal in each hereditarily good target (`cofinal_small_children`).
* **`HG` saturation.** For an `HG` base `U`, every ordinal embeddable in `U` is `HG`
  (`injectable_hg`), and so is the injection graph. So at `HG` bases the `HG`-relative spectrum
  and barriers of the decoder coincide with the ambient ones (`hg_barrier_iff_ambient`,
  `rankBounded_iff_ambient_barrier`).

Not proved: any common bound on the decoded ordinals (the barrier), and the extension of the
base of the whole construction from the specific `U` supplied to arbitrary bases. Nothing here
constructs `Acc`.
-/
universe u

namespace PSet.OrdDecode
open Fml CardF

/-! ### Rank stages -/

/-- Successor-closed ordinals. Zero is allowed. -/
structure SuccClosed (η : PSet.{u}) : Prop where
  ord : IsOrd η
  next : ∀ x, x ∈ η → succ x ∈ η

theorem below_of_le {a b k : PSet.{u}} (hk : IsOrd k) (hab : a ∈ succ b) (hb : b ∈ k) : a ∈ k :=
  Stable.of_nn (mem_succ.1 hab) fun
    | .inl h => hk.trans b hb a h
    | .inr e => (mem_congr_left e).2 hb

theorem le_subset {a b : PSet.{u}} (hb : IsOrd b) (h : a ∈ succ b) : ∀ z, z ∈ a → z ∈ b :=
  fun z hz => Stable.of_nn (mem_succ.1 h) fun
    | .inl hab => hb.trans a hab z hz
    | .inr e => (mem_congr_right e).1 hz

theorem subset_rank_le {x y : PSet.{u}} (h : ∀ z, z ∈ x → z ∈ y) : rank x ∈ succ (rank y) :=
  rank_mem_succ (isOrd_rank y) fun z hz => rank_mem (h z hz)

theorem subset_vl {η x y : PSet.{u}} (he : IsOrd η) (hy : y ∈ Vl η) (h : ∀ z, z ∈ x → z ∈ y) :
    x ∈ Vl η :=
  (mem_Vl_ord he).2 (below_of_le he (subset_rank_le h) ((mem_Vl_ord he).1 hy))

theorem empty_vl {η x : PSet.{u}} (he : IsOrd η) (hx : x ∈ Vl η) : empty ∈ Vl η :=
  subset_vl he hx fun z hz => (not_mem_empty z hz).elim

theorem ordinal_vl {η a : PSet.{u}} (he : IsOrd η) (ha : IsOrd a) (h : a ∈ η) : a ∈ Vl η :=
  (mem_Vl_ord he).2 ((mem_congr_left ha.rank_equiv).2 h)

theorem sUnion_vl {η x : PSet.{u}} (he : IsOrd η) (hx : x ∈ Vl η) : sUnion x ∈ Vl η := by
  refine (mem_Vl_ord he).2 (below_of_le he (rank_mem_succ (isOrd_rank x) fun z hz => ?_)
    ((mem_Vl_ord he).1 hx))
  exact Stable.of_nn (mem_sUnion.1 hz) fun ⟨_, hy, hzy⟩ =>
    (isOrd_rank x).trans _ (rank_mem hy) _ (rank_mem hzy)

theorem powerset_vl {η x : PSet.{u}} (he : SuccClosed η) (hx : x ∈ Vl η) : powerset x ∈ Vl η :=
  (mem_Vl_ord he.ord).2 (below_of_le he.ord
    (rank_mem_succ (isOrd_rank x).succ fun _ hz => subset_rank_le (mem_powerset.1 hz))
    (he.next _ ((mem_Vl_ord he.ord).1 hx)))

theorem upair_vl {η x y : PSet.{u}} (he : SuccClosed η) (hx : x ∈ Vl η) (hy : y ∈ Vl η) :
    upair x y ∈ Vl η := by
  have key : ∀ {x y : PSet.{u}} (R : PSet.{u}), IsOrd R → R ∈ η → rank x ∈ succ R →
      rank y ∈ succ R → upair x y ∈ Vl η := fun R hR hr hx hy =>
    (mem_Vl_ord he.ord).2 (below_of_le he.ord (rank_mem_succ hR.succ fun _ hz =>
      Stable.of_nn (mem_upair.1 hz) fun
        | .inl e => (mem_congr_left (rank_congr e)).2 hx
        | .inr e => (mem_congr_left (rank_congr e)).2 hy) (he.next R hr))
  refine Stable.of_nn ((isOrd_rank x).trichotomy (isOrd_rank y)) fun
    | .inl h => key _ (isOrd_rank y) ((mem_Vl_ord he.ord).1 hy) (mem_succ_of_mem h) (self_mem_succ _)
    | .inr (.inl e) =>
      key _ (isOrd_rank y) ((mem_Vl_ord he.ord).1 hy) (mem_succ_of_equiv e) (self_mem_succ _)
    | .inr (.inr h) =>
      key _ (isOrd_rank x) ((mem_Vl_ord he.ord).1 hx) (self_mem_succ _) (mem_succ_of_mem h)

theorem singleton_vl {η x : PSet.{u}} (he : SuccClosed η) (hx : x ∈ Vl η) : singleton x ∈ Vl η :=
  subset_vl he.ord (upair_vl he hx hx) fun _ hz => mem_upair.2 (nn_intro (.inl (mem_singleton.1 hz)))

theorem pair_vl {η x y : PSet.{u}} (he : SuccClosed η) (hx : x ∈ Vl η) (hy : y ∈ Vl η) :
    pair x y ∈ Vl η :=
  upair_vl he (singleton_vl he hx) (upair_vl he hx hy)

theorem product_vl {η A B : PSet.{u}} (he : SuccClosed η) (ha : A ∈ Vl η) (hb : B ∈ Vl η) :
    product A B ∈ Vl η := by
  have hX : sUnion (upair A B) ∈ Vl η := sUnion_vl he.ord (upair_vl he ha hb)
  refine subset_vl he.ord (powerset_vl he (powerset_vl he hX)) fun q hq => ?_
  refine Stable.of_nn (mem_product.1 hq) fun ⟨a, b, ha, hb, e⟩ => (mem_congr_left e).2 ?_
  exact pair_mem_powerset_powerset (mem_sUnion.2 (nn_intro ⟨A, mem_upair_left _ _, ha⟩))
    (mem_sUnion.2 (nn_intro ⟨B, mem_upair_right _ _, hb⟩))

theorem pure_map_vl {η f a A : PSet.{u}} (he : SuccClosed η) (ha : a ∈ Vl η) (hA : A ∈ Vl η)
    (hf : IsPureFun A f a) : f ∈ Vl η :=
  subset_vl he.ord (product_vl he ha hA) fun q hq => mem_product.2 (hf.1 q hq)

/-- Reading the ordinal formula needs only transitivity of the class. -/
theorem transF_read {M : PSet.{u} → Prop} (tr : ∀ {a z}, M a → z ∈ a → M z) {E : Nat → PSet.{u}}
    (hE : ∀ i, M (E i)) (a : Nat) : Sat M (transF a) E ↔ Trans (E a) :=
  ⟨fun h y hy z hz => h y (tr (hE a) hy) z (tr (tr (hE a) hy) hz) hz hy,
   fun h y _ z _ hz hy => h y hy z hz⟩

theorem ordF_read {M : PSet.{u} → Prop} (tr : ∀ {a z}, M a → z ∈ a → M z) {E : Nat → PSet.{u}}
    (hE : ∀ i, M (E i)) (a : Nat) : Sat M (ordF a) E ↔ IsOrd (E a) := by
  refine sat_and.trans ⟨fun ⟨h, hmem⟩ => ⟨(transF_read tr hE a).1 h, fun z hz => ?_⟩,
    fun h => ⟨(transF_read tr hE a).2 h.trans, fun z hz hza => ?_⟩⟩
  · exact (transF_read tr (Env.cons_mem (tr (hE a) hz) hE) 0).1 (hmem z (tr (hE a) hz) hz)
  · exact (transF_read tr (Env.cons_mem hz hE) 0).2 (h.mem_trans z hza)

/-- At a successor-closed stage, the original isomorphism graph is already in the stage. -/
theorem decoded_at_limit {η d a : PSet.{u}} (he : SuccClosed η) (hd : d ∈ Vl η) (ha : a ∈ Vl η) :
    Decoded d a ↔ DecodedIn (· ∈ Vl η) d a := by
  refine ⟨fun h => ⟨h.1, nn_map (fun ⟨A, r, f, ed, hf⟩ => ?_) h.2⟩, fun h => h.forget⟩
  have hA : A ∈ Vl η := Vl_trans (Vl_trans hd ((mem_congr_right ed).2 (mem_upair_left _ _)))
    (self_mem_singleton A)
  have hr : r ∈ Vl η := Vl_trans (Vl_trans hd ((mem_congr_right ed).2 (mem_upair_right _ _)))
    (mem_upair_right _ _)
  exact ⟨A, r, f, hA, hr, pure_map_vl he ha hA hf.map, ed, hf⟩

/-- The two-slot environment `[x, y]`, padded with `∅`. -/
def env2 (x y : PSet.{u}) : Nat → PSet.{u} := Env.cons x (Env.cons y fun _ => empty)

theorem env2_vl {η x y : PSet.{u}} (he : IsOrd η) (hx : x ∈ Vl η) (hy : y ∈ Vl η) :
    ∀ i, env2 x y i ∈ Vl η :=
  Env.cons_mem hx (Env.cons_mem hy fun _ => empty_vl he hx)

/-- Exact reading of the decoder at a successor-closed rank stage. -/
theorem sat_decode_at_limit {η d a : PSet.{u}} (he : SuccClosed η) (hd : d ∈ Vl η) (ha : a ∈ Vl η) :
    Sat (· ∈ Vl η) decodeF (env2 d a) ↔ Decoded d a :=
  (decode_read (fun h hz => Vl_trans h hz) (env2 d a) (env2_vl he.ord hd ha)).trans
    (decoded_at_limit he hd ha).symm

/-! ### Reaching by the decoder -/

section Reach
variable [Budget.{u}]

/-- The controller floor: the rank of the source of the decoder. -/
def lambda (U : PSet.{u}) : PSet.{u} := rank (diagrams U)

omit [Budget.{u}] in
theorem lambda_ord (U : PSet.{u}) : IsOrd (lambda U) := isOrd_rank _

/-- The parameter-free code of the decoder. -/
def decoderCode : PSet.{u} := code decodeF 0 fun _ => empty

omit [Budget.{u}] in
theorem decode_of_isat {η d a : PSet.{u}} (he : IsOrd η) (h : ISat η decoderCode d a) :
    Decoded d a :=
  have hs := (isat_code (ψ := decodeF) (m := 0) bound_decodeF).1 h
  ((decode_read (fun hx hz => Vl_trans hx hz) (env2 d a) (env2_vl he hs.1 hs.2.1)).1 hs.2.2).forget

theorem source_in_budget (U : PSet.{u}) : diagrams U ∈ D (lambda U) :=
  mem_D_of_subset (lambda_ord U) fun _ hz => hz

theorem decoder_in_budget (ν : PSet.{u}) : decoderCode ∈ D ν :=
  code_mem_D fun i hi => (Nat.not_lt_zero i hi).elim

omit [Budget.{u}] in
/-- The decoder on `diagrams U` is unbounded at every successor-closed `η > λ U` embeddable in
`U`: the values are the ordinals `β < η` themselves, from restrictions of one injection. -/
theorem decoder_unb {η U : PSet.{u}} (he : SuccClosed η) (hl : lambda U ∈ η) (hinj : Emb η U) :
    Unb ISat η decoderCode (diagrams U) := by
  have hS : diagrams U ∈ Vl η := (mem_Vl_ord he.ord).2 hl
  refine ⟨fun d a b _ ha hb => decoded_unique (decode_of_isat he.ord ha) (decode_of_isat he.ord hb),
    fun d a _ h => (mem_Vl_ord he.ord).1 ((isat_code (ψ := decodeF) (m := 0) bound_decodeF).1 h).2.1,
    fun z hz => ?_⟩
  refine nn_map (fun ⟨d, hd, hdec⟩ => ?_) (diagram_of_emb (he.ord.mem hz) (hinj.down he.ord hz))
  have hdV : d ∈ Vl η := Vl_trans hS hd
  have hzV : z ∈ Vl η := ordinal_vl he.ord (he.ord.mem hz) hz
  exact ⟨d, z, hd, (isat_code (ψ := decodeF) (m := 0) bound_decodeF).2
    ⟨hdV, hzV, (sat_decode_at_limit he hdV hzV).2 hdec⟩,
    (mem_congr_right (succ_congr (he.ord.mem hz).rank_equiv)).2 (self_mem_succ z)⟩

theorem decoder_reach {η U : PSet.{u}} (he : SuccClosed η) (hl : lambda U ∈ η) (hinj : Emb η U) :
    Reach ISat η (lambda U) :=
  nn_intro ⟨decoderCode, diagrams U, decoder_in_budget _, source_in_budget _, decoder_unb he hl hinj⟩

/-- Slot `0` unused; slot `1` is the largest ordinal of the stage. -/
def maxOrdF : Fml := and (ordF 1) (all (imp (ordF 0) (or (mem 0 2) (eq 0 2))))

omit [Budget.{u}] in
set_option maxRecDepth 200000 in
theorem maxOrd_bound : Bound 2 maxOrdF := by decide

def maxOrdCode : PSet.{u} := code maxOrdF 0 fun _ => empty

omit [Budget.{u}] in
theorem maxOrd_at_succ {δ x y : PSet.{u}} (hd : IsOrd δ) (hx : x ∈ Vl (succ δ))
    (hy : y ∈ Vl (succ δ)) : Sat (· ∈ Vl (succ δ)) maxOrdF (env2 x y) ↔ y ≈ δ := by
  have tr : ∀ {a z : PSet.{u}}, a ∈ Vl (succ δ) → z ∈ a → z ∈ Vl (succ δ) := fun h hz => Vl_trans h hz
  have hE := env2_vl hd.succ hx hy
  have hdV : δ ∈ Vl (succ δ) := ordinal_vl hd.succ hd (self_mem_succ _)
  constructor
  · intro h
    have hh := sat_and.1 h
    have hyo := (ordF_read tr hE 1).1 hh.1
    have hyd : y ∈ succ δ := (mem_congr_left hyo.rank_equiv).1 ((mem_Vl_ord hd.succ).1 hy)
    have hdy : δ ∈ succ y := mem_succ.2 (sat_or.1
      (hh.2 δ hdV ((ordF_read tr (Env.cons_mem hdV hE) 0).2 hd)))
    exact ext fun z => ⟨le_subset hd hyd z, le_subset hyo hdy z⟩
  · intro ey
    refine sat_and.2 ⟨(ordF_read tr hE 1).2 (hd.resp ey.symm), fun z hz hzo => ?_⟩
    have ho := (ordF_read tr (Env.cons_mem hz hE) 0).1 hzo
    have hzd : z ∈ succ δ := (mem_congr_left ho.rank_equiv).1 ((mem_Vl_ord hd.succ).1 hz)
    exact sat_or.2 (mem_succ.1 ((mem_congr_right (succ_congr ey)).2 hzd))

omit [Budget.{u}] in
/-- Every successor is reached from `0` by a parameter-free formula on the source `{∅}`. -/
theorem successor_unb_zero {δ : PSet.{u}} (hd : IsOrd δ) : Unb ISat (succ δ) maxOrdCode (singleton empty) := by
  refine ⟨fun x y z _ hy hz => ?_, fun x y _ hy => ?_, fun z hz => ?_⟩
  · have sy := (isat_code (ψ := maxOrdF) (m := 0) maxOrd_bound).1 hy
    have sz := (isat_code (ψ := maxOrdF) (m := 0) maxOrd_bound).1 hz
    exact ((maxOrd_at_succ hd sy.1 sy.2.1).1 sy.2.2).trans
      ((maxOrd_at_succ hd sz.1 sz.2.1).1 sz.2.2).symm
  · exact (mem_Vl_ord hd.succ).1 ((isat_code (ψ := maxOrdF) (m := 0) maxOrd_bound).1 hy).2.1
  · have hdV := ordinal_vl hd.succ hd (self_mem_succ δ)
    have h0V := empty_vl hd.succ hdV
    exact nn_intro ⟨empty, δ, self_mem_singleton _, (isat_code (ψ := maxOrdF) (m := 0) maxOrd_bound).2
      ⟨h0V, hdV, (maxOrd_at_succ hd h0V hdV).2 (Equiv.refl _)⟩,
      (mem_congr_right (succ_congr hd.rank_equiv)).2 hz⟩

theorem successor_reach_zero {δ : PSet.{u}} (hd : IsOrd δ) : Reach ISat (succ δ) empty :=
  nn_intro ⟨maxOrdCode, singleton empty, code_mem_D fun i hi => (Nat.not_lt_zero i hi).elim,
    singleton_mem_D (empty_mem_D empty), successor_unb_zero hd⟩

/-! ### The controller cap -/

theorem reach_up {η a b : PSet.{u}} (hab : a ∈ b) (h : Reach ISat η a) : Reach ISat η b :=
  nn_map (fun ⟨q, s, hq, hs, hu⟩ => ⟨q, s, D_mono hab hq, D_mono hab hs, hu⟩) h

/-- The cut is an ordinal even without a reachability premise. -/
theorem controller_ord {η : PSet.{u}} (he : IsOrd η) : IsOrd (Gν ISat η) := by
  refine ⟨fun z hz w hw => ?_, fun z hz => he.mem_trans z ((mem_Gν ISat_resp).1 hz).1⟩
  have hz' := (mem_Gν ISat_resp).1 hz
  exact (mem_Gν ISat_resp).2 ⟨he.trans z hz'.1 w hw, fun hr => hz'.2 (reach_up hw hr)⟩

/-- Any reaching stage bounds the least controller. -/
theorem controller_subset_of_reach {η ν : PSet.{u}} (he : IsOrd η) (hn : IsOrd ν)
    (hr : Reach ISat η ν) : ∀ z, z ∈ Gν ISat η → z ∈ ν := by
  intro z hz
  have hz' := (mem_Gν ISat_resp).1 hz
  refine Stable.of_nn ((he.mem hz'.1).trichotomy hn) fun
    | .inl h => h
    | .inr (.inl e) => (hz'.2 (hr.resp ISat_resp (Equiv.refl _) e.symm)).elim
    | .inr (.inr h) => (hz'.2 (reach_up h hr)).elim

theorem successor_controller_zero {δ : PSet.{u}} (hd : IsOrd δ) : Gν ISat (succ δ) ≈ empty :=
  ext fun z => ⟨controller_subset_of_reach hd.succ isOrd_empty (successor_reach_zero hd) z,
    fun h => (not_mem_empty z h).elim⟩

omit [Budget.{u}] in
/-- An ordinal that is not a successor is successor-closed. -/
theorem succClosed_of_not_successor {η : PSet.{u}} (he : IsOrd η)
    (hn : ¬∃ δ, IsOrd δ ∧ η ≈ succ δ) : SuccClosed η := by
  refine ⟨he, fun z hz => ?_⟩
  have hs : succ z ∈ succ η := (he.mem hz).succ.mem_succ_of_subset he fun w hw =>
    Stable.of_nn (mem_succ.1 hw) fun
      | .inl h => he.trans z hz w h
      | .inr e => (mem_congr_left e).2 hz
  exact Stable.of_nn (mem_succ.1 hs) fun
    | .inl h => h
    | .inr e => (hn ⟨z, he.mem hz, e.symm⟩).elim

/-- **The cap.** No bound on the decoder's outputs, and no negation of one, is assumed. -/
theorem controller_subset {η U : PSet.{u}} (he : IsOrd η) (hi : Emb η U) :
    ∀ z, z ∈ Gν ISat η → z ∈ lambda U := by
  refine Stable.by_cases (lambda U ∈ η) (fun hl => ?_) fun hn z hz => ?_
  · refine Stable.by_cases (∃ δ, IsOrd δ ∧ η ≈ succ δ) (fun ⟨δ, hd, ed⟩ z hz => ?_) fun hns => ?_
    · exact (not_mem_empty z (controller_subset_of_reach he isOrd_empty
        ((successor_reach_zero hd).resp ISat_resp ed.symm (Equiv.refl _)) z hz)).elim
    · exact controller_subset_of_reach he (lambda_ord U)
        (decoder_reach (succClosed_of_not_successor he hns) hl hi)
  · have hze := ((mem_Gν ISat_resp).1 hz).1
    exact Stable.of_nn (he.trichotomy (lambda_ord U)) fun
      | .inl h => (lambda_ord U).trans η h z hze
      | .inr (.inl e) => (mem_congr_right e).1 hze
      | .inr (.inr h) => (hn h).elim

theorem controller_le {η U : PSet.{u}} (he : IsOrd η) (hi : Emb η U) :
    Gν ISat η ∈ succ (lambda U) :=
  (controller_ord he).mem_succ_of_subset (lambda_ord U) (controller_subset he hi)

/-- One native library for all controllers at ordinals embeddable in `U`. -/
def library (U : PSet.{u}) : PSet.{u} := D (succ (lambda U))

theorem budget_in_library {η U w : PSet.{u}} (he : IsOrd η) (hi : Emb η U)
    (hw : w ∈ D (Gν ISat η)) : w ∈ library U :=
  D_mono (controller_le he hi) hw

/-- A small label type, fixed before any output is considered: the child `a`, the children `b`
indexed by the library, and the children `c` indexed by the source `S`. -/
inductive SmallLabel (U S : PSet.{u}) : Type u
  | first
  | second (i : (library U).Idx)
  | source (i : S.Idx)

def SmallLabel.label {U S : PSet.{u}} : SmallLabel U S → Label.{u}
  | .first => .a
  | .second i => .b ((library U).Func i)
  | .source i => .c (S.Func i)

def SmallLabel.path {U S : PSet.{u}} : List (SmallLabel U S) → Path.{u}
  | [] => []
  | l :: p => l.label :: path p

/-- Every label available at a controller of an embeddable ordinal is represented, up to
`Label.Equiv`, by a small label. -/
theorem label_coverage {η U S G : PSet.{u}} (he : IsOrd η) (hi : Emb η U) (eG : G ≈ Gν ISat η)
    {l : Label.{u}} (h : Avail D S G l) : ¬¬∃ a : SmallLabel U S, l.Equiv a.label := by
  rcases h with h | ⟨w, hw, el⟩ | ⟨x, hx, el⟩
  · subst h
    exact nn_intro ⟨.first, Label.Equiv.a⟩
  · refine nn_map (fun ⟨i, ei⟩ => ⟨.second i, ?_⟩)
      (budget_in_library he hi ((mem_congr_right (D_congr eG)).1 hw))
    cases el with
    | b ew => exact .b (ew.trans ei)
  · refine nn_map (fun ⟨i, ei⟩ => ⟨.source i, ?_⟩) hx
    cases el with
    | c ex => exact .c (ex.trans ei)

/-- The small-labelled children remain cofinal in each hereditarily good embeddable target. -/
theorem cofinal_small_children {η U S : PSet.{u}} (he : Cls ISat η) (hi : Emb η U) (z : PSet.{u}) :
    z ∈ η ↔ ¬¬∃ (a : SmallLabel U S) (t : PSet.{u}), rule ISat η a.label t ∧ z ∈ succ t := by
  constructor
  · intro hz
    have hr : Reachable ISat η := he.good z hz
    have hG : ∀ x, x ∈ Gν ISat η ↔ ¬¬∃ t, rule ISat η .a t ∧ x ∈ t := fun x =>
      ⟨fun hx => nn_intro ⟨Gν ISat η, ⟨hr, Equiv.refl _⟩, hx⟩,
       fun hx => Stable.of_nn hx fun ⟨_, ht, hxt⟩ => (mem_congr_right ht.2).1 hxt⟩
    refine nn_bind ((rule_sup ISat_resp S he hG z).1 hz) fun ⟨l, t, hl, ht, hzt⟩ => ?_
    exact nn_map (fun ⟨a, ea⟩ => ⟨a, t, rule_resp ISat_resp (Equiv.refl _) ea (Equiv.refl _) ht, hzt⟩)
      (label_coverage he.1 hi (Equiv.refl _) hl)
  · intro h
    exact Stable.of_nn h fun ⟨_, t, ht, hzt⟩ => below_of_le he.1 hzt (rule_mem ISat_resp he ht).1

/-! ### `HG` saturation -/

theorem floor_cls {U : PSet.{u}} (hU : HG U) : Cls ISat (lambda U) := hg_diagrams hU

/-- Above the floor, embeddable ordinals are reachable: successors by `maxOrdF`, the others by
`decodeF`. -/
theorem reachable_above_floor {η U : PSet.{u}} (he : IsOrd η) (hl : lambda U ∈ η) (hi : Emb η U) :
    Reachable ISat η :=
  Stable.by_cases (∃ δ, IsOrd δ ∧ η ≈ succ δ)
    (fun ⟨_, hd, ed⟩ => (reachable_succ hd).resp ISat_resp ed.symm)
    fun hn => nn_intro ⟨lambda U, hl, decoder_reach (succClosed_of_not_successor he hn) hl hi⟩

theorem injectable_cls {U η : PSet.{u}} (hU : HG U) (he : IsOrd η) (hi : Emb η U) : Cls ISat η := by
  refine ⟨he, fun μ hm => ?_⟩
  have hmo : IsOrd μ := he.succ.mem hm
  have hmi : Emb μ U := hi.le he hm
  refine Stable.by_cases (lambda U ∈ μ) (fun hl _ _ => reachable_above_floor hmo hl hmi) fun hn => ?_
  refine (floor_cls hU).2 μ (Stable.of_nn (hmo.trichotomy (lambda_ord U)) fun
    | .inl h => mem_succ_of_mem h
    | .inr (.inl e) => mem_succ_of_equiv e
    | .inr (.inr h) => (hn h).elim)

/-- **Saturation.** Every ordinal embeddable in an `HG` base is `HG`. -/
theorem injectable_hg {U η : PSet.{u}} (hU : HG U) (he : IsOrd η) (hi : Emb η U) : HG η :=
  Cls.resp he.rank_equiv.symm (injectable_cls hU he hi)

/-- The original injection graph is `HG`: a subset of `η × U`. -/
theorem injection_graph_hg {U η f : PSet.{u}} (hU : HG U) (he : IsOrd η) (hf : OInj f η U) : HG f :=
  hg_subclosed (hg_product (injectable_hg hU he (nn_intro ⟨f, hf⟩)) hU)
    fun q hq => mem_product.2 (hf.1.1 q hq)

theorem emb_iff_canInject_hg {U η : PSet.{u}} (hU : HG U) (he : IsOrd η) :
    Emb η U ↔ CanInject HG η U :=
  ⟨nn_map fun ⟨f, hf⟩ => ⟨f, injection_graph_hg hU he hf, hf⟩, nn_map fun ⟨f, _, hf⟩ => ⟨f, hf⟩⟩

theorem decoded_hg {U d a : PSet.{u}} (hU : HG U) (hd : d ∈ diagrams U) (h : Decoded d a) : HG a :=
  injectable_hg hU h.1 (emb_of_decoded hd h)

/-- At an `HG` base the class guards of the decoder discard nothing. -/
theorem decoded_in_hg {U d a : PSet.{u}} (hU : HG U) (hd : d ∈ diagrams U) (h : Decoded d a) :
    DecodedIn HG d a := by
  have hdH : HG d := HG.mem (hg_diagrams hU) hd
  have haH : HG a := decoded_hg hU hd h
  refine ⟨h.1, nn_map (fun ⟨A, r, f, ed, hf⟩ => ?_) h.2⟩
  have hA : HG A := HG.mem (HG.mem hdH ((mem_congr_right ed).2 (mem_upair_left _ _)))
    (self_mem_singleton _)
  have hr : HG r := HG.mem (HG.mem hdH ((mem_congr_right ed).2 (mem_upair_right _ _)))
    (mem_upair_right _ _)
  exact ⟨A, r, f, hA, hr, hg_subclosed (hg_product haH hA) fun q hq => mem_product.2 (hf.map.1 q hq),
    ed, hf⟩

/-- The ambient meaning of the decoder at an `HG` base is its reading in `HG`. -/
theorem decoded_iff_sat_hg {U d a : PSet.{u}} (hU : HG U) (hd : d ∈ diagrams U) (e : Nat → PSet.{u}) :
    Decoded d a ↔ HG a ∧ Sat HG decodeF (Env.cons d (Env.cons a e)) :=
  ⟨fun h => ⟨decoded_hg hU hd h,
    (sat_decodeF_HG hU (HG.mem (hg_diagrams hU) hd) (decoded_hg hU hd h) e).2 (decoded_in_hg hU hd h)⟩,
   fun ⟨ha, hs⟩ => ((sat_decodeF_HG hU (HG.mem (hg_diagrams hU) hd) ha e).1 hs).forget⟩

/-- The ambient and `HG` spectra of the decoder coincide at `HG` bases. -/
theorem hg_spectrum_iff_ambient {U : PSet.{u}} (hU : HG U) (e : Nat → PSet.{u}) (a : PSet.{u}) :
    (¬¬∃ d, d ∈ diagrams U ∧ HG a ∧ Sat HG decodeF (Env.cons d (Env.cons a e))) ↔
      ¬¬∃ d, d ∈ diagrams U ∧ Decoded d a :=
  nn_congr ⟨fun ⟨d, hd, ha, hs⟩ => ⟨d, hd, (decoded_iff_sat_hg hU hd e).2 ⟨ha, hs⟩⟩,
    fun ⟨d, hd, h⟩ => ⟨d, hd, (decoded_iff_sat_hg hU hd e).1 h⟩⟩

/-- An `HG`-relative barrier at an `HG` base is an ambient barrier. -/
theorem hg_barrier_iff_ambient {U k : PSet.{u}} (hU : HG U) :
    Barrier HG U k ↔ Barrier (fun _ => True) U k :=
  ⟨fun h => ⟨h.1, fun f _ hf => h.2 f (injection_graph_hg hU h.1 hf) hf⟩,
   fun h => ⟨h.1, fun f _ hf => h.2 f trivial hf⟩⟩

/-- **The barrier equivalence at `HG` bases, in ambient terms.** The rank-bound obligation for
`decodeF` at `diagrams U` is exactly negative existence of an ambient barrier at `U`. -/
theorem rankBounded_iff_ambient_barrier {U : PSet.{u}} (hU : HG U) (e : Nat → PSet.{u}) :
    RankBounded decodeF e (diagrams U) ↔ ¬¬∃ k, Barrier (fun _ => True) U k :=
  (barrier_iff_rankBounded hU e).symm.trans
    (nn_congr ⟨fun ⟨k, hk⟩ => ⟨k, (hg_barrier_iff_ambient hU).1 hk⟩,
      fun ⟨k, hk⟩ => ⟨k, (hg_barrier_iff_ambient hU).2 hk⟩⟩)

end Reach

/-- info: 'PSet.OrdDecode.sat_decode_at_limit' does not depend on any axioms -/
#guard_msgs in #print axioms sat_decode_at_limit
/-- info: 'PSet.OrdDecode.decoder_reach' does not depend on any axioms -/
#guard_msgs in #print axioms decoder_reach
/-- info: 'PSet.OrdDecode.successor_reach_zero' does not depend on any axioms -/
#guard_msgs in #print axioms successor_reach_zero
/-- info: 'PSet.OrdDecode.controller_le' does not depend on any axioms -/
#guard_msgs in #print axioms controller_le
/-- info: 'PSet.OrdDecode.cofinal_small_children' does not depend on any axioms -/
#guard_msgs in #print axioms cofinal_small_children
/-- info: 'PSet.OrdDecode.injectable_hg' does not depend on any axioms -/
#guard_msgs in #print axioms injectable_hg
/-- info: 'PSet.OrdDecode.rankBounded_iff_ambient_barrier' does not depend on any axioms -/
#guard_msgs in #print axioms rankBounded_iff_ambient_barrier

end PSet.OrdDecode
