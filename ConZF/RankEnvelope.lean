import ConZF.DecodeGraph
import ConZF.Graph.Pair
import ConZF.Graph.Ordinals
import ConZF.Graph.Hartogs
import ConZF.GraphConsumer
/-!
Rank envelopes and the powerset history in the graph universe (nc4). Everything is over the full
ambient `GSet.{u}`; nothing here changes `NegCore`, and no unrestricted Collection is claimed.

* **Native/graph embedding** (reviewer probe, integrated): every graph subset of an embedded native
  set has an explicit native representative (`nativeSubset_read`); the embedding preserves the full
  ambient graph powerset (`embed_powerset`) and small unions (`embed_iUnion`); the structural tree
  recursion `W` satisfies `W t ≈ embed (Vl t)` (`W_equiv_embed_Vl`), so its members are negatively
  native (`W_native_members`); and a **native** envelope for a graph ordinal already gives that
  ordinal a native representative (`native_envelope_collapses`). The general target `RankCover κ E`
  asks for an arbitrary graph envelope; the native-envelope premise is strictly stronger.
* **Rank identities.** `rank X ⊆ γ ↔ ∀ Y ∈ X, rank Y ∈ γ` (`rank_subset_iff`) and
  `rank X ∈ β ↔ ¬¬∃ γ ∈ β, ∀ Y ∈ X, rank Y ∈ γ` (`rank_mem_iff`); the exact full-ambient reading
  `X ∈ W t ↔ rank X ∈ rank (embed t)` (`mem_W_iff`), giving actual rank envelopes at native tree
  indices (`rankCover_W`) and pointwise negative native representatives below them
  (`native_of_rank_mem`); no family of representatives is extracted.
* **The powerset history.** `PowHist κ h`: `h` is a pure total functional graph on `succ κ` whose
  rows satisfy the membership recurrence `X ∈ V_β ↔ ¬¬∃ γ ∈ β, W (⟨γ, W⟩ ∈ h ∧ X ⊆ W)`. Exact rows
  `X ∈ V_β ↔ rank X ∈ β` (`powHist_exact`), overlap uniqueness, the terminal row at `κ` as an
  envelope, and conversely the whole history from **one** supplied envelope by Separation and a
  range over the literal predecessors of `succ κ` (`hist`, `powHist_hist`). Hence
  `(¬¬∃ h, PowHist κ h) ↔ ¬¬∃ E, RankCover κ E` (`powHist_iff_rankCover`), with zero and successor
  laws for exact rows and the positive case at native tree indices (`powHist_native`). Strict rank
  membership is the row at `κ`; the envelope may be larger.
* **Prefix Collection.** Semantic only: negative existence of the history at `κ` is equivalent to
  ordinary Collection for the fixed matrix "correct history through `γ`" over the lower cone of
  `κ` (`powHist_iff_prefixCollection`). No source formula or satisfaction bridge is claimed.

Open: negative existence of a graph `RankCover` at `relHartogs (embed omega)`. Nothing here supplies
it; native domination of its envelope is not assumed.
-/
universe u

namespace GSet.Envelope
open PSet.OrdDecode

/-! ### The native/graph interface -/

def nativeSubset (x : PSet.{u}) (G : GSet.{u}) : PSet.{u} :=
  PSet.sep (fun z => Mem (embed z) G) x

theorem nativeSubset_read {x : PSet.{u}} {G : GSet.{u}} (h : Subset G (embed x)) :
    Equiv (embed (nativeSubset x G)) G := by
  have hp : ∀ z z' : PSet.{u}, z ≈ z' → Mem (embed z) G → Mem (embed z') G :=
    fun _ _ e hz => Mem.congr_left (embed_congr e) hz
  refine ext fun K => ⟨fun hk => ?_, fun hk => ?_⟩
  · refine Stable.of_nn (embed_readback hk) fun ⟨z, hz, ez⟩ => ?_
    exact Mem.congr_left ez.symm ((PSet.mem_sep hp).1 hz).2
  · refine Stable.of_nn (embed_readback (h K hk)) fun ⟨z, hz, ez⟩ => ?_
    exact Mem.congr_left ez.symm (embed_mem_iff.2 ((PSet.mem_sep hp).2 ⟨hz, Mem.congr_left ez hk⟩))

/-- The embedding preserves the full ambient graph powerset. -/
theorem embed_powerset (x : PSet.{u}) : Equiv (embed (PSet.powerset x)) (powerset (embed x)) := by
  refine ext fun G => ⟨fun hg => ?_, fun hg => ?_⟩
  · refine Stable.of_nn (embed_readback hg) fun ⟨z, hz, ez⟩ => ?_
    refine (mem_powerset _).2 fun K hk => ?_
    refine Stable.of_nn (embed_readback (Mem.congr_right ez hk)) fun ⟨w, hw, ew⟩ => ?_
    exact Mem.congr_left ew.symm (embed_mem_iff.2 ((PSet.mem_powerset.1 hz) w hw))
  · have hs := (mem_powerset _).1 hg
    have hn : nativeSubset x G ∈ PSet.powerset x :=
      PSet.mem_powerset.2 fun z hz =>
        ((PSet.mem_sep (fun _ _ e hm => Mem.congr_left (embed_congr e) hm)).1 hz).1
    exact Mem.congr_left (nativeSubset_read hs) (embed_mem_iff.2 hn)

theorem embed_iUnion {A : Type u} (f : A → PSet.{u}) :
    Equiv (embed (PSet.iUnion f)) (sUnion (range fun a => embed (f a))) := by
  refine ext fun K => ⟨fun hk => ?_, fun hk => ?_⟩
  · refine Stable.of_nn (embed_readback hk) fun ⟨z, hz, ez⟩ => ?_
    refine Stable.of_nn (PSet.mem_iUnion.1 hz) fun ⟨a, ha⟩ => ?_
    exact (mem_sUnion _).2 (nn_intro ⟨embed (f a), (mem_range _).2 (nn_intro ⟨a, Equiv.refl _⟩),
      Mem.congr_left ez.symm (embed_mem_iff.2 ha)⟩)
  · refine Stable.of_nn ((mem_sUnion _).1 hk) fun ⟨H, hh, hkh⟩ => ?_
    refine Stable.of_nn ((mem_range _).1 hh) fun ⟨a, ea⟩ => ?_
    refine Stable.of_nn (embed_readback (Mem.congr_right ea hkh)) fun ⟨z, hz, ez⟩ => ?_
    exact Mem.congr_left ez.symm (embed_mem_iff.2 (PSet.mem_iUnion.2 (nn_intro ⟨a, hz⟩)))

/-- The graph rank level of a native tree, by structural recursion with the full graph powerset. -/
def W : PSet.{u} → GSet.{u}
  | ⟨A, f⟩ => sUnion (range fun a : A => powerset (W (f a)))

theorem W_equiv_embed_Vl : ∀ t : PSet.{u}, Equiv (W t) (embed (PSet.Vl t))
  | ⟨A, f⟩ => by
    refine Equiv.trans ?_ (embed_iUnion (fun a : A => PSet.powerset (PSet.Vl (f a)))).symm
    refine ext fun K => ?_
    have side : ∀ (F H : A → GSet.{u}), (∀ a, Equiv (F a) (H a)) →
        Mem K (sUnion (range F)) → Mem K (sUnion (range H)) := by
      intro F H eh hk
      refine Stable.of_nn ((mem_sUnion _).1 hk) fun ⟨Y, hy, hky⟩ => ?_
      refine Stable.of_nn ((mem_range _).1 hy) fun ⟨a, ea⟩ => ?_
      exact (mem_sUnion _).2 (nn_intro ⟨H a, (mem_range _).2 (nn_intro ⟨a, Equiv.refl _⟩),
        Mem.congr_right (ea.trans (eh a)) hky⟩)
    have ep : ∀ a : A, Equiv (powerset (W (f a))) (embed (PSet.powerset (PSet.Vl (f a)))) := by
      intro a
      refine Equiv.trans ?_ (embed_powerset _).symm
      refine ext fun Y => (mem_powerset _).trans ?_
      refine Iff.trans ?_ (mem_powerset _).symm
      exact ⟨fun h Z hz => Mem.congr_right (W_equiv_embed_Vl (f a)) (h Z hz),
        fun h Z hz => Mem.congr_right (W_equiv_embed_Vl (f a)).symm (h Z hz)⟩
    exact ⟨side _ _ ep, side _ _ (fun a => (ep a).symm)⟩

/-- Every member of a level `W t` is negatively an embedded native set. -/
theorem W_native_members {t : PSet.{u}} {G : GSet.{u}} (h : Mem G (W t)) :
    ¬¬∃ x : PSet.{u}, x ∈ PSet.Vl t ∧ Equiv G (embed x) :=
  embed_readback (Mem.congr_right (W_equiv_embed_Vl t) h)

/-- The general target: a graph set containing every graph set of rank in `κ`. -/
def RankCover (κ E : GSet.{u}) : Prop := ∀ X : GSet.{u}, Mem (rank X) κ → Mem X E

/-- A **native** envelope is stronger than the requested arbitrary graph envelope: it already
gives the ordinal a native representative. -/
theorem native_envelope_collapses {κ : GSet.{u}} {E : PSet.{u}} (hκ : IsOrd κ)
    (h : RankCover κ (embed E)) : Equiv (embed (nativeSubset E κ)) κ := by
  refine nativeSubset_read fun β hβ => h β ?_
  exact Mem.congr_left (rank_equiv_of_isOrd (hκ.mem hβ)).symm hβ

/-! ### Rank identities -/

theorem ord_subset_iff {a b : GSet.{u}} (ha : IsOrd a) (hb : IsOrd b) :
    Subset a b ↔ ¬¬(Mem a b ∨ Equiv a b) :=
  ⟨IsOrd.subset ha hb, fun h K hK => Stable.of_nn h fun
    | .inl h => hb.1 a h K hK
    | .inr e => Mem.congr_right e hK⟩

/-- nc4 (1). -/
theorem rank_subset_iff {X γ : GSet.{u}} (hγ : IsOrd γ) :
    Subset (rank X) γ ↔ ∀ Y, Mem Y X → Mem (rank Y) γ := by
  constructor
  · exact fun h Y hY => h _ (rank_mem hY)
  · intro h K hK
    refine Stable.of_nn ((mem_rank_at' (G := X) (a := X.r)).1 hK) fun ⟨b, hb, hKb⟩ => ?_
    have hr : Mem (rank (X.at' b)) γ := h _ (at'_mem hb)
    rcases hKb with e | hm
    · exact Mem.congr_left e.symm hr
    · exact hγ.1 _ hr K hm

/-- nc4 (2). -/
theorem rank_mem_iff {X β : GSet.{u}} (hβ : IsOrd β) :
    Mem (rank X) β ↔ ¬¬∃ γ, Mem γ β ∧ ∀ Y, Mem Y X → Mem (rank Y) γ := by
  constructor
  · exact fun h => nn_intro ⟨rank X, h, fun _ hY => rank_mem hY⟩
  · intro h
    refine Stable.of_nn h fun ⟨γ, hγ, hY⟩ => ?_
    have hs := (rank_subset_iff (hβ.mem hγ)).2 hY
    refine Stable.of_nn ((isOrd_rank X).trichotomy (hβ.mem hγ)) fun
      | .inl h => hβ.1 γ hγ _ h
      | .inr (.inl e) => Mem.congr_left e.symm hγ
      | .inr (.inr h) => (not_mem_self γ (hs γ h)).elim

theorem mem_sUnion_range {ι : Type u} (F : ι → GSet.{u}) {X : GSet.{u}} :
    Mem X (sUnion (range F)) ↔ ¬¬∃ i, Mem X (F i) :=
  ⟨fun h => nn_bind ((mem_sUnion _).1 h) fun ⟨_, hY, hX⟩ =>
      nn_map (fun ⟨i, e⟩ => ⟨i, Mem.congr_right e hX⟩) ((mem_range _).1 hY),
   fun h => (mem_sUnion _).2 (nn_map (fun ⟨i, h⟩ => ⟨F i, (mem_range _).2 (nn_intro ⟨i, Equiv.refl _⟩), h⟩) h)⟩

/-- The rank of a small range: the ranks of the components and their members. -/
theorem mem_rank_range {ι : Type u} (F : ι → GSet.{u}) {K : GSet.{u}} :
    Mem K (rank (range F)) ↔ ¬¬∃ i, Equiv K (rank (F i)) ∨ Mem K (rank (F i)) := by
  constructor
  · intro h
    refine nn_bind ((mem_rank_at' (G := range F) (a := (range F).r)).1 h) fun ⟨b, hb, hK⟩ => ?_
    obtain ⟨i, rfl⟩ := rangeRel_none F hb
    have e : Equiv ((rank (range F)).at' (some ⟨i, (F i).r⟩)) (rank (F i)) :=
      rank_congr (range_at'_equiv F i (F i).r)
    rcases hK with hK | hK
    · exact nn_intro ⟨i, .inl (hK.trans e)⟩
    · exact nn_intro ⟨i, .inr (Mem.congr_right e hK)⟩
  · intro h
    refine nn_bind h fun ⟨i, hK⟩ => (mem_rank_at' (G := range F) (a := (range F).r)).2
      (nn_intro ⟨some ⟨i, (F i).r⟩, RangeRel.root i, ?_⟩)
    have e : Equiv ((rank (range F)).at' (some ⟨i, (F i).r⟩)) (rank (F i)) :=
      rank_congr (range_at'_equiv F i (F i).r)
    rcases hK with hK | hK
    · exact .inl (hK.trans e.symm)
    · exact .inr (Mem.congr_right e.symm hK)

/-- **The exact full-ambient reading of the level** `W t`, nc4 (22). -/
theorem mem_W_iff : ∀ (t : PSet.{u}) (X : GSet.{u}), Mem X (W t) ↔ Mem (rank X) (rank (embed t))
  | ⟨A, f⟩, X => by
    have step : ∀ a : A, Mem X (powerset (W (f a))) ↔
        ¬¬(Mem (rank X) (rank (embed (f a))) ∨ Equiv (rank X) (rank (embed (f a)))) := fun a =>
      (mem_powerset _).trans <| Iff.trans
        ⟨fun h Y hY => (mem_W_iff (f a) Y).1 (h Y hY), fun h Y hY => (mem_W_iff (f a) Y).2 (h Y hY)⟩
        ((rank_subset_iff (isOrd_rank _)).symm.trans (ord_subset_iff (isOrd_rank _) (isOrd_rank _)))
    refine (mem_sUnion_range _).trans <| Iff.trans ?_ (mem_rank_range fun a => embed (f a)).symm
    constructor
    · exact fun h => nn_bind h fun ⟨a, ha⟩ => nn_map (fun
        | .inl h => ⟨a, .inr h⟩
        | .inr e => ⟨a, .inl e⟩) ((step a).1 ha)
    · exact nn_map fun ⟨a, ha⟩ => ⟨a, (step a).2 (nn_intro (ha.elim .inr .inl))⟩

/-- An actual rank envelope at every native tree index. -/
theorem rankCover_W (t : PSet.{u}) : RankCover (rank (embed t)) (W t) :=
  fun X h => (mem_W_iff t X).2 h

/-- Graph sets of rank below a native tree index are, pointwise and negatively, native. -/
theorem native_of_rank_mem (t : PSet.{u}) (X : GSet.{u}) (h : Mem (rank X) (rank (embed t))) :
    ¬¬∃ x : PSet.{u}, x ∈ PSet.Vl t ∧ Equiv X (embed x) :=
  W_native_members ((mem_W_iff t X).2 h)

theorem embed_isOrd {α : PSet.{u}} (hα : PSet.IsOrd α) : IsOrd (embed α) := by
  have tr : ∀ {x : PSet.{u}}, PSet.Trans x → Trans (embed x) := by
    intro x hx K hK K' hK'
    refine Stable.of_nn (embed_readback hK) fun ⟨z, hz, ez⟩ => ?_
    refine Stable.of_nn (embed_readback (Mem.congr_right ez hK')) fun ⟨w, hw, ew⟩ => ?_
    exact Mem.congr_left ew.symm (embed_mem_iff.2 (hx z hz w hw))
  refine ⟨tr hα.trans, fun K hK => ?_⟩
  refine Stable.of_nn (embed_readback hK) fun ⟨z, hz, ez⟩ => ?_
  intro K' hK' K'' hK''
  exact Mem.congr_right ez.symm (tr (hα.mem_trans z hz) K' (Mem.congr_right ez hK') K'' hK'')

/-- At an embedded native ordinal the level is the exact envelope. -/
theorem rankCover_embed_ord {α : PSet.{u}} (hα : PSet.IsOrd α) : RankCover (embed α) (W α) :=
  fun X h => (mem_W_iff α X).2 (Mem.congr_right (rank_equiv_of_isOrd (embed_isOrd hα)).symm h)

/-! ### Successors -/

theorem mem_gsucc_self (κ : GSet.{u}) : Mem κ (Consumer.gsucc κ) :=
  (Consumer.mem_gsucc _ _).2 (nn_intro (.inr (Equiv.refl _)))

theorem mem_gsucc_of_mem {κ β : GSet.{u}} (h : Mem β κ) : Mem β (Consumer.gsucc κ) :=
  (Consumer.mem_gsucc _ _).2 (nn_intro (.inl h))

theorem subset_of_mem_gsucc {κ β : GSet.{u}} (hκ : IsOrd κ) (h : Mem β (Consumer.gsucc κ)) : Subset β κ :=
  fun K hK => Stable.of_nn ((Consumer.mem_gsucc _ _).1 h) fun
    | .inl h => hκ.1 β h K hK
    | .inr e => Mem.congr_right e hK

theorem isOrd_gsucc {κ : GSet.{u}} (hκ : IsOrd κ) : IsOrd (Consumer.gsucc κ) := by
  refine ⟨fun K hK K' hK' => mem_gsucc_of_mem (subset_of_mem_gsucc hκ hK K' hK'), fun K hK => ?_⟩
  refine Stable.of_nn ((Consumer.mem_gsucc _ _).1 hK) fun
    | .inl h => hκ.2 K h
    | .inr e => fun K' hK' K'' hK'' => Mem.congr_right e.symm (hκ.1 K' (Mem.congr_right e hK') K'' hK'')

theorem gsucc_congr {κ κ' : GSet.{u}} (e : Equiv κ κ') : Equiv (Consumer.gsucc κ) (Consumer.gsucc κ') :=
  ext fun _ => (Consumer.mem_gsucc _ _).trans <| .trans
    (nn_congr (or_congr (mem_congr_right e) ⟨fun h => h.trans e, fun h => h.trans e.symm⟩))
    (Consumer.mem_gsucc _ _).symm

/-! ### The powerset history -/

/-- `⟨β, V⟩ ∈ h`. -/
def Edge (h β V : GSet.{u}) : Prop := Mem (opair β V) h

instance {h β V : GSet.{u}} : Stable (Edge h β V) := inferInstanceAs (Stable (Mem _ _))

/-- `h` is a pure total functional graph on `succ κ` whose rows satisfy the powerset recurrence in
membership form, nc4 (3). -/
structure PowHist (κ h : GSet.{u}) : Prop where
  pure : ∀ q, Mem q h → ¬¬∃ β V, Mem β (Consumer.gsucc κ) ∧ Equiv q (opair β V)
  total : ∀ β, Mem β (Consumer.gsucc κ) → ¬¬∃ V, Edge h β V
  func : ∀ β V V', Edge h β V → Edge h β V' → Equiv V V'
  row : ∀ β V, Edge h β V → ∀ X, Mem X V ↔ ¬¬∃ γ W, Mem γ β ∧ Edge h γ W ∧ Subset X W

instance {κ h : GSet.{u}} : Stable (PowHist κ h) :=
  ⟨fun hh => ⟨fun q hq => Stable.dne fun hn => hh fun z => hn (z.pure q hq),
    fun β hβ => Stable.dne fun hn => hh fun z => hn (z.total β hβ),
    fun β V V' h1 h2 => Stable.dne fun hn => hh fun z => hn (z.func β V V' h1 h2),
    fun β V hV X => Stable.dne fun hn => hh fun z => hn (z.row β V hV X)⟩⟩

theorem PowHist.congr {κ κ' h : GSet.{u}} (e : Equiv κ κ') (hh : PowHist κ h) : PowHist κ' h :=
  ⟨fun q hq => nn_map (fun ⟨β, V, hβ, eq⟩ => ⟨β, V, Mem.congr_right (gsucc_congr e) hβ, eq⟩) (hh.pure q hq),
   fun β hβ => hh.total β (Mem.congr_right (gsucc_congr e).symm hβ), hh.func, hh.row⟩

/-- **Exact rows**, nc4 (4): every row of a correct history is the strict rank class. -/
theorem powHist_exact {κ h : GSet.{u}} (hκ : IsOrd κ) (hh : PowHist κ h) :
    ∀ β, Mem β (Consumer.gsucc κ) → ∀ V, Edge h β V → ∀ X, Mem X V ↔ Mem (rank X) β := by
  refine mem_induction (F := fun β => Mem β (Consumer.gsucc κ) → ∀ V, Edge h β V → ∀ X,
    (Mem X V ↔ Mem (rank X) β)) fun β ih hβs V hV X => ?_
  have hβ : IsOrd β := (isOrd_gsucc hκ).mem hβs
  have hγs : ∀ γ, Mem γ β → Mem γ (Consumer.gsucc κ) := fun γ hγ => (isOrd_gsucc hκ).1 β hβs γ hγ
  constructor
  · intro hX
    refine (rank_mem_iff hβ).2 ?_
    refine nn_map (fun ⟨γ, W, hγ, hW, hXW⟩ => ⟨γ, hγ, fun Y hY => ?_⟩) ((hh.row β V hV X).1 hX)
    exact (ih γ hγ (hγs γ hγ) W hW Y).1 (hXW Y hY)
  · intro hX
    refine Stable.of_nn (hh.total (rank X) (hγs _ hX)) fun ⟨W, hW⟩ => ?_
    refine (hh.row β V hV X).2 (nn_intro ⟨rank X, W, hX, hW, fun Y hY => ?_⟩)
    exact (ih _ hX (hγs _ hX) W hW Y).2 (rank_mem hY)

/-- Correct histories agree on overlapping indices. -/
theorem powHist_overlap {κ κ' h h' β V V' : GSet.{u}} (hκ : IsOrd κ) (hκ' : IsOrd κ')
    (hh : PowHist κ h) (hh' : PowHist κ' h') (hβ : Mem β (Consumer.gsucc κ)) (hβ' : Mem β (Consumer.gsucc κ'))
    (hV : Edge h β V) (hV' : Edge h' β V') : Equiv V V' :=
  ext fun X => (powHist_exact hκ hh β hβ V hV X).trans (powHist_exact hκ' hh' β hβ' V' hV' X).symm

/-- The terminal row is the strict rank class at `κ`, hence an envelope. -/
theorem powHist_top {κ h : GSet.{u}} (hκ : IsOrd κ) (hh : PowHist κ h) :
    ¬¬∃ V, ∀ X, Mem X V ↔ Mem (rank X) κ :=
  nn_map (fun ⟨V, hV⟩ => ⟨V, powHist_exact hκ hh κ (mem_gsucc_self κ) V hV⟩) (hh.total κ (mem_gsucc_self κ))

theorem rankCover_of_powHist {κ h : GSet.{u}} (hκ : IsOrd κ) (hh : PowHist κ h) :
    ¬¬∃ E, RankCover κ E :=
  nn_map (fun ⟨V, hV⟩ => ⟨V, fun X hX => (hV X).2 hX⟩) (powHist_top hκ hh)

/-! ### The history from one envelope -/

/-- The row at `β`, cut from the envelope by rank. -/
def row (E β : GSet.{u}) : GSet.{u} := sep (fun X => Mem (rank X) β) E

theorem row_resp (β : GSet.{u}) : ∀ K K' : GSet.{u}, Equiv K K' → Mem (rank K) β → Mem (rank K') β :=
  fun _ _ e h => Mem.congr_left (rank_congr e) h

theorem mem_row {κ E β X : GSet.{u}} (hE : RankCover κ E) (hβ : Subset β κ) :
    Mem X (row E β) ↔ Mem (rank X) β :=
  (mem_sep _ E (row_resp β)).trans ⟨And.right, fun h => ⟨hE X (hβ _ h), h⟩⟩

theorem row_congr {E β β' : GSet.{u}} (e : Equiv β β') : Equiv (row E β) (row E β') :=
  ext fun _ => (mem_sep _ E (row_resp β)).trans
    ((and_congr Iff.rfl (mem_congr_right e)).trans (mem_sep _ E (row_resp β')).symm)

/-- The history: the rows over the literal predecessors of `succ κ`. -/
def hist (κ E : GSet.{u}) : GSet.{u} :=
  range fun i : {i : (Consumer.gsucc κ).A // (Consumer.gsucc κ).R i (Consumer.gsucc κ).r} =>
    opair ((Consumer.gsucc κ).at' i.1) (row E ((Consumer.gsucc κ).at' i.1))

theorem edge_hist {κ E β V : GSet.{u}} (h : Edge (hist κ E) β V) :
    ¬¬∃ β', Mem β' (Consumer.gsucc κ) ∧ Equiv β β' ∧ Equiv V (row E β') :=
  nn_map (fun ⟨i, e⟩ => ⟨_, at'_mem i.2, (opair_inj _ _ e).1, (opair_inj _ _ e).2⟩) ((mem_range _).1 h)

theorem edge_hist_exact {κ E β V : GSet.{u}} (hκ : IsOrd κ) (hE : RankCover κ E)
    (h : Edge (hist κ E) β V) : ∀ X, Mem X V ↔ Mem (rank X) β := fun X => by
  refine ⟨fun hX => ?_, fun hX => ?_⟩
  · refine Stable.of_nn (edge_hist h) fun ⟨β', hβ', eβ, eV⟩ => ?_
    exact Mem.congr_right eβ.symm ((mem_row hE (subset_of_mem_gsucc hκ hβ')).1 (Mem.congr_right eV hX))
  · refine Stable.of_nn (edge_hist h) fun ⟨β', hβ', eβ, eV⟩ => ?_
    exact Mem.congr_right eV.symm ((mem_row hE (subset_of_mem_gsucc hκ hβ')).2 (Mem.congr_right eβ hX))

/-- **One envelope constructs the entire history.** -/
theorem powHist_hist {κ E : GSet.{u}} (hκ : IsOrd κ) (hE : RankCover κ E) : PowHist κ (hist κ E) := by
  refine ⟨fun q hq => ?_, fun β hβ => ?_, fun β V V' h1 h2 => ?_, fun β V hV X => ?_⟩
  · exact nn_map (fun ⟨i, e⟩ => ⟨_, _, at'_mem i.2, e⟩) ((mem_range _).1 hq)
  · refine nn_map (fun ⟨i, hi, e⟩ => ⟨row E ((Consumer.gsucc κ).at' i), ?_⟩) hβ
    exact (mem_range _).2 (nn_intro ⟨⟨i, hi⟩, opair_congr _ _ e (Equiv.refl _)⟩)
  · exact ext fun X => (edge_hist_exact hκ hE h1 X).trans (edge_hist_exact hκ hE h2 X).symm
  · have hβs : Mem β (Consumer.gsucc κ) :=
      Stable.of_nn (edge_hist hV) fun ⟨β', hβ', eβ, _⟩ => Mem.congr_left eβ.symm hβ'
    have hβ : IsOrd β := (isOrd_gsucc hκ).mem hβs
    refine (edge_hist_exact hκ hE hV X).trans ((rank_mem_iff hβ).trans ⟨fun h => ?_, fun h => ?_⟩)
    · refine nn_bind h fun ⟨γ, hγ, hY⟩ => ?_
      have hγs : Mem γ (Consumer.gsucc κ) := (isOrd_gsucc hκ).1 β hβs γ hγ
      refine nn_map (fun ⟨W, hW⟩ => ⟨γ, W, hγ, hW, fun Y hY' => ?_⟩) ((powHist_hist_total hκ hE) γ hγs)
      exact (edge_hist_exact hκ hE hW Y).2 (hY Y hY')
    · exact nn_map (fun ⟨γ, W, hγ, hW, hXW⟩ => ⟨γ, hγ, fun Y hY =>
        (edge_hist_exact hκ hE hW Y).1 (hXW Y hY)⟩) h
where
  powHist_hist_total {κ E : GSet.{u}} (_ : IsOrd κ) (_ : RankCover κ E) :
      ∀ β, Mem β (Consumer.gsucc κ) → ¬¬∃ V, Edge (hist κ E) β V := fun _ hβ =>
    nn_map (fun ⟨i, hi, e⟩ => ⟨row E ((Consumer.gsucc κ).at' i),
      (mem_range _).2 (nn_intro ⟨⟨i, hi⟩, opair_congr _ _ e (Equiv.refl _)⟩)⟩) hβ

/-- **nc4 (\*)**: a history exists negatively iff a rank envelope does. -/
theorem powHist_iff_rankCover {κ : GSet.{u}} (hκ : IsOrd κ) :
    (¬¬∃ h, PowHist κ h) ↔ ¬¬∃ E, RankCover κ E :=
  ⟨fun h => nn_bind h fun ⟨_, hh⟩ => rankCover_of_powHist hκ hh,
   nn_map fun ⟨E, hE⟩ => ⟨hist κ E, powHist_hist hκ hE⟩⟩

/-- Zero law: at an index with no members the exact row is empty. -/
theorem exact_zero {β V : GSet.{u}} (hV : ∀ X, Mem X V ↔ Mem (rank X) β) (h0 : ∀ γ, ¬ Mem γ β) :
    ∀ X, ¬ Mem X V := fun X hX => h0 _ ((hV X).1 hX)

/-- Successor law: the exact row at `succ β` is the full graph powerset of the exact row at `β`. -/
theorem exact_succ {β V V' : GSet.{u}} (hβ : IsOrd β) (hV : ∀ X, Mem X V ↔ Mem (rank X) β)
    (hV' : ∀ X, Mem X V' ↔ Mem (rank X) (Consumer.gsucc β)) : Equiv V' (powerset V) := by
  refine ext fun X => (hV' X).trans <| .trans ((Consumer.mem_gsucc _ _).trans
    ((ord_subset_iff (isOrd_rank X) hβ).symm.trans (rank_subset_iff hβ))) ?_
  exact Iff.trans ⟨fun h Y hY => (hV Y).2 (h Y hY), fun h Y hY => (hV Y).1 (h Y hY)⟩ (mem_powerset _).symm

/-- The positive case: at every native tree index the history exists. -/
theorem powHist_native (t : PSet.{u}) : ¬¬∃ h, PowHist (rank (embed t)) h :=
  (powHist_iff_rankCover (isOrd_rank _)).2 (nn_intro ⟨W t, rankCover_W t⟩)

theorem powHist_embed_ord {α : PSet.{u}} (hα : PSet.IsOrd α) : ¬¬∃ h, PowHist (embed α) h :=
  (powHist_iff_rankCover (embed_isOrd hα)).2 (nn_intro ⟨W α, rankCover_embed_ord hα⟩)

/-- info: 'GSet.Envelope.native_envelope_collapses' does not depend on any axioms -/
#guard_msgs in #print axioms native_envelope_collapses
/-- info: 'GSet.Envelope.rank_mem_iff' does not depend on any axioms -/
#guard_msgs in #print axioms rank_mem_iff
/-- info: 'GSet.Envelope.mem_W_iff' does not depend on any axioms -/
#guard_msgs in #print axioms mem_W_iff
/-- info: 'GSet.Envelope.native_of_rank_mem' does not depend on any axioms -/
#guard_msgs in #print axioms native_of_rank_mem
/-- info: 'GSet.Envelope.powHist_exact' does not depend on any axioms -/
#guard_msgs in #print axioms powHist_exact
/-- info: 'GSet.Envelope.powHist_hist' does not depend on any axioms -/
#guard_msgs in #print axioms powHist_hist
/-- info: 'GSet.Envelope.powHist_iff_rankCover' does not depend on any axioms -/
#guard_msgs in #print axioms powHist_iff_rankCover
/-- info: 'GSet.Envelope.exact_succ' does not depend on any axioms -/
#guard_msgs in #print axioms exact_succ
/-- info: 'GSet.Envelope.powHist_native' does not depend on any axioms -/
#guard_msgs in #print axioms powHist_native

/-! ### Prefix Collection, semantically -/

/-- Ordinary Collection for the fixed matrix "correct history through `γ`", over the lower cone of
`κ`, nc4 (14). Semantic: no source formula is claimed. -/
def PrefixCollection (κ : GSet.{u}) : Prop :=
  ∀ β, Mem β (Consumer.gsucc κ) → (∀ γ, Mem γ β → ¬¬∃ h, PowHist γ h) →
    ¬¬∃ B, ∀ γ, Mem γ β → ¬¬∃ h, Mem h B ∧ PowHist γ h

/-- The restriction of a history to the indices in `succ γ`. -/
def restrict (h γ : GSet.{u}) : GSet.{u} :=
  sep (fun q => ¬¬∃ δ V, Mem δ (Consumer.gsucc γ) ∧ Equiv q (opair δ V)) h

theorem restrict_resp (γ : GSet.{u}) : ∀ K K' : GSet.{u}, Equiv K K' →
    (¬¬∃ δ V, Mem δ (Consumer.gsucc γ) ∧ Equiv K (opair δ V)) →
    ¬¬∃ δ V, Mem δ (Consumer.gsucc γ) ∧ Equiv K' (opair δ V) :=
  fun _ _ e => nn_map fun ⟨δ, V, hδ, e'⟩ => ⟨δ, V, hδ, e.symm.trans e'⟩

theorem edge_restrict {h γ δ V : GSet.{u}} :
    Edge (restrict h γ) δ V ↔ Edge h δ V ∧ Mem δ (Consumer.gsucc γ) := by
  refine (mem_sep _ h (restrict_resp γ)).trans (and_congr Iff.rfl ⟨fun hn => ?_, fun hδ => nn_intro ⟨δ, V, hδ, Equiv.refl _⟩⟩)
  exact Stable.of_nn hn fun ⟨_, _, hδ', e⟩ => Mem.congr_left (opair_inj _ _ e).1.symm hδ'

/-- A restriction of a correct history to an index below its top is a correct history. -/
theorem powHist_restrict {κ h γ : GSet.{u}} (hκ : IsOrd κ) (hh : PowHist κ h)
    (hγ : Mem γ (Consumer.gsucc κ)) : PowHist γ (restrict h γ) := by
  have hγo : IsOrd γ := (isOrd_gsucc hκ).mem hγ
  have up : ∀ δ, Mem δ (Consumer.gsucc γ) → Mem δ (Consumer.gsucc κ) := fun δ hδ =>
    Stable.of_nn ((Consumer.mem_gsucc _ _).1 hδ) fun
      | .inl h => (isOrd_gsucc hκ).1 γ hγ δ h
      | .inr e => Mem.congr_left e.symm hγ
  refine ⟨fun q hq => ?_, fun δ hδ => ?_, fun δ V V' h1 h2 => hh.func δ V V' (edge_restrict.1 h1).1 (edge_restrict.1 h2).1,
    fun δ V hV X => ?_⟩
  · exact ((mem_sep _ h (restrict_resp γ)).1 hq).2
  · exact nn_map (fun ⟨V, hV⟩ => ⟨V, edge_restrict.2 ⟨hV, hδ⟩⟩) (hh.total δ (up δ hδ))
  · have hδ := (edge_restrict.1 hV).2
    refine (hh.row δ V (edge_restrict.1 hV).1 X).trans (nn_congr ⟨fun ⟨γ', W, hγ', hW, hXW⟩ => ?_,
      fun ⟨γ', W, hγ', hW, hXW⟩ => ⟨γ', W, hγ', (edge_restrict.1 hW).1, hXW⟩⟩)
    exact ⟨γ', W, hγ', edge_restrict.2 ⟨hW, (isOrd_gsucc hγo).1 δ hδ γ' hγ'⟩, hXW⟩

/-- A full history supplies the prefix collections: the range of its restrictions over the literal
predecessors of the source. -/
theorem prefixCollection_of_powHist {κ h : GSet.{u}} (hκ : IsOrd κ) (hh : PowHist κ h) :
    PrefixCollection κ := by
  intro β hβ _
  refine nn_intro ⟨range fun i : {i : β.A // β.R i β.r} => restrict h (β.at' i.1), fun γ hγ => ?_⟩
  refine nn_map (fun ⟨i, hi, e⟩ => ⟨restrict h (β.at' i), (mem_range _).2 (nn_intro ⟨⟨i, hi⟩, Equiv.refl _⟩), ?_⟩) hγ
  have hi' : Mem (β.at' i) (Consumer.gsucc κ) := (isOrd_gsucc hκ).1 β hβ _ (at'_mem hi)
  exact (powHist_restrict hκ hh hi').congr e.symm

/-- The envelope assembled from a collecting set of predecessor histories: the terminal row of a
correct history through `γ` lies in `⋃⋃⋃B`, so every set of rank `γ` is a subset of `⋃⋃⋃⋃B`. -/
theorem rankCover_of_collected {β B : GSet.{u}}
    (hB : ∀ γ, Mem γ β → ¬¬∃ h, Mem h B ∧ PowHist γ h) :
    RankCover β (powerset (sUnion (sUnion (sUnion (sUnion B))))) := by
  intro X hX
  refine Stable.of_nn (hB _ hX) fun ⟨h, hhB, hh⟩ => ?_
  refine Stable.of_nn (hh.total (rank X) (mem_gsucc_self _)) fun ⟨V, hV⟩ => ?_
  have hex := powHist_exact (isOrd_rank X) hh (rank X) (mem_gsucc_self _) V hV
  have h1 : Mem (opair (rank X) V) (sUnion B) := (mem_sUnion _).2 (nn_intro ⟨h, hhB, hV⟩)
  have h2 : Mem (pair (rank X) V) (sUnion (sUnion B)) :=
    (mem_sUnion _).2 (nn_intro ⟨_, h1, mem_pair_right _ _⟩)
  have h3 : Mem V (sUnion (sUnion (sUnion B))) := (mem_sUnion _).2 (nn_intro ⟨_, h2, mem_pair_right _ _⟩)
  exact (mem_powerset _).2 fun Y hY => (mem_sUnion _).2 (nn_intro ⟨V, h3, (hex Y).2 (rank_mem hY)⟩)

/-- **nc4 (18)**: the history at `κ` exists negatively iff prefix Collection holds over its lower
cone. -/
theorem powHist_iff_prefixCollection {κ : GSet.{u}} (hκ : IsOrd κ) :
    (¬¬∃ h, PowHist κ h) ↔ PrefixCollection κ := by
  constructor
  · exact fun h hβ hβs hpre => Stable.of_nn h fun ⟨_, hh⟩ => prefixCollection_of_powHist hκ hh hβ hβs hpre
  · intro pc
    have all : ∀ β, Mem β (Consumer.gsucc κ) → ¬¬∃ h, PowHist β h := by
      refine mem_induction (F := fun β => Mem β (Consumer.gsucc κ) → ¬¬∃ h, PowHist β h) fun β ih hβ => ?_
      have hβo : IsOrd β := (isOrd_gsucc hκ).mem hβ
      refine nn_bind (pc β hβ fun γ hγ => ih γ hγ ((isOrd_gsucc hκ).1 β hβ γ hγ)) fun ⟨B, hB⟩ => ?_
      exact nn_intro ⟨_, powHist_hist hβo (rankCover_of_collected hB)⟩
    exact all κ (mem_gsucc_self κ)

/-- info: 'GSet.Envelope.powHist_iff_prefixCollection' does not depend on any axioms -/
#guard_msgs in #print axioms powHist_iff_prefixCollection

end GSet.Envelope
