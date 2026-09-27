import ConZF.RankEnvelope
import ConZF.DecodeSpectrum
/-!
The native/graph boundary at `ω` (nc5 closeout). No envelope and no barrier is constructed here.

* **Rank and nativity** (reviewer probe, integrated): the embedding commutes with rank
  (`embed_rank`); a graph set is negatively native iff its graph rank is (`native_iff_native_rank`);
  an exact rank row at an ordinal `κ` has rank `κ` and is native iff `κ` is (`rank_exact_row`,
  `native_exact_row_iff`). Representing the rank is as hard as representing the object.
* **The least-image bridge at `ω`.** For a **native** domain `a`, an injection relation
  `embed a → embed ω` is equivalent to a native pure injection `a → ω` (`injRel_embed_omega_iff`).
  From the relation, each input keeps its `∈`-minimal successful label in `ω`, found by the native
  `exists_minimal` on a separated set of labels and unique by ordinal trichotomy; the native graph is
  a Separation inside `a × ω`. All witnesses stay negative. Hence an embedded native ordinal lies in
  `relHartogs (embed ω)` iff it injects natively into `ω` (`embed_mem_relHartogs_iff`).
* **The native barrier equivalences**, all existentials double-negated: a native barrier at `ω`
  exists iff `κ = relHartogs (embed ω)` is native iff `κ` has a native rank envelope
  (`barrier_iff_native`, `native_iff_native_envelope`), the native representative being the explicit
  Separation `nativeSubset b κ`; each implies the arbitrary graph-envelope target, whose converse
  is not established.
* **The representative-bound calibration**, conditional on a supplied envelope: with the concrete
  filtered carrier of its pointed subgraphs of rank in `κ`, a native bound on their native
  representatives is equivalent to a native barrier at `ω` (`repBound_iff_barrier`), the barrier
  being the native rank of the bound. Also the canonical cut `row E κ` has rank `κ` and is native
  iff a barrier exists (`native_cut_iff_barrier`). None of this produces the bound.
-/
universe u

namespace GSet.Bridge
open PSet.OrdDecode Envelope

/-! ### Rank and nativity -/

theorem embed_rank : ∀ t : PSet.{u}, Equiv (rank (embed t)) (embed (PSet.rank t))
  | ⟨A, f⟩ => by
    refine ext fun K => ?_
    change Mem K (rank (range fun a : A => embed (f a))) ↔ _
    refine (mem_rank_range _).trans ⟨fun hk => ?_, fun hk => ?_⟩
    · refine nn_bind hk fun ⟨a, ha⟩ => ?_
      rcases ha with ea | ha
      · exact Mem.congr_left (ea.trans (embed_rank (f a))).symm
          (embed_mem_iff.2 (PSet.mem_rank.2 (nn_intro ⟨a, PSet.self_mem_succ (PSet.rank (f a))⟩)))
      · refine Stable.of_nn (embed_readback (Mem.congr_right (embed_rank (f a)) ha)) fun ⟨z, hz, ez⟩ => ?_
        exact Mem.congr_left ez.symm (embed_mem_iff.2 (PSet.mem_rank.2 (nn_intro ⟨a, PSet.mem_succ_of_mem hz⟩)))
    · refine nn_bind (embed_readback hk) fun ⟨z, hz, ez⟩ => ?_
      refine nn_bind (PSet.mem_rank.1 hz) fun ⟨a, ha⟩ => ?_
      refine nn_map (fun hm => ?_) (PSet.mem_succ.1 ha)
      rcases hm with hm | em
      · exact ⟨a, Or.inr (Mem.congr_right (embed_rank (f a)).symm (Mem.congr_left ez.symm (embed_mem_iff.2 hm)))⟩
      · exact ⟨a, Or.inl (ez.trans ((embed_congr em).trans (embed_rank (f a)).symm))⟩

/-- Negatively having a native representative. -/
def Native (X : GSet.{u}) : Prop := ¬¬∃ x : PSet.{u}, Equiv X (embed x)

instance {X : GSet.{u}} : Stable (Native X) := inferInstanceAs (Stable (¬_))

theorem native_iff_native_rank (X : GSet.{u}) : Native X ↔ Native (rank X) := by
  constructor
  · exact nn_map fun ⟨x, ex⟩ => ⟨PSet.rank x, (rank_congr ex).trans (embed_rank x)⟩
  · intro hn
    refine nn_bind hn fun ⟨a, ea⟩ => ?_
    have er : Equiv (rank X) (rank (embed a)) := (rank_rank X).symm.trans (rank_congr ea)
    have hm : Mem (rank X) (rank (embed (PSet.succ a))) :=
      Mem.congr_left er.symm (rank_mem (embed_mem_iff.2 (PSet.self_mem_succ a)))
    exact nn_map (fun ⟨x, _, ex⟩ => ⟨x, ex⟩) (native_of_rank_mem _ _ hm)

theorem rank_exact_row {κ L : GSet.{u}} (hκ : IsOrd κ) (hL : ∀ X, Mem X L ↔ Mem (rank X) κ) :
    Equiv (rank L) κ := by
  have sub : Subset (rank L) κ := (rank_subset_iff hκ).2 fun X hX => (hL X).1 hX
  refine ext fun β => ⟨sub β, fun hβ => ?_⟩
  have er := rank_equiv_of_isOrd (hκ.mem hβ)
  exact Mem.congr_left er (rank_mem ((hL β).2 (Mem.congr_left er.symm hβ)))

theorem native_exact_row_iff {κ L : GSet.{u}} (hκ : IsOrd κ) (hL : ∀ X, Mem X L ↔ Mem (rank X) κ) :
    Native L ↔ Native κ := by
  refine (native_iff_native_rank L).trans ?_
  have er := rank_exact_row hκ hL
  exact ⟨nn_map fun ⟨x, ex⟩ => ⟨x, er.symm.trans ex⟩, nn_map fun ⟨x, ex⟩ => ⟨x, er.trans ex⟩⟩

theorem embed_isOrd_iff (α : PSet.{u}) : IsOrd (embed α) ↔ PSet.IsOrd α := by
  refine ⟨fun h => ⟨fun y hy z hz => ?_, fun y hy z hz w hw => ?_⟩, embed_isOrd⟩
  · exact embed_mem_iff.1 (h.1 _ (embed_mem_iff.2 hy) _ (embed_mem_iff.2 hz))
  · exact embed_mem_iff.1 (h.2 _ (embed_mem_iff.2 hy) _ (embed_mem_iff.2 hz) _ (embed_mem_iff.2 hw))

/-! ### The least-image bridge at `ω` -/

/-- `y ∈ ω` is a successful label for the native input `x` under `F`. -/
def Label (F : GSet.{u} → (embed PSet.omega.{u}).A → Prop) (x y : PSet.{u}) : Prop :=
  ¬¬∃ v, (embed PSet.omega.{u}).R v (embed PSet.omega).r ∧
    Equiv ((embed PSet.omega.{u}).at' v) (embed y) ∧ F (embed x) v

instance {F : GSet.{u} → (embed PSet.omega.{u}).A → Prop} {x y : PSet.{u}} : Stable (Label F x y) :=
  inferInstanceAs (Stable (¬_))

/-- The successful labels of `x`, as a native set. -/
def labels (F : GSet.{u} → (embed PSet.omega.{u}).A → Prop) (x : PSet.{u}) : PSet.{u} :=
  PSet.sep (Label F x) PSet.omega

theorem label_resp_right {F : GSet.{u} → (embed PSet.omega.{u}).A → Prop} (x : PSet.{u}) :
    ∀ y y' : PSet.{u}, y ≈ y' → Label F x y → Label F x y' :=
  fun _ _ e => nn_map fun ⟨v, hv, ev, hF⟩ => ⟨v, hv, ev.trans (embed_congr e), hF⟩

theorem label_resp_left {F : GSet.{u} → (embed PSet.omega.{u}).A → Prop}
    (resp : ∀ ξ ξ' a, Equiv ξ ξ' → F ξ a → F ξ' a) {x x' y : PSet.{u}} (e : x ≈ x')
    (h : Label F x y) : Label F x' y :=
  nn_map (fun ⟨v, hv, ev, hF⟩ => ⟨v, hv, ev, resp _ _ _ (embed_congr e) hF⟩) h

theorem mem_labels {F : GSet.{u} → (embed PSet.omega.{u}).A → Prop} {x y : PSet.{u}} :
    y ∈ labels F x ↔ y ∈ PSet.omega ∧ Label F x y :=
  PSet.mem_sep (label_resp_right x)

/-- `y` is the `∈`-least successful label of `x`. -/
def MinLabel (F : GSet.{u} → (embed PSet.omega.{u}).A → Prop) (x y : PSet.{u}) : Prop :=
  y ∈ labels F x ∧ ∀ w, w ∈ y → ¬ w ∈ labels F x

instance {F : GSet.{u} → (embed PSet.omega.{u}).A → Prop} {x y : PSet.{u}} : Stable (MinLabel F x y) :=
  inferInstanceAs (Stable (_ ∧ _))

theorem minLabel_unique {F : GSet.{u} → (embed PSet.omega.{u}).A → Prop} {x y y' : PSet.{u}}
    (h : MinLabel F x y) (h' : MinLabel F x y') : y ≈ y' := by
  have hy : PSet.IsOrd y := PSet.isOrd_omega.mem (mem_labels.1 h.1).1
  have hy' : PSet.IsOrd y' := PSet.isOrd_omega.mem (mem_labels.1 h'.1).1
  exact Stable.of_nn (hy.trichotomy hy') fun
    | .inl hm => (h'.2 y hm h.1).elim
    | .inr (.inl e) => e
    | .inr (.inr hm) => (h.2 y' hm h'.1).elim

/-- The native injection graph: the pairs `⟨x, y⟩ ∈ a × ω` with `y` the least label of `x`. -/
def leastGraph (F : GSet.{u} → (embed PSet.omega.{u}).A → Prop) (a : PSet.{u}) : PSet.{u} :=
  PSet.sep (fun q => ¬¬∃ x y, MinLabel F x y ∧ q ≈ PSet.pair x y) (product a PSet.omega)

theorem mem_leastGraph {F : GSet.{u} → (embed PSet.omega.{u}).A → Prop} {a q : PSet.{u}} :
    q ∈ leastGraph F a ↔ q ∈ product a PSet.omega ∧ ¬¬∃ x y, MinLabel F x y ∧ q ≈ PSet.pair x y :=
  PSet.mem_sep fun _ _ e => nn_map fun ⟨x, y, hm, eq⟩ => ⟨x, y, hm, e.symm.trans eq⟩

theorem minLabel_congr {F : GSet.{u} → (embed PSet.omega.{u}).A → Prop}
    (resp : ∀ ξ ξ' a, Equiv ξ ξ' → F ξ a → F ξ' a) {x x' y : PSet.{u}} (e : x ≈ x')
    (h : MinLabel F x y) : MinLabel F x' y := by
  have tr : ∀ {x x' w : PSet.{u}}, x ≈ x' → w ∈ labels F x → w ∈ labels F x' := fun e hw =>
    mem_labels.2 ⟨(mem_labels.1 hw).1, label_resp_left resp e (mem_labels.1 hw).2⟩
  exact ⟨tr e h.1, fun w hw hw' => h.2 w hw (tr e.symm hw')⟩

theorem left_mem_of_leastGraph {F : GSet.{u} → (embed PSet.omega.{u}).A → Prop} {a i v : PSet.{u}}
    (h : PSet.pair i v ∈ leastGraph F a) : i ∈ a :=
  Stable.of_nn (mem_product.1 (mem_leastGraph.1 h).1) fun ⟨_, _, hi', _, e'⟩ =>
    (PSet.mem_congr_left (PSet.pair_inj e').1).2 hi'

/-- **From an injection relation to a native injection**, on a native domain. -/
theorem emb_of_injRel_embed {a : PSet.{u}} (h : InjRel (embed a) (embed PSet.omega.{u})) : Emb a PSet.omega := by
  refine Stable.of_nn h fun ⟨F, hF⟩ => ?_
  refine nn_intro ⟨leastGraph F a, ⟨fun q hq => ?_, fun i hi => ?_, fun i v v' hv hv' => ?_⟩,
    fun i j v w hiv hjw evw => ?_⟩
  · exact mem_product.1 (mem_leastGraph.1 hq).1
  · -- totality: a successful label exists, hence a least one
    refine Stable.of_nn (hF.total (embed i) (embed_mem_iff.2 hi)) fun ⟨v, hv, hFv⟩ => ?_
    refine Stable.of_nn (embed_readback (at'_mem hv)) fun ⟨y, hy, ey⟩ => ?_
    have hyl : y ∈ labels F i := mem_labels.2 ⟨hy, nn_intro ⟨v, hv, ey, hFv⟩⟩
    refine nn_map (fun ⟨y', hy', hmin⟩ => ⟨y', mem_leastGraph.2 ⟨?_, nn_intro ⟨i, y', ⟨hy', hmin⟩, PSet.Equiv.refl _⟩⟩⟩)
      (PSet.exists_minimal (labels F i) y hyl)
    exact mem_product.2 (nn_intro ⟨i, y', hi, (mem_labels.1 hy').1, PSet.Equiv.refl _⟩)
  · refine Stable.of_nn (mem_leastGraph.1 hv).2 fun ⟨x, y, hm, e⟩ => ?_
    refine Stable.of_nn (mem_leastGraph.1 hv').2 fun ⟨x', y', hm', e'⟩ => ?_
    have ⟨ex, ev⟩ := PSet.pair_inj e
    have ⟨ex', ev'⟩ := PSet.pair_inj e'
    have hm2 : MinLabel F x y' := minLabel_congr (F := F) (fun ξ ξ' a e => hF.resp_left (ξ := ξ) (ξ' := ξ') (a := a) e) (ex'.symm.trans ex) hm'
    exact ev.trans ((minLabel_unique hm hm2).trans ev'.symm)
  · refine Stable.of_nn (mem_leastGraph.1 hiv).2 fun ⟨x, y, hm, e⟩ => ?_
    refine Stable.of_nn (mem_leastGraph.1 hjw).2 fun ⟨x', y', hm', e'⟩ => ?_
    have ⟨ex, ev⟩ := PSet.pair_inj e
    have ⟨ex', ev'⟩ := PSet.pair_inj e'
    have eyy : y ≈ y' := ev.symm.trans (evw.trans ev')
    refine Stable.of_nn (mem_labels.1 hm.1).2 fun ⟨u, hu, eu, hFu⟩ => ?_
    refine Stable.of_nn (mem_labels.1 hm'.1).2 fun ⟨u', _, eu', hFu'⟩ => ?_
    have hFu'' : F (embed x') u := hF.resp_right (eu'.trans ((embed_congr eyy.symm).trans eu.symm)) hFu'
    have hx : x ∈ a := (PSet.mem_congr_left ex).1 (left_mem_of_leastGraph hiv)
    have hx' : x' ∈ a := (PSet.mem_congr_left ex').1 (left_mem_of_leastGraph hjw)
    have exx : Equiv (embed x) (embed x') :=
      hF.inv_unique (embed_mem_iff.2 hx) (embed_mem_iff.2 hx') hFu hFu''
    exact ex.trans (((embed_equiv_iff x x').1 exx).trans ex'.symm)

/-- **From a native injection to an injection relation**: relate `embed x` to every vertex
representing its native image. -/
theorem injRel_embed_of_emb {a : PSet.{u}} (h : Emb a PSet.omega.{u}) : InjRel (embed a) (embed PSet.omega) := by
  refine nn_map (fun ⟨f, hf⟩ => ⟨fun ξ v => ¬¬∃ x y, x ∈ a ∧ Equiv ξ (embed x) ∧ PSet.pair x y ∈ f ∧
    Equiv (embed y) ((embed PSet.omega).at' v), ⟨fun _ _ => inferInstance, ?_, ?_, ?_, ?_⟩⟩) h
  · exact fun e => nn_map fun ⟨x, y, hx, ex, hp, ey⟩ => ⟨x, y, hx, e.symm.trans ex, hp, ey⟩
  · exact fun e => nn_map fun ⟨x, y, hx, ex, hp, ey⟩ => ⟨x, y, hx, ex, hp, ey.trans e⟩
  · intro ξ hξ
    refine nn_bind (embed_readback hξ) fun ⟨x, hx, ex⟩ => ?_
    refine nn_bind (hf.1.2.1 x hx) fun ⟨y, hp⟩ => ?_
    have hy : Mem (embed y) (embed PSet.omega) := embed_mem_iff.2 (map_edge_typed hf.1 hp).2
    exact nn_map (fun ⟨v, hv, ev⟩ => ⟨v, hv, nn_intro ⟨x, y, hx, ex, hp, ev⟩⟩) hy
  · intro ξ ξ' v _ _ h1 h2
    refine Stable.of_nn h1 fun ⟨x, y, _, ex, hp, ey⟩ => Stable.of_nn h2 fun ⟨x', y', _, ex', hp', ey'⟩ => ?_
    have eyy : y ≈ y' := (embed_equiv_iff y y').1 (ey.trans ey'.symm)
    exact ex.trans ((embed_congr (hf.2 x x' y y' hp hp' eyy)).trans ex'.symm)

/-- **The bridge at `ω`**, for native domains. -/
theorem injRel_embed_omega_iff (a : PSet.{u}) : InjRel (embed a) (embed PSet.omega.{u}) ↔ Emb a PSet.omega :=
  ⟨emb_of_injRel_embed, injRel_embed_of_emb⟩

/-- An embedded native ordinal lies in the relational Hartogs bound of `embed ω` iff it injects
natively into `ω`. -/
theorem embed_mem_relHartogs_iff (α : PSet.{u}) :
    Mem (embed α) (relHartogs (embed PSet.omega.{u})) ↔ PSet.IsOrd α ∧ Emb α PSet.omega :=
  mem_relHartogs.trans (and_congr (embed_isOrd_iff α) (injRel_embed_omega_iff α))

/-! ### The native barrier equivalences at `ω` -/

/-- `κ = relHartogs (embed ω)`. -/
def κ : GSet.{u} := relHartogs (embed PSet.omega)

theorem κ_ord : IsOrd κ.{u} := isOrd_relHartogs _

/-- A native barrier at `ω`, negatively. -/
def NativeBarrier : Prop := ¬¬∃ b : PSet.{u}, Barrier (fun _ => True) PSet.omega b

theorem not_emb_of_barrier {b : PSet.{u}} (hb : Barrier (fun _ => True) PSet.omega b) : ¬ Emb b PSet.omega :=
  fun h => h fun ⟨f, hf⟩ => hb.2 f trivial hf

/-- A native barrier gives an explicit native representative of `κ`: the members of `b` that embed
into `κ`. -/
theorem native_of_barrier {b : PSet.{u}} (hb : Barrier (fun _ => True) PSet.omega b) :
    Equiv (embed (nativeSubset b κ)) κ := by
  refine nativeSubset_read fun β hβ => ?_
  have hbo : IsOrd (embed b) := embed_isOrd hb.1
  have hnot : ¬ Mem (embed b) κ := fun h => not_emb_of_barrier hb ((embed_mem_relHartogs_iff b).1 h).2
  refine Stable.of_nn (κ_ord.trichotomy hbo) fun
    | .inl h => hbo.1 _ h β hβ
    | .inr (.inl e) => Mem.congr_right e hβ
    | .inr (.inr h) => (hnot h).elim

theorem barrier_of_native {k : PSet.{u}} (e : Equiv (embed k) κ) : Barrier (fun _ => True) PSet.omega k := by
  refine ⟨(embed_isOrd_iff k).1 (κ_ord.congr e.symm), fun f _ hf => ?_⟩
  exact not_injRel_relHartogs _ (InjRel.congr_left e (injRel_embed_of_emb (nn_intro ⟨f, hf⟩)))

theorem barrier_iff_native : NativeBarrier.{u} ↔ Native κ.{u} :=
  ⟨nn_map fun ⟨_, hb⟩ => ⟨_, (native_of_barrier hb).symm⟩,
   nn_map fun ⟨k, ek⟩ => ⟨k, barrier_of_native ek.symm⟩⟩

/-- A native representative of `κ` gives the native envelope `embed (Vl k)`, and conversely a native
envelope collapses `κ`. -/
theorem native_iff_native_envelope : Native κ.{u} ↔ ¬¬∃ B : PSet.{u}, RankCover κ (embed B) := by
  constructor
  · refine nn_map fun ⟨k, ek⟩ => ⟨PSet.Vl k, fun X hX => ?_⟩
    have hk : PSet.IsOrd k := (embed_isOrd_iff k).1 (κ_ord.congr ek)
    refine Mem.congr_right (W_equiv_embed_Vl k) ((mem_W_iff k X).2 ?_)
    exact Mem.congr_right ((rank_equiv_of_isOrd (embed_isOrd hk)).symm) (Mem.congr_right ek hX)
  · exact nn_map fun ⟨B, hB⟩ => ⟨_, (native_envelope_collapses κ_ord hB).symm⟩

/-- The three equivalent statements each give the arbitrary graph-envelope target; the converse
is not established. -/
theorem rankCover_of_nativeBarrier (h : NativeBarrier.{u}) : ¬¬∃ E : GSet.{u}, RankCover κ E :=
  nn_map (fun ⟨B, hB⟩ => ⟨embed B, hB⟩) (native_iff_native_envelope.1 (barrier_iff_native.1 h))

/-! ### The representative-bound calibration, conditional on an envelope -/

/-- The pointed subgraphs of `E` of rank in `κ`: a small carrier with total graph readback. -/
def Carrier (E : GSet.{u}) : Type u := {v : E.A // E.R v E.r ∧ Mem (rank (E.at' v)) κ}

/-- `x` is a native representative of the readback at `c`. -/
def Rep (E : GSet.{u}) (c : Carrier E) (x : PSet.{u}) : Prop := Equiv (E.at' c.1) (embed x)

/-- A native bound on all native representatives of the family. -/
def RepBound (E : GSet.{u}) : Prop := ¬¬∃ B : PSet.{u}, ∀ (c : Carrier E) (x : PSet.{u}), Rep E c x → x ∈ B

/-- From a representative bound to a native barrier: the native rank of the bound. -/
theorem barrier_of_repBound {E : GSet.{u}} (hE : RankCover κ E) {B : PSet.{u}}
    (hB : ∀ (c : Carrier E) (x : PSet.{u}), Rep E c x → x ∈ B) :
    Barrier (fun _ => True) PSet.omega (PSet.rank B) := by
  refine ⟨PSet.isOrd_rank B, fun f _ hf => ?_⟩
  have hbo : PSet.IsOrd (PSet.rank B) := PSet.isOrd_rank B
  have hmem : Mem (embed (PSet.rank B)) κ := (embed_mem_relHartogs_iff _).2 ⟨hbo, nn_intro ⟨f, hf⟩⟩
  have hE' : Mem (embed (PSet.rank B)) E :=
    hE _ (Mem.congr_left (rank_equiv_of_isOrd (embed_isOrd hbo)).symm hmem)
  refine Stable.of_nn hE' fun ⟨v, hv, ev⟩ => ?_
  have hc : Mem (rank (E.at' v)) κ := Mem.congr_left (rank_congr ev) (Mem.congr_left (rank_equiv_of_isOrd (embed_isOrd hbo)).symm hmem)
  have hb : PSet.rank B ∈ B := hB ⟨v, hv, hc⟩ _ ev.symm
  exact PSet.not_mem_self (PSet.rank B) ((PSet.mem_congr_left hbo.rank_equiv).1 (PSet.rank_mem hb))

/-- From a native barrier to a representative bound: `Vl k` for the native representative `k`. -/
theorem repBound_of_native {E : GSet.{u}} {k : PSet.{u}} (ek : Equiv (embed k) κ) :
    ∀ (c : Carrier E) (x : PSet.{u}), Rep E c x → x ∈ PSet.Vl k := by
  intro c x hx
  have hk : PSet.IsOrd k := (embed_isOrd_iff k).1 (κ_ord.congr ek.symm)
  have h1 : Mem (embed (PSet.rank x)) (embed k) :=
    Mem.congr_right ek.symm (Mem.congr_left ((rank_congr hx).trans (embed_rank x)) c.2.2)
  exact (PSet.mem_Vl_ord hk).2 (embed_mem_iff.1 h1)

/-- **The calibration**: given an envelope, a native representative bound is exactly a native
barrier. This is conditional on the envelope and produces neither. -/
theorem repBound_iff_barrier {E : GSet.{u}} (hE : RankCover κ E) : RepBound E ↔ NativeBarrier.{u} :=
  ⟨nn_map fun ⟨_, hB⟩ => ⟨_, barrier_of_repBound hE hB⟩,
   fun h => nn_map (fun ⟨k, ek⟩ => ⟨PSet.Vl k, repBound_of_native (E := E) ek.symm⟩) (barrier_iff_native.1 h)⟩

/-- The canonical cut of an envelope has rank `κ`, and is native iff a native barrier exists. -/
theorem native_cut_iff_barrier {E : GSet.{u}} (hE : RankCover κ E) :
    Equiv (rank (row E κ)) κ ∧ (Native (row E κ) ↔ NativeBarrier.{u}) :=
  have hrow : ∀ X, Mem X (row E κ) ↔ Mem (rank X) κ := fun _ => mem_row hE fun _ h => h
  ⟨rank_exact_row κ_ord hrow, (native_exact_row_iff κ_ord hrow).trans barrier_iff_native.symm⟩

/-- info: 'GSet.Bridge.embed_rank' does not depend on any axioms -/
#guard_msgs in #print axioms embed_rank
/-- info: 'GSet.Bridge.native_iff_native_rank' does not depend on any axioms -/
#guard_msgs in #print axioms native_iff_native_rank
/-- info: 'GSet.Bridge.native_exact_row_iff' does not depend on any axioms -/
#guard_msgs in #print axioms native_exact_row_iff
/-- info: 'GSet.Bridge.injRel_embed_omega_iff' does not depend on any axioms -/
#guard_msgs in #print axioms injRel_embed_omega_iff
/-- info: 'GSet.Bridge.embed_mem_relHartogs_iff' does not depend on any axioms -/
#guard_msgs in #print axioms embed_mem_relHartogs_iff
/-- info: 'GSet.Bridge.barrier_iff_native' does not depend on any axioms -/
#guard_msgs in #print axioms barrier_iff_native
/-- info: 'GSet.Bridge.native_iff_native_envelope' does not depend on any axioms -/
#guard_msgs in #print axioms native_iff_native_envelope
/-- info: 'GSet.Bridge.rankCover_of_nativeBarrier' does not depend on any axioms -/
#guard_msgs in #print axioms rankCover_of_nativeBarrier
/-- info: 'GSet.Bridge.repBound_iff_barrier' does not depend on any axioms -/
#guard_msgs in #print axioms repBound_iff_barrier
/-- info: 'GSet.Bridge.native_cut_iff_barrier' does not depend on any axioms -/
#guard_msgs in #print axioms native_cut_iff_barrier

end GSet.Bridge
