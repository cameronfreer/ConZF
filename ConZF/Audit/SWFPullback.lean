import ConZF.NativeBridge
import ConZF.NativeBound
import ConZF.DecoderLocal
/-!
Two checks on future semantic proposals (nc6 audit). Neither produces an envelope or a barrier
without a logical premise, and nothing here changes `NegCore`.

* **Accessible collapse** (reviewer probe, integrated): accessibility of a graph root constructs an
  explicit native tree equivalent to the graph (`embed_treeAcc`, `native_of_nnacc`); under excluded
  middle, stable well-founded induction gives ordinary well-foundedness (`wf_of_swf_of_em`), so every
  graph set is native and irrefutable excluded middle already yields the native barrier at `ω`
  (`nativeBarrier_of_not_not_em`). Excluded middle is a theorem parameter, never an axiom. A model of
  the no-barrier scenario must therefore fail irrefutable excluded middle; being non-Boolean is not
  enough.
* **The pullback test** (nc6 §4): fix `bStar := wfBound (ULift Nat)` before any injection. From a
  pure injection `f : bStar → ω`, the active labels `labelS f` and the pulled-back membership relation
  `labelR f` on them satisfy stable well-founded induction (`swf_labelR`) but not ordinary
  well-foundedness (`not_wf_labelR`): a well-foundedness proof would make the relation a `WFCode` on
  `ULift Nat` whose decoded trees represent every member of `bStar`, so its height dominates
  `bStar` and `bStar ∈ bStar`. Hence `Emb bStar ω` gives, negatively, a relation built from the
  injection with `SWF` and `¬ WellFounded` (`emb_bStar_swf_not_wf`), in particular from absence of a
  native barrier (`swf_not_wf_of_no_barrier`). This is a necessary test for a countermodel, not a
  countermodel; one such relation does not refute all native barriers.
-/
universe u

namespace GSet.AccessibleAudit
open PSet.OrdDecode

def treeAcc (G : GSet.{u}) : (a : G.A) → Acc G.R a → PSet.{u} :=
  fun _ h => Acc.rec (motive := fun _ _ => PSet.{u})
    (fun a _ ih => ⟨{b : G.A // G.R b a}, fun b => ih b.1 b.2⟩) h

theorem treeAcc_eq (G : GSet.{u}) (a : G.A) (h : Acc G.R a) :
    treeAcc G a h = ⟨{b : G.A // G.R b a}, fun b => treeAcc G b.1 (h.inv b.2)⟩ := by
  cases h
  rfl

/-- An accessible root has an explicit native tree, exactly. -/
theorem embed_treeAcc (G : GSet.{u}) (a : G.A) (h : Acc G.R a) : Equiv (embed (treeAcc G a h)) (G.at' a) := by
  induction h with
  | intro a h ih =>
    rw [treeAcc_eq]
    refine ext fun K => ⟨fun hk => ?_, fun hk => ?_⟩
    · exact nn_map (fun ⟨b, eb⟩ => ⟨b.1, b.2, eb.trans (ih b.1 b.2)⟩) (mem_embed.1 hk)
    · exact mem_embed.2 (nn_map (fun ⟨b, hb, eb⟩ => ⟨⟨b, hb⟩, eb.trans (ih b hb).symm⟩) hk)

/-- Negative accessibility at the root gives nativity. -/
theorem native_of_nnacc (G : GSet.{u}) (h : ¬¬Acc G.R G.r) : Bridge.Native G :=
  nn_map (fun ha => ⟨treeAcc G G.r ha, (embed_treeAcc G G.r ha).symm⟩) h

/-- Under excluded middle, stable well-founded induction is ordinary well-foundedness. -/
theorem wf_of_swf_of_em {A : Type u} {R : A → A → Prop} (em : ∀ p : Prop, p ∨ ¬p) (h : Graph.SWF R) :
    WellFounded R := by
  have hs : ∀ a, Stable (Acc R a) := fun a => ⟨fun hn => (em (Acc R a)).elim id (fun nh => False.elim (hn nh))⟩
  exact ⟨h (fun a => Acc R a) hs (fun a ih => Acc.intro a ih)⟩

theorem all_native_of_em (em : ∀ p : Prop, p ∨ ¬p) (G : GSet.{u}) : Bridge.Native G :=
  native_of_nnacc G (nn_intro ((wf_of_swf_of_em em G.swf).apply G.r))

/-- Irrefutable excluded middle already yields the native barrier at `ω`. -/
theorem nativeBarrier_of_not_not_em (hem : ¬¬(∀ p : Prop, p ∨ ¬p)) : Bridge.NativeBarrier.{u} := by
  haveI : Stable Bridge.NativeBarrier.{u} := inferInstanceAs (Stable (¬_))
  exact Stable.of_nn hem fun em => Bridge.barrier_iff_native.2 (all_native_of_em em Bridge.κ)

/-- info: 'GSet.AccessibleAudit.embed_treeAcc' does not depend on any axioms -/
#guard_msgs in #print axioms embed_treeAcc
/-- info: 'GSet.AccessibleAudit.native_of_nnacc' does not depend on any axioms -/
#guard_msgs in #print axioms native_of_nnacc
/-- info: 'GSet.AccessibleAudit.wf_of_swf_of_em' does not depend on any axioms -/
#guard_msgs in #print axioms wf_of_swf_of_em
/-- info: 'GSet.AccessibleAudit.nativeBarrier_of_not_not_em' does not depend on any axioms -/
#guard_msgs in #print axioms nativeBarrier_of_not_not_em

end GSet.AccessibleAudit

namespace PSet.SWFPullbackAudit
open PSet.OrdDecode

/-- The native ordinal fixed before any injection is opened. -/
def bStar : PSet.{u} := wfBound (ULift.{u} Nat)

theorem bStar_ord : IsOrd bStar.{u} := isOrd_wfBound _

/-- The active labels of `f`: naturals labelling some member of `bStar`. -/
def labelS (f : PSet.{u}) (n : ULift.{u} Nat) : Prop := ¬¬∃ α, α ∈ bStar ∧ pair α (ofNat n.down) ∈ f

/-- The pulled-back membership relation on active labels. -/
def labelR (f : PSet.{u}) (m n : {n : ULift.{u} Nat // labelS f n}) : Prop :=
  ¬¬∃ α β, α ∈ bStar ∧ β ∈ bStar ∧ pair α (ofNat m.1.down) ∈ f ∧ pair β (ofNat n.1.down) ∈ f ∧ α ∈ β

instance {f : PSet.{u}} {m n : {n : ULift.{u} Nat // labelS f n}} : Stable (labelR f m n) :=
  inferInstanceAs (Stable (¬_))

/-- **Stable well-founded induction holds**, by native membership induction on the represented
ordinal with every label of it quantified over. -/
theorem swf_labelR {f : PSet.{u}} (hf : OInj f bStar omega) : Graph.SWF (labelR f) := by
  intro P hP H n
  have key : ∀ α : PSet.{u}, ∀ n : {n : ULift.{u} Nat // labelS f n}, pair α (ofNat n.1.down) ∈ f → P n := by
    refine mem_induction (P := fun α => ∀ n : {n : ULift.{u} Nat // labelS f n}, pair α (ofNat n.1.down) ∈ f → P n)
      fun α ih n hn => ?_
    refine H n fun m hm => ?_
    refine Stable.of_nn hm fun ⟨α', β', _, _, hm', hn', hab⟩ => ?_
    have e : β' ≈ α := hf.2 β' α _ _ hn' hn (Equiv.refl _)
    exact ih α' ((mem_congr_right e).1 hab) m hm'
  exact Stable.of_nn n.2 fun ⟨α, _, hn⟩ => key α n hn

/-- Under a well-foundedness proof, the relation is a certificate on `ULift Nat`. -/
def code (f : PSet.{u}) (wf : WellFounded (labelR f)) : WFCode (ULift.{u} Nat) := ⟨labelS f, labelR f, wf⟩

/-- Every member of `bStar` is labelled by an active label. -/
theorem label_of_mem {f : PSet.{u}} (hf : OInj f bStar omega) {z : PSet.{u}} (hz : z ∈ bStar) :
    ¬¬∃ n : {n : ULift.{u} Nat // labelS f n}, pair z (ofNat n.1.down) ∈ f := by
  refine nn_bind (hf.1.2.1 z hz) fun ⟨v, hv⟩ => ?_
  refine nn_map (fun ⟨k, ek⟩ => ?_) (mem_omega.1 (map_edge_typed hf.1 hv).2)
  have hk : pair z (ofNat k) ∈ f := (mem_congr_left (pair_congr (Equiv.refl z) ek)).1 hv
  exact ⟨⟨⟨k⟩, nn_intro ⟨z, hz, hk⟩⟩, hk⟩

/-- The decoded tree at a label represents its ordinal exactly, by full predecessor coverage. -/
theorem tree_equiv {f : PSet.{u}} (hf : OInj f bStar omega) (wf : WellFounded (labelR f)) :
    ∀ α : PSet.{u}, α ∈ bStar → ∀ n : {n : ULift.{u} Nat // labelS f n}, pair α (ofNat n.1.down) ∈ f →
      (code f wf).tree n ≈ α := by
  have inst : ∀ α : PSet.{u}, Stable (α ∈ bStar → ∀ n : {n : ULift.{u} Nat // labelS f n},
      pair α (ofNat n.1.down) ∈ f → (code f wf).tree n ≈ α) :=
    fun _ => ⟨fun h hα n hn => Stable.dne fun hne => h fun g => hne (g hα n hn)⟩
  intro α₀
  refine @mem_induction.{u} (fun α => α ∈ bStar → ∀ n : {n : ULift.{u} Nat // labelS f n},
    pair α (ofNat n.1.down) ∈ f → (code f wf).tree n ≈ α) inst (fun α ih hα n hn => ?_) α₀
  rw [WFCode.tree_eq (code f wf) n]
  refine ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · refine Stable.of_nn hz fun ⟨⟨m, hm⟩, ez⟩ => ?_
    refine Stable.of_nn hm fun ⟨α', β', hα', _, hm', hn', hab⟩ => ?_
    have e : β' ≈ α := hf.2 β' α _ _ hn' hn (Equiv.refl _)
    have hα'α : α' ∈ α := (mem_congr_right e).1 hab
    exact (mem_congr_left (ez.trans (ih α' hα'α hα' m hm'))).2 hα'α
  · have hzb : z ∈ bStar := bStar_ord.trans α hα z hz
    refine Stable.of_nn (label_of_mem hf hzb) fun ⟨m, hm⟩ => ?_
    have hR : labelR f m n := nn_intro ⟨z, α, hzb, hα, hm, hn, hz⟩
    exact nn_intro ⟨⟨m, hR⟩, (ih z hz hzb m hm).symm⟩

/-- **Ordinary well-foundedness fails**: the height of the certificate would dominate `bStar`. -/
theorem not_wf_labelR {f : PSet.{u}} (hf : OInj f bStar omega) : ¬ WellFounded (labelR f) := by
  intro wf
  have dom : ∀ z, z ∈ bStar → z ∈ (code f wf).height := by
    intro z hz
    refine Stable.of_nn (label_of_mem hf hz) fun ⟨n, hn⟩ => ?_
    have hr : rank z ∈ (code f wf).height :=
      (mem_congr_left (rank_congr (tree_equiv hf wf z hz n hn))).1 (rank_mem (func_mem (range (code f wf).tree) n))
    exact (mem_congr_left (bStar_ord.mem hz).rank_equiv).1 hr
  exact not_mem_self bStar (mem_wfBound_of_dominated bStar_ord (nn_intro ⟨code f wf, dom⟩))

/-- **nc6 (23)**: an injection of `bStar` into `ω` gives, negatively, a relation built from it with
stable but not ordinary well-foundedness. -/
theorem emb_bStar_swf_not_wf (h : Emb bStar.{u} omega) :
    ¬¬∃ f : PSet.{u}, OInj f bStar omega ∧ Graph.SWF (labelR f) ∧ ¬ WellFounded (labelR f) :=
  nn_map (fun ⟨f, hf⟩ => ⟨f, hf, swf_labelR hf, not_wf_labelR hf⟩) h

/-- Absence of a native barrier at `ω` forces such a relation. The converse is not claimed. -/
theorem swf_not_wf_of_no_barrier (h : ¬ GSet.Bridge.NativeBarrier.{u}) :
    ¬¬∃ f : PSet.{u}, OInj f bStar omega ∧ Graph.SWF (labelR f) ∧ ¬ WellFounded (labelR f) :=
  emb_bStar_swf_not_wf ((DecoderLocal.no_barrier_iff omega).1 h bStar bStar_ord)

/-- info: 'PSet.SWFPullbackAudit.swf_labelR' does not depend on any axioms -/
#guard_msgs in #print axioms swf_labelR
/-- info: 'PSet.SWFPullbackAudit.not_wf_labelR' does not depend on any axioms -/
#guard_msgs in #print axioms not_wf_labelR
/-- info: 'PSet.SWFPullbackAudit.emb_bStar_swf_not_wf' does not depend on any axioms -/
#guard_msgs in #print axioms emb_bStar_swf_not_wf
/-- info: 'PSet.SWFPullbackAudit.swf_not_wf_of_no_barrier' does not depend on any axioms -/
#guard_msgs in #print axioms swf_not_wf_of_no_barrier

end PSet.SWFPullbackAudit
