import ConZF.Audit.SWFPullback
import ConZF.Endpoint
import ConZF.Markov
/-!
The conditional upgrade bridge (nc8 closeout; reviewer probe integrated). `Upgrade.{u}` is the
principle "stable well-founded induction implies ordinary well-foundedness for every relation on a
`Type u` carrier". It is a theorem parameter with explicit universe levels, never an axiom or an
instance, and nothing here proves it in bare Lean.

* Full predicate induction is Lean's accessibility-based well-foundedness (`fullInd_iff_wf`).
* `Upgrade.{u}` collapses every graph set to an actual native tree through the checked accessible
  recursor (`collapse`, `collapse_exact`), so every graph set is native and the native barrier at `ω`
  exists (`all_native`, `barrier`); it also refutes an injection of the actual `bStar` into `ω`
  through `Audit/SWFPullback.lean` (`bStar_not_emb`).
* Native membership on `PSet.{u}` has stable induction unconditionally (`mem_swf`); since
  `PSet.{u} : Type (u+1)`, `Upgrade.{u+1}` gives ordinary well-foundedness of membership (`mem_wf`),
  hence the branch's accessibility premise `AccHyp.{u}` (`accHyp`), the Markov statement at the base
  universe from accessibility of `ω` (`propMarkov`), and at the upper universe the existing
  consistency endpoint `Con ZFCI` (`con_ZFCI`) with no excluded-middle premise.

External result (recorded, not formalized): Hofmann, van Oosten and Streicher, *Well-foundedness in
realizability*, Theorem 1.1, promotes induction for `j`-closed predicates to full induction in
ordinary realizability, with `j` double negation over a Boolean base, and handles parameters and
internalization. Subject to a faithful interpretation of the relevant Lean rules and universes,
ordinary full realizability therefore validates `Upgrade` and hence the whole accessibility route
above, not merely the one-barrier benchmark, so such models are unsuitable for refuting this route.
Their Theorem 2.1 shows the general principle entails Markov's principle, and its proof uses a
partial-combinatory-algebra fixed point: none of this makes `Upgrade` an axiom-free theorem of Lean.
All targets stay distinct: `Upgrade` is much stronger than the barrier; the barrier suffices for the
graph envelope; neither converse nor unrestricted graph Collection is supplied.

Further external observation (nc9, reviewed at e19c092; not formalized): internal realizability over
the full natural-number-chain presheaf base does not escape either. Density of the canonical
inclusion lets the closed-subobject correspondence preserve negation, so the stable active-label
subtype and its stable pulled-back relation transfer to the base, where the chain model supplies full
induction; the published reflection theorem, which needs no Boolean base, brings full induction back,
in arbitrary contexts. That yields only the **restricted** upgrade, for stable relations on stable
natural-number subtypes, which suffices to refute an injection of `bStar` into `ω` through the
checked pullback; it does not establish the unrestricted `Upgrade` parameter above, nor its
`Con ZFCI` corollary. The next countermodel test stays negative: even `SWF R → ¬¬WellFounded R`
contradicts the pullback, so failing to force full well-foundedness, or refuting Markov or the
unrestricted upgrade, does not pass it.

Further external exclusion (nc10, reviewed at c420fd1; not formalized), replacing the earlier
pending smallness audit. For a full presheaf base on a universe-small frame with ordinary internal
realizability over it, under the standard cardinal-small display-map structure (the assembly
criterion of van den Berg–Moerdijk, Definition 2.5) and faithful native rules, the constant
well-order of `λ = (max(|W|, ℵ₀))⁺` transfers to a small carrier, reflected well-foundedness makes it
a certificate, the existing native decoder produces a native ordinal `b_λ` with `λ` many pairwise
inequivalent global members, and a world/numeral counting argument in the context of any hypothetical
injection makes `b_λ` an internal native barrier at `ω`; through the checked bridge these models also
satisfy the graph-envelope benchmark. For **countable** frames the smallness of the carrier is forced
without a chosen display universe: `∇(Δω₁)` embeds monically into `∇(𝒫(ΔNat)) ≅ (Ω_j)^N` using an
external family of `ω₁` distinct subsets of `Nat` in the full base, and that type is small whenever
full `Prop` and `Nat` are small and small types are closed under function types and `Prop`-defined
subtypes. Kept distinct: `b_λ` is not asserted to be `bStar`; no unrestricted `Upgrade`, unrestricted
graph Collection, or unconditional Lean barrier results; and a global native element of a semantic
model is not a closed Lean term.
-/
universe u

namespace UpgradeAudit

def FullInd {A : Type u} (R : A → A → Prop) : Prop :=
  ∀ P : A → Prop, (∀ a, (∀ b, R b a → P b) → P a) → ∀ a, P a

theorem fullInd_iff_wf {A : Type u} {R : A → A → Prop} :
    FullInd R ↔ WellFounded R := by
  constructor
  · intro h
    exact ⟨h (Acc R) (fun a ih => Acc.intro a ih)⟩
  · intro h P step a
    exact h.induction a step

/-- The model-specific principle claimed in nc8, scoped to one universe. -/
def Upgrade : Prop :=
  ∀ (A : Type u) (R : A → A → Prop), Graph.SWF R → WellFounded R

/-- The graph carrier is in Type u. -/
def collapse (up : Upgrade.{u}) (G : GSet.{u}) : PSet.{u} :=
  GSet.AccessibleAudit.treeAcc G G.r ((up G.A G.R G.swf).apply G.r)

theorem collapse_exact (up : Upgrade.{u}) (G : GSet.{u}) :
    GSet.Equiv (PSet.OrdDecode.embed (collapse up G)) G :=
  GSet.AccessibleAudit.embed_treeAcc G G.r ((up G.A G.R G.swf).apply G.r)

theorem all_native (up : Upgrade.{u}) (G : GSet.{u}) : GSet.Bridge.Native G :=
  nn_intro ⟨collapse up G, (collapse_exact up G).symm⟩

theorem barrier (up : Upgrade.{u}) : GSet.Bridge.NativeBarrier.{u} :=
  GSet.Bridge.barrier_iff_native.2 (all_native up GSet.Bridge.κ)

theorem bStar_not_emb (up : Upgrade.{u}) :
    ¬ PSet.OrdDecode.Emb PSet.SWFPullbackAudit.bStar.{u} PSet.omega := by
  intro h
  apply PSet.SWFPullbackAudit.emb_bStar_swf_not_wf h
  rintro ⟨f, _, hs, hn⟩
  exact hn (up _ (PSet.SWFPullbackAudit.labelR f) hs)

/-- Native membership already has stable induction; no Upgrade premise here. -/
theorem mem_swf : Graph.SWF (fun x y : PSet.{u} => x ∈ y) := by
  intro P hs step
  haveI : ∀ x, Stable (P x) := hs
  exact PSet.mem_induction step

/-- PSet u lives in Type (u+1), so the upgrade is used one universe higher. -/
theorem mem_wf (up : Upgrade.{u+1}) :
    WellFounded (fun x y : PSet.{u} => x ∈ y) :=
  up PSet.{u} (fun x y => x ∈ y) mem_swf

theorem accHyp (up : Upgrade.{u+1}) : PSet.AccHyp.{u} :=
  PSet.accHyp_iff_not_not_mem_wf.2 (nn_intro (mem_wf up).apply)

/-- A consequence at the base native universe, using the existing search theorem. -/
theorem propMarkov (up : Upgrade.{1}) : PSet.PropMarkov :=
  PSet.prop_markov_of_acc_omega ((mem_wf up).apply PSet.omega.{0})

/-- Full upper membership accessibility suffices for the existing endpoint. -/
theorem con_ZFCI (up : Upgrade.{2}) : PSet.Con PSet.ZFCI :=
  PSet.con_ZFCI_of_upper_mem_wf (nn_intro (mem_wf up).apply)

/-- info: 'UpgradeAudit.fullInd_iff_wf' does not depend on any axioms -/
#guard_msgs in #print axioms fullInd_iff_wf
/-- info: 'UpgradeAudit.collapse_exact' does not depend on any axioms -/
#guard_msgs in #print axioms collapse_exact
/-- info: 'UpgradeAudit.all_native' does not depend on any axioms -/
#guard_msgs in #print axioms all_native
/-- info: 'UpgradeAudit.barrier' does not depend on any axioms -/
#guard_msgs in #print axioms barrier
/-- info: 'UpgradeAudit.bStar_not_emb' does not depend on any axioms -/
#guard_msgs in #print axioms bStar_not_emb
/-- info: 'UpgradeAudit.mem_swf' does not depend on any axioms -/
#guard_msgs in #print axioms mem_swf
/-- info: 'UpgradeAudit.mem_wf' does not depend on any axioms -/
#guard_msgs in #print axioms mem_wf
/-- info: 'UpgradeAudit.accHyp' does not depend on any axioms -/
#guard_msgs in #print axioms accHyp
/-- info: 'UpgradeAudit.propMarkov' does not depend on any axioms -/
#guard_msgs in #print axioms propMarkov
/-- info: 'UpgradeAudit.con_ZFCI' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZFCI

end UpgradeAudit
