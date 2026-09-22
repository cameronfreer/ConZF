import ConZF.NativeBound
import ConZF.Mat
/-!
Negative upper simulations. A certificate for an ordinal bound on the target of a state `p` of
a source relation `R` need not present the target: it suffices to simulate `p` in a node `z` of
a native well-founded code `c`, in the sense that every `R`-child of `p` is not not simulated in
some `c`-predecessor of `z` (`Sim`, a stable proposition defined by native recursion on the
certificate). Then

* `subset_ht_of_sim`: under coverage (every element of the target of `p` is not not reached by
  the successor of the target of a child), the target of `p` is included in the height of `z`;
  neither functionality nor accessibility of `R` is used;
* `sim_of_subset_ht`: conversely, under descent, so that for the coherent assignments of
  `Mat.lean` simulation at `z` is exactly inclusion of the target in the height of `z`
  (`Coherent.cover` supplies the coverage);
* `sim_top`: certificates for all children, each in some code on a fixed carrier `X`, give one
  certificate for the parent, at the top of the enclosing tree `Enc X` of all codes on `X`,
  which is natively well-founded without any premise. No double negation crosses a universal
  quantifier: the enclosing tree is formed before the pointwise certificates are used;
* `not_sim_top`: the top of the enclosing tree is not simulated in any code on `X` itself, so
  the enlargement of the carrier is necessary.

`Sim` is defined by `WellFounded.fix` with a `Type`-valued motive. `SimI` is the same relation as
an impredicative least fixed point in `Prop`, with no elimination of `Acc` into `Type`
(`sim_iff_simI`); the decoders of `NativeBound.lean` and `Mat.lean` do need that elimination.
-/
universe u v

namespace PSet

/-! ### Heights of nodes -/

namespace WFCode
variable {X : Type u} (c : WFCode X)

/-- The height of a node: the rank of its tree. -/
def ht (x : {x : X // c.S x}) : PSet.{u} := rank (c.tree x)

theorem isOrd_ht (x : {x : X // c.S x}) : IsOrd (c.ht x) := isOrd_rank _

theorem mem_ht {x : {x : X // c.S x}} {z : PSet.{u}} :
    z ∈ c.ht x ↔ ¬¬∃ y : {y : {x : X // c.S x} // c.R y x}, z ∈ succ (c.ht y.1) := by
  unfold ht; rw [c.tree_eq]; exact mem_rank

theorem ht_mem_ht {x y : {x : X // c.S x}} (h : c.R y x) : c.ht y ∈ c.ht x :=
  c.mem_ht.2 (nn_intro ⟨⟨y, h⟩, self_mem_succ _⟩)

end WFCode

/-! ### Simulation -/

section
variable {α : Sort v} (R : α → α → Prop) {X : Type u} (c : WFCode X)

/-- `p` is simulated at the node `z`: every child of `p` is not not simulated at some
predecessor of `z`. Defined by native recursion on the certificate. -/
def Sim : α → {x : X // c.S x} → Prop := fun p z =>
  c.wf.fix (C := fun _ => α → Prop)
    (fun z ih p => ∀ q, R q p → ¬¬∃ z' : {y // c.R y z}, ih z'.1 z'.2 q) z p

theorem sim_iff {p : α} {z : {x : X // c.S x}} :
    Sim R c p z ↔ ∀ q, R q p → ¬¬∃ z' : {y // c.R y z}, Sim R c q z'.1 := by
  unfold Sim; rw [WellFounded.fix_eq]

instance {p : α} {z : {x : X // c.S x}} : Stable (Sim R c p z) :=
  ⟨fun h => (sim_iff R c).2 fun q hq => Stable.of_nn h fun hs => (sim_iff R c).1 hs q hq⟩

/-- Simulation as an impredicative least fixed point: the same relation, with no recursion on
the certificate and no elimination of `Acc` into `Type`. -/
def SimI (p : α) (z : {x : X // c.S x}) : Prop :=
  ∀ Q : α → {x : X // c.S x} → Prop,
    (∀ p z, (∀ q, R q p → ¬¬∃ z' : {y // c.R y z}, Q q z'.1) → Q p z) → Q p z

theorem simI_iff {p : α} {z : {x : X // c.S x}} :
    SimI R c p z ↔ ∀ q, R q p → ¬¬∃ z' : {y // c.R y z}, SimI R c q z'.1 := by
  constructor
  · intro h
    refine h (fun p z => ∀ q, R q p → ¬¬∃ z' : {y // c.R y z}, SimI R c q z'.1) ?_
    intro p z ih q hq
    refine nn_map (fun ⟨z', hz'⟩ => ⟨z', ?_⟩) (ih q hq)
    intro Q hQ
    exact hQ q z'.1 fun q' hq' => nn_map (fun ⟨z'', h⟩ => ⟨z'', h Q hQ⟩) (hz' q' hq')
  · intro h Q hQ
    exact hQ p z fun q hq => nn_map (fun ⟨z', hz'⟩ => ⟨z', hz' Q hQ⟩) (h q hq)

/-- The two definitions agree; only this comparison uses the certificate's well-foundedness. -/
theorem sim_iff_simI : ∀ (z : {x : X // c.S x}) (p : α), Sim R c p z ↔ SimI R c p z := by
  intro z
  induction c.wf.apply z with
  | intro z _ ih =>
    intro p
    constructor
    · intro h
      refine (simI_iff R c).2 fun q hq => ?_
      exact nn_map (fun ⟨z', h'⟩ => ⟨z', (ih z'.1 z'.2 q).1 h'⟩) ((sim_iff R c).1 h q hq)
    · intro h
      refine (sim_iff R c).2 fun q hq => ?_
      exact nn_map (fun ⟨z', h'⟩ => ⟨z', (ih z'.1 z'.2 q).2 h'⟩) ((simI_iff R c).1 h q hq)

variable {τ : α → PSet.{u} → Prop}

/-- Coverage: every element of a target is not not reached by the successor of the target of a
child. -/
def Cover (τ : α → PSet.{u} → Prop) : Prop :=
  ∀ p t ξ, τ p t → ξ ∈ t → ¬¬∃ q t', R q p ∧ τ q t' ∧ ξ ∈ succ t'

/-- Soundness: a simulation bounds the target by the height of the node. -/
theorem subset_ht_of_sim (hc : Cover R τ) (hord : ∀ p t, τ p t → IsOrd t) :
    ∀ (z : {x : X // c.S x}) p t, τ p t → Sim R c p z → ∀ ξ, ξ ∈ t → ξ ∈ c.ht z := by
  intro z
  induction c.wf.apply z with
  | intro z _ ih =>
    intro p t hpt hs ξ hξ
    refine Stable.of_nn (hc p t ξ hpt hξ) fun ⟨q, t', hq, hqt, hξ'⟩ => ?_
    refine Stable.of_nn ((sim_iff R c).1 hs q hq) fun ⟨z', hs'⟩ => ?_
    have sub : ∀ ξ, ξ ∈ t' → ξ ∈ c.ht z'.1 := ih z'.1 z'.2 q t' hqt hs'
    refine c.mem_ht.2 (nn_intro ⟨z', ?_⟩)
    refine Stable.of_nn (mem_succ.1 hξ') fun
      | .inl h => mem_succ_of_mem (sub ξ h)
      | .inr e => (mem_congr_left e).2 ((hord q t' hqt).mem_succ_of_subset (c.isOrd_ht _) sub)

/-- Completeness of simulations for bounds: under descent, inclusion of the target in the
height of a node gives a simulation at that node. -/
theorem sim_of_subset_ht (desc : ∀ q p t t', R q p → τ q t → τ p t' → t ∈ t')
    (htot : ∀ q p, R q p → ¬¬∃ t, τ q t) :
    ∀ (z : {x : X // c.S x}) p t, τ p t → (∀ ξ, ξ ∈ t → ξ ∈ c.ht z) → Sim R c p z := by
  intro z
  induction c.wf.apply z with
  | intro z _ ih =>
    intro p t hpt hsub
    refine (sim_iff R c).2 fun q hq => ?_
    refine Stable.of_nn (htot q p hq) fun ⟨t', hqt⟩ => ?_
    refine Stable.of_nn (c.mem_ht.1 (hsub t' (desc q p t' t hq hqt hpt))) fun ⟨z', h⟩ => ?_
    refine nn_intro ⟨z', ih z'.1 z'.2 q t' hqt fun ξ hξ => ?_⟩
    refine Stable.of_nn (mem_succ.1 h) fun
      | .inl h => (c.isOrd_ht _).trans _ h ξ hξ
      | .inr e => (mem_congr_right e).1 hξ

end

/-- The coherent assignments satisfy coverage at ordinal targets: the first-child set is formed
by Separation inside the target, and the availability restriction is forgotten. -/
theorem Coherent.cover {D : PSet.{u} → PSet.{u}} {U : PSet.{u}} {τ : Path.{u} → PSet.{u} → Prop}
    (hτ : Coherent D U τ) {p : Path.{u}} {t ξ : PSet.{u}} (hpt : τ p t) (ht : IsOrd t)
    (hξ : ξ ∈ t) : ¬¬∃ q t', Rel τ q p ∧ τ q t' ∧ ξ ∈ succ t' := by
  let P : PSet.{u} → Prop := fun x => ¬¬∃ ζ, τ (.a :: p) ζ ∧ x ∈ ζ
  have hG : IsG τ p (sep P t) := fun x => by
    refine (mem_sep (p := P) fun _ _ e => nn_map fun ⟨ζ, hζ, hx⟩ =>
      ⟨ζ, hζ, (mem_congr_left e).1 hx⟩).trans ⟨And.right, fun h => ⟨?_, h⟩⟩
    exact Stable.of_nn h fun ⟨ζ, hζ, hx⟩ => ht.trans ζ (hτ.desc hζ hpt) x hx
  exact nn_map (fun ⟨l, t', _, h, hξ⟩ => ⟨l :: p, t', ⟨l, rfl, t', h⟩, h, hξ⟩)
    ((hτ.sup hpt hG ξ).1 hξ)

/-! ### The enclosing tree of all codes on a carrier -/

/-- A top node, and the nodes of every code on `X`. -/
def Enc (X : Type u) : Type u := Option (Σ c : WFCode X, {x : X // c.S x})

/-- The nodes of each code, below the top. -/
inductive EncRel {X : Type u} : Enc X → Enc X → Prop
  | tag {c : WFCode X} {z z' : {x : X // c.S x}} : c.R z' z → EncRel (some ⟨c, z'⟩) (some ⟨c, z⟩)
  | top (w : Σ c : WFCode X, {x : X // c.S x}) : EncRel (some w) none

theorem acc_encRel_some {X : Type u} (c : WFCode X) :
    ∀ z : {x : X // c.S x}, Acc EncRel (some ⟨c, z⟩ : Enc X) := by
  intro z
  induction c.wf.apply z with
  | intro z _ ih =>
    refine ⟨_, fun y hy => ?_⟩
    cases hy with
    | tag h => exact ih _ h

theorem wf_encRel (X : Type u) : WellFounded (EncRel (X := X)) :=
  ⟨fun
    | none => ⟨_, fun y hy => by cases hy with | top w => exact acc_encRel_some w.1 w.2⟩
    | some ⟨c, z⟩ => acc_encRel_some c z⟩

/-- The enclosing tree as a code on `Enc X`. It is well-founded without any premise. -/
def encCode (X : Type u) : WFCode (Enc X) where
  S _ := True
  R a b := EncRel a.1 b.1
  wf := InvImage.wf Subtype.val (wf_encRel X)

/-- The node of the enclosing tree for a node of a code. -/
def Enc.node {X : Type u} (c : WFCode X) (z : {x : X // c.S x}) : {y : Enc X // (encCode X).S y} :=
  ⟨some ⟨c, z⟩, trivial⟩

/-- The top of the enclosing tree. -/
def Enc.top (X : Type u) : {y : Enc X // (encCode X).S y} := ⟨none, trivial⟩

section
variable {α : Sort v} (R : α → α → Prop) {X : Type u}

/-- A simulation in a code embeds into the enclosing tree. -/
theorem sim_node (c : WFCode X) :
    ∀ (z : {x : X // c.S x}) (p : α), Sim R c p z → Sim R (encCode X) p (Enc.node c z) := by
  intro z
  induction c.wf.apply z with
  | intro z _ ih =>
    intro p hs
    refine (sim_iff R (encCode X)).2 fun q hq => ?_
    exact nn_map (fun ⟨z', hs'⟩ => ⟨⟨Enc.node c z'.1, EncRel.tag z'.2⟩, ih z'.1 z'.2 q hs'⟩)
      ((sim_iff R c).1 hs q hq)

/-- Certificates for all children, in codes on `X`, give a certificate for the parent at the
top of the enclosing tree. The tree is formed first; the pointwise certificates prove the
simulation. -/
theorem sim_top {p : α} (h : ∀ q, R q p → ¬¬∃ (c : WFCode X) (z : {x : X // c.S x}), Sim R c q z) :
    Sim R (encCode X) p (Enc.top X) :=
  (sim_iff R (encCode X)).2 fun q hq => nn_map (fun ⟨c, z, hs⟩ =>
    ⟨⟨Enc.node c z, EncRel.top _⟩, sim_node R c z q hs⟩) (h q hq)

end

theorem encRel_some {X : Type u} {c : WFCode X} {z : {x : X // c.S x}} {y : Enc X}
    (h : EncRel y (some ⟨c, z⟩)) : ∃ z' : {y : {x : X // c.S x} // c.R y z}, y = some ⟨c, z'.1⟩ := by
  cases h with
  | tag h => exact ⟨⟨_, h⟩, rfl⟩

/-- The height of a node in the enclosing tree is its height in its code. -/
theorem ht_node {X : Type u} (c : WFCode X) :
    ∀ z : {x : X // c.S x}, (encCode X).ht (Enc.node c z) ≈ c.ht z := by
  intro z
  induction c.wf.apply z with
  | intro z _ ih =>
    refine ext fun ξ => (encCode X).mem_ht.trans (Iff.trans ?_ c.mem_ht.symm)
    constructor
    · refine nn_map fun ⟨⟨y, hy⟩, h⟩ => ?_
      obtain ⟨z', e⟩ := encRel_some hy
      have : y = Enc.node c z'.1 := Subtype.ext e
      subst this
      exact ⟨z', (mem_congr_right (succ_congr (ih z'.1 z'.2))).1 h⟩
    · exact nn_map fun ⟨z', h⟩ => ⟨⟨Enc.node c z'.1, EncRel.tag z'.2⟩,
        (mem_congr_right (succ_congr (ih z'.1 z'.2))).2 h⟩

/-- The bound of a carrier: the height of the top of its enclosing tree. -/
def encBound (X : Type u) : PSet.{u} := (encCode X).ht (Enc.top X)

theorem isOrd_encBound (X : Type u) : IsOrd (encBound X) := (encCode X).isOrd_ht _

theorem ht_node_mem_encBound {X : Type u} (c : WFCode X) (z : {x : X // c.S x}) :
    (encCode X).ht (Enc.node c z) ∈ encBound X :=
  (encCode X).ht_mem_ht (EncRel.top _)

/-- The target of a state whose children all have certificates on `X` is bounded by
`encBound X`. -/
theorem mem_succ_encBound_of_children {α : Sort v} {R : α → α → Prop} {τ : α → PSet.{u} → Prop}
    (hc : Cover R τ) (hord : ∀ p t, τ p t → IsOrd t) {X : Type u} {p : α} {t : PSet.{u}}
    (hpt : τ p t) (h : ∀ q, R q p → ¬¬∃ (c : WFCode X) (z : {x : X // c.S x}), Sim R c q z) :
    t ∈ succ (encBound X) :=
  (hord p t hpt).mem_succ_of_subset (isOrd_encBound X)
    (subset_ht_of_sim R (encCode X) hc hord _ p t hpt (sim_top R h))

/-! ### The enlargement is necessary -/

/-- Every code covers its own heights. -/
theorem cover_ht {X : Type u} (c : WFCode X) : Cover c.R (fun z t => t ≈ c.ht z) :=
  fun _ _ _ e hξ => nn_map (fun ⟨y, h⟩ => ⟨y.1, c.ht y.1, y.2, Equiv.refl _, h⟩)
    (c.mem_ht.1 ((mem_congr_right e).1 hξ))

/-- The top of the enclosing tree is not simulated in any code on `X`: its height would then
be included in a height that belongs to it. -/
theorem not_sim_top {X : Type u} (c : WFCode X) (z : {x : X // c.S x}) :
    ¬ Sim (encCode X).R c (Enc.top X) z := fun hs =>
  have sub := subset_ht_of_sim (encCode X).R c (cover_ht (encCode X))
    (fun _ _ e => (encCode X).isOrd_ht _ |>.resp e.symm) z _ _ (Equiv.refl _) hs
  not_mem_self (c.ht z) ((mem_congr_left (ht_node c z)).1 (sub _ (ht_node_mem_encBound c z)))

/-- info: 'PSet.mem_succ_encBound_of_children' does not depend on any axioms -/
#guard_msgs in #print axioms mem_succ_encBound_of_children
/-- info: 'PSet.sim_of_subset_ht' does not depend on any axioms -/
#guard_msgs in #print axioms sim_of_subset_ht
/-- info: 'PSet.Coherent.cover' does not depend on any axioms -/
#guard_msgs in #print axioms Coherent.cover
/-- info: 'PSet.sim_iff_simI' does not depend on any axioms -/
#guard_msgs in #print axioms sim_iff_simI
/-- info: 'PSet.not_sim_top' does not depend on any axioms -/
#guard_msgs in #print axioms not_sim_top

end PSet
