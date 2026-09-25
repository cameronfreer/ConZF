import ConZF.CofinalCut
import ConZF.Reflection
/-!
A native majorant compiler for a certified fragment of the formula syntax (con42). A `Plan` is a
recipe whose interpretation `Plan.formula` is an actual `Fml` in the branch's convention (input
`0`, output `1`, parameters `2, 3, …`): copying the input or a parameter, an element or subset of
the input, the internal powerset formula, the union, relational composition and image (both
capturing the original input as a parameter), a conjunction with an *arbitrary* native test, and
disjunction. `Plan.bound` computes, by recursion on the plan and from an envelope of the source
and envelopes of the parameters, a native set containing every successful output.

* `Plan.sound`: in any transitive class, every output of the compiled formula lies in the
  computed envelope. No stability, closure, functionality, accessibility or model premise; the
  test of a guard is never evaluated, it only restricts where outputs can be.
* `Certificate ψ`: a plan together with the equation `plan.formula = ψ`, checked by Lean, so the
  original matrix is bounded, not a related one. `isat_original_rank_bound`: for the actual
  interpreter `ISat`, a native ordinal bounding all output ranks on a source, uniform in the
  stage. `certifiedRankBounded`, `certifiedReplacement`: the instancewise rank bound and the
  `HG` collecting set for a certified matrix, through the unchanged consumers.
* The nested example `stress T = Image (Image (Guard (Compose Power Power) T))`, for any test
  `T`: its envelope is `𝒫⁵ (⋃³ s)` (`stress_envelope`), an image formula is functional in any
  transitive class (`imageF_functional`), and `stress_replacement` is the resulting `HG`
  Replacement instance with no hypothesis beyond `HG` of the source and parameters.

This is an unconditional producer for the certified fragment only; it says nothing about the
ordinal-decoder barrier, whose outputs are not built by these constructors.
-/
universe u

namespace PSet.Majorant
open Fml CardF Reflection

/-! ### The fragment -/

/-- `y ⊆ x`. -/
def subsetF : Fml := all (imp (mem 0 2) (mem 0 1))

/-- `y = ⋃ x`. -/
def unionF : Fml := all (iff (mem 0 2) (ex (and (mem 0 2) (mem 1 0))))

/-- Under `[z, x, y, e…]`, the left formula reads `[x, z, e…]`. -/
def leftRen : Nat → Nat
  | 0 => 1
  | 1 => 0
  | i+2 => i+3

/-- Under `[z, x, y, e…]`, the right formula reads `[z, y, x, e…]`. -/
def rightRen : Nat → Nat
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | i+3 => i+3

/-- Under `[a, z, x, y, e…]`, the image body reads `[a, z, x, e…]`; it cannot see `y`. -/
def imageRen : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | i+3 => i+4

/-- `∃ z (p x z ∧ q z y x)`. -/
def composeF (p q : Fml) : Fml := ex (and (rename leftRen p) (rename rightRen q))

/-- `∀ z (z ∈ y ↔ ∃ a ∈ x, p a z x)`. -/
def imageF (p : Fml) : Fml := all (iff (mem 0 2) (ex (and (mem 0 2) (rename imageRen p))))

/-- Certificates. `formula` builds the actual formula; `bound` its native envelope. -/
inductive Plan : Type
  | input
  | parameter (j : Nat)
  | element
  | subset
  | power
  | union
  | compose (p q : Plan)
  | image (p : Plan)
  | guard (p : Plan) (test : Fml)
  | either (p q : Plan)

def Plan.formula : Plan → Fml
  | .input => eq 1 0
  | .parameter j => eq 1 (j+2)
  | .element => mem 1 0
  | .subset => subsetF
  | .power => powF 1 0
  | .union => unionF
  | .compose p q => composeF p.formula q.formula
  | .image p => imageF p.formula
  | .guard p test => and p.formula test
  | .either p q => or p.formula q.formula

/-- The envelope: `P j` contains parameter `j`, `A` contains the input. -/
def Plan.bound : Plan → (Nat → PSet.{u}) → PSet.{u} → PSet.{u}
  | .input, _, A => A
  | .parameter j, P, _ => P j
  | .element, _, A => sUnion A
  | .subset, _, A => powerset (sUnion A)
  | .power, _, A => powerset (powerset (sUnion A))
  | .union, _, A => powerset (sUnion (sUnion A))
  | .compose p q, P, A => q.bound (Env.cons A P) (p.bound P A)
  | .image p, P, A => powerset (p.bound (Env.cons A P) (sUnion A))
  | .guard p _, P, A => p.bound P A
  | .either p q, P, A => PSet.union (p.bound P A) (q.bound P A)

/-- A declared arity, not necessarily minimal. -/
def Plan.scope (p : Plan) : Nat := fv p.formula

theorem Plan.bound_formula (p : Plan) : Bound (p.scope+2) p.formula :=
  (bound_fv p.formula).mono (Nat.le_add_right _ 2)

theorem read_left {M : PSet.{u} → Prop} (p : Fml) (x y z : PSet.{u}) (e : Nat → PSet.{u}) :
    Sat M (rename leftRen p) (Env.cons z (Env.cons x (Env.cons y e))) ↔
      Sat M p (Env.cons x (Env.cons z e)) :=
  (sat_rename p leftRen _).trans (Sat.resp_iff (fun _ => Iff.rfl) p
    fun i => by rcases i with _ | _ | i <;> exact Equiv.refl _)

theorem read_right {M : PSet.{u} → Prop} (p : Fml) (x y z : PSet.{u}) (e : Nat → PSet.{u}) :
    Sat M (rename rightRen p) (Env.cons z (Env.cons x (Env.cons y e))) ↔
      Sat M p (Env.cons z (Env.cons y (Env.cons x e))) :=
  (sat_rename p rightRen _).trans (Sat.resp_iff (fun _ => Iff.rfl) p
    fun i => by rcases i with _ | _ | _ | i <;> exact Equiv.refl _)

theorem read_image {M : PSet.{u} → Prop} (p : Fml) (x y z a : PSet.{u}) (e : Nat → PSet.{u}) :
    Sat M (rename imageRen p) (Env.cons a (Env.cons z (Env.cons x (Env.cons y e)))) ↔
      Sat M p (Env.cons a (Env.cons z (Env.cons x e))) :=
  (sat_rename p imageRen _).trans (Sat.resp_iff (fun _ => Iff.rfl) p
    fun i => by rcases i with _ | _ | _ | i <;> exact Equiv.refl _)

theorem sat_composeF {M : PSet.{u} → Prop} (p q : Fml) (x y : PSet.{u}) (e : Nat → PSet.{u}) :
    Sat M (composeF p q) (Env.cons x (Env.cons y e)) ↔
      ¬¬∃ z, M z ∧ Sat M p (Env.cons x (Env.cons z e)) ∧
        Sat M q (Env.cons z (Env.cons y (Env.cons x e))) :=
  sat_ex.trans (nn_congr
    ⟨fun ⟨z, hz, hs⟩ => ⟨z, hz, (read_left p x y z e).1 (sat_and.1 hs).1,
      (read_right q x y z e).1 (sat_and.1 hs).2⟩,
     fun ⟨z, hz, hp, hq⟩ => ⟨z, hz, sat_and.2 ⟨(read_left p x y z e).2 hp, (read_right q x y z e).2 hq⟩⟩⟩)

/-- **Soundness** in any transitive class: every output lies in the envelope. -/
theorem Plan.sound {M : PSet.{u} → Prop} (tr : ∀ {a z}, M a → z ∈ a → M z) :
    ∀ (p : Plan) (e P : Nat → PSet.{u}) (A x y : PSet.{u}), (∀ j, e j ∈ P j) → M x → M y → x ∈ A →
      Sat M p.formula (Env.cons x (Env.cons y e)) → y ∈ p.bound P A
  | .input, _, _, _, _, _, _, _, _, hA, hs => (mem_congr_left hs).2 hA
  | .parameter j, _, _, _, _, _, hp, _, _, _, hs => (mem_congr_left hs).2 (hp j)
  | .element, _, _, _, x, _, _, _, _, hA, hs => mem_sUnion.2 (nn_intro ⟨x, hA, hs⟩)
  | .subset, _, _, _, x, _, _, _, hy, hA, hs =>
    mem_powerset.2 fun z hz => mem_sUnion.2 (nn_intro ⟨x, hA, hs z (tr hy hz) hz⟩)
  | .power, _, _, _, x, _, _, _, hy, hA, hs =>
    mem_powerset.2 fun z hz => mem_powerset.2 fun t ht =>
      mem_sUnion.2 (nn_intro ⟨x, hA, (sat_iff.1 (hs z (tr hy hz))).1 hz t (tr (tr hy hz) ht) ht⟩)
  | .union, _, _, _, x, _, _, _, hy, hA, hs =>
    mem_powerset.2 fun z hz =>
      Stable.of_nn (sat_ex.1 ((sat_iff.1 (hs z (tr hy hz))).1 hz)) fun ⟨a, _, hs⟩ =>
        mem_sUnion.2 (nn_intro ⟨a, mem_sUnion.2 (nn_intro ⟨x, hA, (sat_and.1 hs).1⟩), (sat_and.1 hs).2⟩)
  | .compose p q, e, P, A, x, y, hp, hx, hy, hA, hs =>
    Stable.of_nn ((sat_composeF p.formula q.formula x y e).1 hs) fun ⟨z, hz, hpz, hqz⟩ =>
      Plan.sound tr q (Env.cons x e) (Env.cons A P) (p.bound P A) z y
        (fun j => by cases j with | zero => exact hA | succ j => exact hp j)
        hz hy (Plan.sound tr p e P A x z hp hx hz hA hpz) hqz
  | .image p, e, P, A, x, y, hp, _, hy, hA, hs =>
    mem_powerset.2 fun z hz =>
      Stable.of_nn (sat_ex.1 ((sat_iff.1 (hs z (tr hy hz))).1 hz)) fun ⟨a, ha, hs⟩ =>
        Plan.sound tr p (Env.cons x e) (Env.cons A P) (sUnion A) a z
          (fun j => by cases j with | zero => exact hA | succ j => exact hp j)
          ha (tr hy hz) (mem_sUnion.2 (nn_intro ⟨x, hA, (sat_and.1 hs).1⟩))
          ((read_image p.formula x y z a e).1 (sat_and.1 hs).2)
  | .guard p _, e, P, A, x, y, hp, hx, hy, hA, hs =>
    Plan.sound tr p e P A x y hp hx hy hA (sat_and.1 hs).1
  | .either p q, e, P, A, x, y, hp, hx, hy, hA, hs =>
    Stable.of_nn (sat_or.1 hs) fun
      | .inl h => mem_union.2 (nn_intro (.inl (Plan.sound tr p e P A x y hp hx hy hA h)))
      | .inr h => mem_union.2 (nn_intro (.inr (Plan.sound tr q e P A x y hp hx hy hA h)))

/-! ### Certificates and the interpreter -/

/-- The parameter envelopes: singletons of the actual parameters. -/
def parameterCaps (e : Nat → PSet.{u}) : Nat → PSet.{u} := fun j => singleton (e j)

/-- The envelope of a plan at a source `s` with parameters `e`. -/
def envelope (p : Plan) (e : Nat → PSet.{u}) (s : PSet.{u}) : PSet.{u} :=
  p.bound (parameterCaps e) s

/-- A certificate for an original matrix: a plan and the checked equation. -/
structure Certificate (ψ : Fml) where
  plan : Plan
  equation : plan.formula = ψ

theorem class_envelope {M : PSet.{u} → Prop} (tr : ∀ {a z}, M a → z ∈ a → M z) {ψ : Fml}
    (cert : Certificate ψ) {s x y : PSet.{u}} {e : Nat → PSet.{u}} (hx : M x) (hy : M y)
    (hxs : x ∈ s) (hs : Sat M ψ (Env.cons x (Env.cons y e))) : y ∈ envelope cert.plan e s :=
  cert.plan.sound tr e (parameterCaps e) s x y (fun _ => mem_singleton.2 (Equiv.refl _)) hx hy hxs
    (cert.equation.symm ▸ hs)

section
variable [Budget.{u}]

omit [Budget.{u}] in
/-- Every output of the interpreter at a certified code lies in the envelope, at every stage. -/
theorem isat_original_envelope {ψ : Fml} (cert : Certificate ψ) {n : Nat} (hb : Bound (n+2) ψ)
    {η s x y : PSet.{u}} {e : Nat → PSet.{u}} (hx : x ∈ s) (h : ISat η (code ψ n e) x y) :
    y ∈ envelope cert.plan e s :=
  have ⟨hxV, hyV, hs⟩ := (isat_code hb).1 h
  class_envelope (fun ha hz => Vl_trans ha hz) cert hxV hyV hx hs

omit [Budget.{u}] in
/-- **A native ordinal bound on the ranks of all outputs**, uniform in the stage. -/
theorem isat_original_rank_bound {ψ : Fml} (cert : Certificate ψ) {n : Nat} (hb : Bound (n+2) ψ)
    (s : PSet.{u}) (e : Nat → PSet.{u}) :
    IsOrd (rank (envelope cert.plan e s)) ∧
      ∀ η x y, x ∈ s → ISat η (code ψ n e) x y → rank y ∈ rank (envelope cert.plan e s) :=
  ⟨isOrd_rank _, fun _ _ _ hx h => rank_mem (isat_original_envelope cert hb hx h)⟩

theorem hg_original_output_bound {ψ : Fml} (cert : Certificate ψ) {a : PSet.{u}}
    {e : Nat → PSet.{u}} (ha : HG a) {x y : PSet.{u}} (hx : x ∈ a) (hy : HG y)
    (hs : Sat HG ψ (Env.cons x (Env.cons y e))) : y ∈ envelope cert.plan e a :=
  class_envelope (fun hz hw => HG.mem hz hw) cert (HG.mem ha hx) hy hx hs

/-- The instancewise rank bound of the model's Replacement clause, for a certified matrix. -/
theorem certifiedRankBounded {ψ : Fml} (cert : Certificate ψ) {a : PSet.{u}} (e : Nat → PSet.{u})
    (ha : HG a) : RankBounded ψ e a :=
  rankBounded_of_mem fun _ _ hx hy hs => hg_original_output_bound cert ha hx hy hs

/-- One original admissible `HG` Replacement instance, closed by a certificate. -/
theorem certifiedReplacement {ψ : Fml} (cert : Certificate ψ) {a : PSet.{u}} {e : Nat → PSet.{u}}
    (ha : HG a) (he : ∀ i, HG (e i))
    (hf : ∀ x y y', x ∈ a → HG y → HG y' → Sat HG ψ (Env.cons x (Env.cons y e)) →
      Sat HG ψ (Env.cons x (Env.cons y' e)) → y ≈ y') :
    ¬¬∃ b, HG b ∧ ∀ x y, x ∈ a → HG y → Sat HG ψ (Env.cons x (Env.cons y e)) → y ∈ b :=
  hg_replacement_of_rank_bound (κ := rank (envelope cert.plan e a)) (isOrd_rank _) ha he hf
    fun _ _ hx hy hs => rank_mem (hg_original_output_bound cert ha hx hy hs)

end

/-! ### The nested example -/

/-- A nested image with an arbitrary test, possibly unbounded and negative. -/
def stress (test : Fml) : Plan := .image (.image (.guard (.compose .power .power) test))

theorem powerset_congr' {a a' : PSet.{u}} (e : a ≈ a') : powerset a ≈ powerset a' :=
  ext fun _ => mem_powerset.trans (.trans
    ⟨fun h w hw => (mem_congr_right e).1 (h w hw), fun h w hw => (mem_congr_right e).2 (h w hw)⟩
    mem_powerset.symm)

theorem sUnion_powerset (Y : PSet.{u}) : sUnion (powerset Y) ≈ Y :=
  ext fun z => ⟨fun h => Stable.of_nn (mem_sUnion.1 h) fun ⟨_, hw, hzw⟩ => mem_powerset.1 hw z hzw,
    fun h => mem_sUnion.2 (nn_intro ⟨singleton z,
      mem_powerset.2 fun _ hw => (mem_congr_left (mem_singleton.1 hw)).2 h, self_mem_singleton z⟩)⟩

/-- The envelope of the nested example is `𝒫⁵ (⋃³ s)`, for every test and every parameter list. -/
theorem stress_envelope (test : Fml) (e : Nat → PSet.{u}) (s : PSet.{u}) :
    envelope (stress test) e s ≈
      powerset (powerset (powerset (powerset (powerset (sUnion (sUnion (sUnion s))))))) :=
  powerset_congr' (powerset_congr' (powerset_congr' (powerset_congr' (sUnion_powerset _))))

/-- The image body reads independently of the output slot. -/
theorem image_body_iff {M : PSet.{u} → Prop} (p : Fml) (x y z : PSet.{u}) (e : Nat → PSet.{u}) :
    Sat M (ex (and (mem 0 2) (rename imageRen p))) (Env.cons z (Env.cons x (Env.cons y e))) ↔
      ¬¬∃ a, M a ∧ a ∈ x ∧ Sat M p (Env.cons a (Env.cons z (Env.cons x e))) :=
  sat_ex.trans (nn_congr
    ⟨fun ⟨a, ha, hs⟩ => ⟨a, ha, (sat_and.1 hs).1, (read_image p x y z a e).1 (sat_and.1 hs).2⟩,
     fun ⟨a, ha, hax, hs⟩ => ⟨a, ha, sat_and.2 ⟨hax, (read_image p x y z a e).2 hs⟩⟩⟩)

/-- An image formula is functional in any transitive class. -/
theorem imageF_functional {M : PSet.{u} → Prop} (tr : ∀ {a z}, M a → z ∈ a → M z) (p : Fml)
    {x y y' : PSet.{u}} {e : Nat → PSet.{u}} (hy : M y) (hy' : M y')
    (h : Sat M (imageF p) (Env.cons x (Env.cons y e)))
    (h' : Sat M (imageF p) (Env.cons x (Env.cons y' e))) : y ≈ y' :=
  ext fun z => ⟨fun hz => (sat_iff.1 (h' z (tr hy hz))).2 ((image_body_iff p x y' z e).2
      ((image_body_iff p x y z e).1 ((sat_iff.1 (h z (tr hy hz))).1 hz))),
    fun hz => (sat_iff.1 (h z (tr hy' hz))).2 ((image_body_iff p x y z e).2
      ((image_body_iff p x y' z e).1 ((sat_iff.1 (h' z (tr hy' hz))).1 hz)))⟩

/-- **The end-to-end nested instance.** For any test, the `HG` Replacement instance of the
nested image at an `HG` source with `HG` parameters has an `HG` collecting set. -/
theorem stress_replacement [Budget.{u}] (test : Fml) {a : PSet.{u}} {e : Nat → PSet.{u}}
    (ha : HG a) (he : ∀ i, HG (e i)) :
    ¬¬∃ b, HG b ∧ ∀ x y, x ∈ a → HG y →
      Sat HG (stress test).formula (Env.cons x (Env.cons y e)) → y ∈ b :=
  certifiedReplacement ⟨stress test, rfl⟩ ha he fun _ _ _ _ hy hy' h h' =>
    imageF_functional (fun hz hw => HG.mem hz hw) _ hy hy' h h'

/-- info: 'PSet.Majorant.Plan.sound' does not depend on any axioms -/
#guard_msgs in #print axioms Plan.sound
/-- info: 'PSet.Majorant.isat_original_rank_bound' does not depend on any axioms -/
#guard_msgs in #print axioms isat_original_rank_bound
/-- info: 'PSet.Majorant.certifiedReplacement' does not depend on any axioms -/
#guard_msgs in #print axioms certifiedReplacement
/-- info: 'PSet.Majorant.stress_envelope' does not depend on any axioms -/
#guard_msgs in #print axioms stress_envelope
/-- info: 'PSet.Majorant.stress_replacement' does not depend on any axioms -/
#guard_msgs in #print axioms stress_replacement

end PSet.Majorant
