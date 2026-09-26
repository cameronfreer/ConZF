import ConZF.Majorant
import ConZF.DecodeSpectrum
/-!
Already constructed output sets are hereditarily good (conzf23). An arbitrary supplied native set
`Y` whose members are `HG` outputs of one partial functional relation on an `HG` source, with
negative source names, is `HG`: its own rank is the cap of the cofinal cut, and the cut is
hereditarily good at every cap (`hg_of_definably_covered`). Nothing is constructed: `Y` is data,
and the lemma does not turn `∀ x, ¬¬∃ y, R x y` into a family. Special case: the range of an
actual source-indexed family of outputs (`hg_range_of_definable`).

For the certified fragment of `Majorant`, the envelope itself is `HG` on `HG` data
(`plan_bound_hg`, `envelope_hg`), so the exact relational image `outputSet` is an `HG` set with
the exact membership law `mem_outputSet`, with no functionality or totality premise.
-/
universe u

namespace PSet
open Fml OrdDecode
variable [Budget.{u}]

/-- **A supplied set of outputs is `HG`.** `Y` is native data; its rank is the cap. -/
theorem hg_of_definably_covered {a Y : PSet.{u}} {ψ : Fml} {e : Nat → PSet.{u}} (ha : HG a)
    (he : ∀ j, HG (e j))
    (hf : ∀ x y z, x ∈ a → HG y → HG z → Sat HG ψ (Env.cons x (Env.cons y e)) →
      Sat HG ψ (Env.cons x (Env.cons z e)) → y ≈ z)
    (hc : ∀ y, y ∈ Y → HG y ∧ ¬¬∃ x, x ∈ a ∧ Sat HG ψ (Env.cons x (Env.cons y e))) : HG Y :=
  HG.of_bound (cls_rankCofinalCut (isOrd_rank Y) ha he hf) fun y hy =>
    Stable.of_nn (hc y hy).2 fun ⟨_, hx, hs⟩ =>
      rank_mem_rankCofinalCut hx (hc y hy).1 hs (rank_mem hy)

/-- The range of an actual family of outputs is `HG`. -/
theorem hg_range_of_definable {a : PSet.{u}} {ψ : Fml} {e : Nat → PSet.{u}} (f : a.Idx → PSet.{u})
    (ha : HG a) (he : ∀ j, HG (e j))
    (hf : ∀ x y z, x ∈ a → HG y → HG z → Sat HG ψ (Env.cons x (Env.cons y e)) →
      Sat HG ψ (Env.cons x (Env.cons z e)) → y ≈ z)
    (hval : ∀ i, HG (f i)) (hspec : ∀ i, Sat HG ψ (Env.cons (a.Func i) (Env.cons (f i) e))) :
    HG (range f) :=
  hg_of_definably_covered ha he hf fun y hy =>
    ⟨Stable.of_nn (mem_range.1 hy) fun ⟨i, ei⟩ => HG.resp ei.symm (hval i),
     nn_map (fun ⟨i, ei⟩ => ⟨a.Func i, func_mem a i,
       Sat.resp ψ (fun j => by rcases j with _ | _ | j <;> first | exact Equiv.refl _ | exact ei.symm)
         (hspec i)⟩) (mem_range.1 hy)⟩

/-! ### The certified fragment -/

theorem hg_sep (P : PSet.{u} → Prop) {a : PSet.{u}} (ha : HG a) : HG (sep P a) :=
  hg_subclosed ha fun _ hz => Stable.of_nn hz fun ⟨⟨i, _⟩, e⟩ => nn_intro ⟨i, e⟩

/-- The envelope of a plan is `HG` on `HG` envelopes. -/
theorem plan_bound_hg : ∀ (p : Majorant.Plan) (P : Nat → PSet.{u}) (A : PSet.{u}),
    (∀ j, HG (P j)) → HG A → HG (p.bound P A)
  | .input, _, _, _, hA => hA
  | .parameter j, _, _, hP, _ => hP j
  | .element, _, _, _, hA => hg_sUnion hA
  | .subset, _, _, _, hA => hg_powerset (hg_sUnion hA)
  | .power, _, _, _, hA => hg_powerset (hg_powerset (hg_sUnion hA))
  | .union, _, _, _, hA => hg_powerset (hg_sUnion (hg_sUnion hA))
  | .compose p q, P, A, hP, hA =>
    plan_bound_hg q (Env.cons A P) (p.bound P A)
      (fun j => by cases j with | zero => exact hA | succ j => exact hP j)
      (plan_bound_hg p P A hP hA)
  | .image p, P, A, hP, hA =>
    hg_powerset (plan_bound_hg p (Env.cons A P) (sUnion A)
      (fun j => by cases j with | zero => exact hA | succ j => exact hP j) (hg_sUnion hA))
  | .guard p _, P, A, hP, hA => plan_bound_hg p P A hP hA
  | .either p q, P, A, hP, hA => hg_union (plan_bound_hg p P A hP hA) (plan_bound_hg q P A hP hA)

theorem envelope_hg (p : Majorant.Plan) {e : Nat → PSet.{u}} {A : PSet.{u}} (he : ∀ j, HG (e j))
    (hA : HG A) : HG (Majorant.envelope p e A) :=
  plan_bound_hg p (Majorant.parameterCaps e) A (fun j => (he j).singleton) hA

/-- The exact relational image of a certified matrix on a source, by Separation in the envelope. -/
def outputSet {ψ : Fml} (cert : Majorant.Certificate ψ) (e : Nat → PSet.{u}) (A : PSet.{u}) :
    PSet.{u} :=
  sep (fun y => HG y ∧ ¬¬∃ x, x ∈ A ∧ Sat HG ψ (Env.cons x (Env.cons y e)))
    (Majorant.envelope cert.plan e A)

/-- **Exact membership**, with no functionality or totality premise. -/
theorem mem_outputSet {ψ : Fml} (cert : Majorant.Certificate ψ) {e : Nat → PSet.{u}} {A : PSet.{u}}
    (hA : HG A) (y : PSet.{u}) :
    y ∈ outputSet cert e A ↔ HG y ∧ ¬¬∃ x, x ∈ A ∧ Sat HG ψ (Env.cons x (Env.cons y e)) := by
  refine (mem_sep fun y y' ey h => ⟨HG.resp ey h.1, nn_map (fun ⟨x, hx, hs⟩ => ⟨x, hx,
    Sat.resp ψ (fun j => by rcases j with _ | _ | j <;> first | exact Equiv.refl _ | exact ey) hs⟩)
    h.2⟩).trans ⟨And.right, fun h => ⟨?_, h⟩⟩
  exact Stable.of_nn h.2 fun ⟨_, hx, hs⟩ => Majorant.hg_original_output_bound cert hA hx h.1 hs

theorem outputSet_hg {ψ : Fml} (cert : Majorant.Certificate ψ) {e : Nat → PSet.{u}} {A : PSet.{u}}
    (he : ∀ j, HG (e j)) (hA : HG A) : HG (outputSet cert e A) :=
  hg_sep _ (envelope_hg cert.plan he hA)

/-- info: 'PSet.hg_of_definably_covered' does not depend on any axioms -/
#guard_msgs in #print axioms hg_of_definably_covered
/-- info: 'PSet.hg_range_of_definable' does not depend on any axioms -/
#guard_msgs in #print axioms hg_range_of_definable
/-- info: 'PSet.plan_bound_hg' does not depend on any axioms -/
#guard_msgs in #print axioms plan_bound_hg
/-- info: 'PSet.mem_outputSet' does not depend on any axioms -/
#guard_msgs in #print axioms mem_outputSet
/-- info: 'PSet.outputSet_hg' does not depend on any axioms -/
#guard_msgs in #print axioms outputSet_hg

end PSet
