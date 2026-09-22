import ConZF.Bar
import ConZF.EnvFml
/-!
A producer: total finite-observation specifications on the negative Cantor space have a
source-wide cap. A relation `P` from points of `powerset omega` to sets is *finite-observation*
(`FinObs`) when every witness at a point is, negatively, certified by a finite prefix and works
throughout its cylinder. Then negative totality gives, negatively, one ordinal capping the
witness ranks at every point (`cap_of_finObs`): a witness with its prefix caps its cylinder by
the successor of its rank, and `cap_of_bar` combines the local caps. No witness is computed, no
uniform generator is assumed, and the witness condition may have arbitrary quantifiers; the
restriction is the finite-observation dependence on the point and totality over all negative
points, including those made by Separation.

There is also a witness menu: negatively, one set meets the witness class of every point
(`menu_of_finObs`), built from singletons by binary unions along the bar. With functionality it
contains every output, so `rankBounded_of_mem` applies. Without functionality the menu meets
each witness class; it does not cover every output in the sense of `Cover.lean`.

The adapter `rankBounded_of_finObs` states the result for `Sat HG ψ` on the source
`powerset omega`, with the finite-observation property of `ψ` as an explicit hypothesis.
-/
universe u

namespace PSet
open Fml

section
variable (P : PSet.{u} → PSet.{u} → Prop)

/-- Every witness at a point is, negatively, certified by a finite prefix of the point and
works throughout the cylinder of that prefix. -/
def FinObs : Prop :=
  ∀ X, X ∈ powerset omega.{u} → ∀ y, P X y →
    ¬¬∃ s, Prec s X ∧ ∀ Z, Z ∈ powerset omega.{u} → Prec s Z → P Z y

/-- Negative totality on the source. -/
def NegTotal : Prop := ∀ X, X ∈ powerset omega.{u} → ¬¬∃ y, P X y

/-- **The cap.** A total finite-observation specification has a source-wide cap. -/
theorem cap_of_finObs (hfo : FinObs P) (htot : NegTotal P) :
    ¬¬∃ κ, IsOrd κ ∧ ∀ X, X ∈ powerset omega.{u} → ¬¬∃ y, P X y ∧ rank y ∈ κ := by
  have h := cap_of_bar P fun X hX => by
    refine Stable.of_nn (htot X hX) fun ⟨y, hy⟩ => ?_
    refine nn_map (fun ⟨s, hs, hcyl⟩ => ⟨s, hs, ?_⟩) (hfo X hX y hy)
    exact nn_intro ⟨succ (rank y), (isOrd_rank y).succ, fun Z hZ hp _ =>
      nn_intro ⟨y, hcyl Z hZ hp, self_mem_succ _⟩⟩
  exact nn_map (fun ⟨κ, hκ, hc⟩ => ⟨κ, hκ, fun X hX => hc X hX (htot X hX)⟩) h

/-- `m` meets the witness class of every point of the cylinder of `s`. -/
def MenuAt (m : PSet.{u}) (s : List Bool) : Prop :=
  ∀ X, X ∈ powerset omega.{u} → Prec s X → (¬¬∃ y, P X y) → ¬¬∃ y, y ∈ m ∧ P X y

def LocMenu (s : List Bool) : Prop := ¬¬∃ m : PSet.{u}, MenuAt P m s

instance {s : List Bool} : Stable (LocMenu P s) := inferInstanceAs (Stable (¬_))

theorem locMenu_join (s : List Bool) (h0 : LocMenu P (false :: s)) (h1 : LocMenu P (true :: s)) :
    LocMenu P s := by
  refine Stable.of_nn h0 fun ⟨m0, hm0⟩ => Stable.of_nn h1 fun ⟨m1, hm1⟩ => ?_
  refine nn_intro ⟨union m0 m1, fun X hX hp hE => ?_⟩
  refine Stable.by_cases (ofNat s.length ∈ X) (fun hb => ?_) fun hb => ?_
  · exact nn_map (fun ⟨y, hy, hP⟩ => ⟨y, mem_union.2 (nn_intro (.inr hy)), hP⟩)
      (hm1 X hX ⟨hp, fun _ => hb, fun _ => rfl⟩ hE)
  · exact nn_map (fun ⟨y, hy, hP⟩ => ⟨y, mem_union.2 (nn_intro (.inl hy)), hP⟩)
      (hm0 X hX ⟨hp, fun h => Bool.noConfusion h, fun h => (hb h).elim⟩ hE)

/-- **The witness menu.** Negatively, one set, a finite union of singletons along the bar,
meets the witness class of every point. -/
theorem menu_of_finObs (hfo : FinObs P) (htot : NegTotal P) :
    ¬¬∃ m : PSet.{u}, ∀ X, X ∈ powerset omega.{u} → ¬¬∃ y, y ∈ m ∧ P X y := by
  have h : LocMenu P [] := bar_induction (LocMenu P) (locMenu_join P) fun X hX => by
    refine Stable.of_nn (htot X hX) fun ⟨y, hy⟩ => ?_
    refine nn_map (fun ⟨s, hs, hcyl⟩ => ⟨s, hs, ?_⟩) (hfo X hX y hy)
    exact nn_intro ⟨singleton y, fun Z hZ hp _ =>
      nn_intro ⟨y, self_mem_singleton y, hcyl Z hZ hp⟩⟩
  exact nn_map (fun ⟨m, hm⟩ => ⟨m, fun X hX => hm X hX trivial (htot X hX)⟩) h

/-- With functionality, every output is in the menu. -/
theorem output_mem_menu {m : PSet.{u}}
    (hfun : ∀ X y y', X ∈ powerset omega.{u} → P X y → P X y' → y ≈ y')
    (hm : ∀ X, X ∈ powerset omega.{u} → ¬¬∃ y, y ∈ m ∧ P X y) :
    ∀ X y, X ∈ powerset omega.{u} → P X y → y ∈ m :=
  fun X y hX hy => Stable.of_nn (hm X hX) fun ⟨y', hy', hP⟩ =>
    (mem_congr_left (hfun X y' y hX hP hy)).1 hy'

end

/-- **The adapter.** A formula `ψ` that is finite-observation, negatively total and functional
on the negative Cantor space is rank bounded there. -/
theorem rankBounded_of_finObs {ψ : Fml} {e : Nat → PSet.{u}}
    (hfo : FinObs (Wit ψ · e ·)) (htot : NegTotal (Wit ψ · e ·))
    (hf : ∀ x y y', x ∈ powerset omega.{u} → HG y → HG y' →
      Sat HG ψ (Env.cons x (Env.cons y e)) → Sat HG ψ (Env.cons x (Env.cons y' e)) → y ≈ y') :
    RankBounded ψ e (powerset omega.{u}) := by
  refine Stable.of_nn (menu_of_finObs (Wit ψ · e ·) hfo htot) fun ⟨m, hm⟩ => ?_
  exact rankBounded_of_mem fun x y hx hy hs =>
    output_mem_menu (Wit ψ · e ·) (fun X y y' hX h h' => hf X y y' hX h.1 h'.1 h.2 h'.2) hm x y hx
      ⟨hy, hs⟩

/-- info: 'PSet.cap_of_finObs' does not depend on any axioms -/
#guard_msgs in #print axioms cap_of_finObs
/-- info: 'PSet.menu_of_finObs' does not depend on any axioms -/
#guard_msgs in #print axioms menu_of_finObs
/-- info: 'PSet.rankBounded_of_finObs' does not depend on any axioms -/
#guard_msgs in #print axioms rankBounded_of_finObs

end PSet
