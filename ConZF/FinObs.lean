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

There is also a finite witness menu: negatively, one finite list of sets meets the witness
class of every point (`menu_of_finObs`), singleton lists concatenated along the bar; the list
is in the conclusion, so finiteness is certified. With functionality every output is bisimilar
to an entry of the list (`output_mem_menu`), so the image is finite and `rankBounded_of_mem`
applies to the set of the list. Without functionality the menu meets each witness class; it
does not cover every output in the sense of `Cover.lean`.

The adapters state the result for `Sat HG ψ` on the source `powerset omega`, with the
finite-observation property of `ψ` as an explicit hypothesis: `rankBounded_of_finObs` for a
functional `ψ`, and `rankBounded_envFml_of_finObs` for the envelope instance of any `ψ`, which
needs no functionality and does not assume that envelope formation preserves finite observation.
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

theorem List.mem_append_left' {α : Type _} {y : α} : ∀ {l l' : List α}, y ∈ l → y ∈ l ++ l'
  | _ :: _, _, .head _ => .head _
  | _ :: _, _, .tail _ h => .tail _ (List.mem_append_left' h)

theorem List.mem_append_right' {α : Type _} {y : α} : ∀ (l : List α) {l' : List α}, y ∈ l' → y ∈ l ++ l'
  | [], _, h => h
  | _ :: l, _, h => .tail _ (List.mem_append_right' l h)

/-- The finite list `l` meets the witness class of every point of the cylinder of `s`. -/
def MenuAt (l : List PSet.{u}) (s : List Bool) : Prop :=
  ∀ X, X ∈ powerset omega.{u} → Prec s X → (¬¬∃ y, P X y) → ¬¬∃ y, y ∈ l ∧ P X y

def LocMenu (s : List Bool) : Prop := ¬¬∃ l : List PSet.{u}, MenuAt P l s

instance {s : List Bool} : Stable (LocMenu P s) := inferInstanceAs (Stable (¬_))

theorem locMenu_join (s : List Bool) (h0 : LocMenu P (false :: s)) (h1 : LocMenu P (true :: s)) :
    LocMenu P s := by
  refine Stable.of_nn h0 fun ⟨l0, hl0⟩ => Stable.of_nn h1 fun ⟨l1, hl1⟩ => ?_
  refine nn_intro ⟨l0 ++ l1, fun X hX hp hE => ?_⟩
  refine Stable.by_cases (ofNat s.length ∈ X) (fun hb => ?_) fun hb => ?_
  · exact nn_map (fun ⟨y, hy, hP⟩ => ⟨y, List.mem_append_right' l0 hy, hP⟩)
      (hl1 X hX ⟨hp, fun _ => hb, fun _ => rfl⟩ hE)
  · exact nn_map (fun ⟨y, hy, hP⟩ => ⟨y, List.mem_append_left' hy, hP⟩)
      (hl0 X hX ⟨hp, fun h => Bool.noConfusion h, fun h => (hb h).elim⟩ hE)

/-- **The finite witness menu.** Negatively, one finite list of sets meets the witness class of
every point. -/
theorem menu_of_finObs (hfo : FinObs P) (htot : NegTotal P) :
    ¬¬∃ l : List PSet.{u}, ∀ X, X ∈ powerset omega.{u} → ¬¬∃ y, y ∈ l ∧ P X y := by
  have h : LocMenu P [] := bar_induction (LocMenu P) (locMenu_join P) fun X hX => by
    refine Stable.of_nn (htot X hX) fun ⟨y, hy⟩ => ?_
    refine nn_map (fun ⟨s, hs, hcyl⟩ => ⟨s, hs, ?_⟩) (hfo X hX y hy)
    exact nn_intro ⟨[y], fun Z hZ hp _ => nn_intro ⟨y, .head _, hcyl Z hZ hp⟩⟩
  exact nn_map (fun ⟨l, hl⟩ => ⟨l, fun X hX => hl X hX trivial (htot X hX)⟩) h

/-- With functionality, every output is bisimilar to an entry of the menu: the image is finite. -/
theorem output_mem_menu {l : List PSet.{u}}
    (hfun : ∀ X y y', X ∈ powerset omega.{u} → P X y → P X y' → y ≈ y')
    (hl : ∀ X, X ∈ powerset omega.{u} → ¬¬∃ y, y ∈ l ∧ P X y) :
    ∀ X y, X ∈ powerset omega.{u} → P X y → ¬¬∃ y', y' ∈ l ∧ y ≈ y' :=
  fun X y hX hy => nn_map (fun ⟨y', hy', hP⟩ => ⟨y', hy', hfun X y y' hX hy hP⟩) (hl X hX)

end

/-- The set of a finite list. -/
def ofList : List PSet.{u} → PSet.{u}
  | [] => empty
  | y :: l => union (singleton y) (ofList l)

theorem mem_ofList {z : PSet.{u}} : ∀ {l : List PSet.{u}}, z ∈ ofList l ↔ ¬¬∃ y, y ∈ l ∧ z ≈ y
  | [] => ⟨fun h => (not_mem_empty z h).elim, fun h => Stable.of_nn h fun ⟨_, h, _⟩ => nomatch h⟩
  | y :: l => mem_union.trans ⟨fun h => Stable.of_nn h fun
      | .inl h => nn_intro ⟨y, .head _, mem_singleton.1 h⟩
      | .inr h => nn_map (fun ⟨y', h, e⟩ => ⟨y', .tail _ h, e⟩) (mem_ofList.1 h),
    fun h => Stable.of_nn h fun ⟨y', hy', e⟩ => by
      cases hy' with
      | head => exact nn_intro (.inl (mem_singleton.2 e))
      | tail _ hy' => exact nn_intro (.inr (mem_ofList.2 (nn_intro ⟨y', hy', e⟩)))⟩

end

/-- **The adapter.** A formula `ψ` that is finite-observation, negatively total and functional
on the negative Cantor space is rank bounded there. -/
theorem rankBounded_of_finObs {ψ : Fml} {e : Nat → PSet.{u}}
    (hfo : FinObs (Wit ψ · e ·)) (htot : NegTotal (Wit ψ · e ·))
    (hf : ∀ x y y', x ∈ powerset omega.{u} → HG y → HG y' →
      Sat HG ψ (Env.cons x (Env.cons y e)) → Sat HG ψ (Env.cons x (Env.cons y' e)) → y ≈ y') :
    RankBounded ψ e (powerset omega.{u}) := by
  refine Stable.of_nn (menu_of_finObs (Wit ψ · e ·) hfo htot) fun ⟨l, hl⟩ => ?_
  refine rankBounded_of_mem (K := ofList l) fun x y hx hy hs => mem_ofList.2 ?_
  exact output_mem_menu (Wit ψ · e ·) (fun X y y' hX h h' => hf X y y' hX h.1 h'.1 h.2 h'.2) hl x y
    hx ⟨hy, hs⟩

/-- **The envelope adapter.** The envelope instance of any finite-observation, negatively total
`ψ` is rank bounded on the source; no functionality of `ψ` is needed. -/
theorem rankBounded_envFml_of_finObs {ψ : Fml} {e : Nat → PSet.{u}}
    (hfo : FinObs (Wit ψ · e ·)) (htot : NegTotal (Wit ψ · e ·)) :
    RankBounded (envFml ψ) e (powerset omega.{u}) :=
  rankBounded_envFml_of_cap <| nn_map (fun ⟨κ, hκ, hc⟩ => ⟨κ, hκ, fun X hX _ =>
    nn_map (fun ⟨y, hy, hr⟩ => ⟨y, hy, (mem_Vl_ord hκ).2 hr⟩) (hc X hX)⟩)
    (cap_of_finObs (Wit ψ · e ·) hfo htot)

/-- info: 'PSet.cap_of_finObs' does not depend on any axioms -/
#guard_msgs in #print axioms cap_of_finObs
/-- info: 'PSet.menu_of_finObs' does not depend on any axioms -/
#guard_msgs in #print axioms menu_of_finObs
/-- info: 'PSet.rankBounded_of_finObs' does not depend on any axioms -/
#guard_msgs in #print axioms rankBounded_of_finObs
/-- info: 'PSet.rankBounded_envFml_of_finObs' does not depend on any axioms -/
#guard_msgs in #print axioms rankBounded_envFml_of_finObs

end PSet
