import ConZF.CofinalCut
/-!
Native covers. A relation `F` is *covered* at an input `x` by a small type `C` of candidates with
a decoder `e : C → PSet.{u}` when every output at `x` is not not the value of some candidate
(`Covers`). Candidates may be wrong: the family only has to contain every genuine output,
negatively. Generating candidates needs native data; testing them may use arbitrary predicates
in `Prop`.

* `rank_mem_of_covers`: covers at the literal inputs of a domain `a`, with candidate types
  depending on the literal index, bound the ranks of all outputs on `a` by the rank of the
  combined range, an unconditional term (`coverBound`). For an admissible instance over `HG`
  this is `RankBounded` (`rankBounded_of_covers`).
* `covers_comp`: covers compose through an existential intermediate,
  `¬¬∃ z, F x z ∧ G z y`, by a dependent sum of candidate types, provided `G` respects
  bisimulation in its input, so that it accepts the reconstructed intermediate value. No choice
  of intermediate is made: the negative witnesses are opened inside the stable goal.
-/
universe u

namespace PSet

/-- `F` is covered at `x` by the candidates `e : C → PSet`. -/
def Covers (F : PSet.{u} → PSet.{u} → Prop) (x : PSet.{u}) {C : Type u} (e : C → PSet.{u}) :
    Prop :=
  ∀ y, F x y → ¬¬∃ c, e c ≈ y

/-- The combined range of candidate families over the literal indices of `a`. -/
def coverBound (a : PSet.{u}) {C : a.Idx → Type u} (e : (i : a.Idx) → C i → PSet.{u}) :
    PSet.{u} :=
  rank (range fun p : Σ i, C i => e p.1 p.2)

theorem isOrd_coverBound (a : PSet.{u}) {C : a.Idx → Type u} (e : (i : a.Idx) → C i → PSet.{u}) :
    IsOrd (coverBound a e) := isOrd_rank _

/-- Covers at the literal inputs bound the ranks of all outputs on the domain. -/
theorem rank_mem_of_covers {F : PSet.{u} → PSet.{u} → Prop}
    (hresp : ∀ {x x' y}, x ≈ x' → F x y → F x' y) {a : PSet.{u}} {C : a.Idx → Type u}
    {e : (i : a.Idx) → C i → PSet.{u}} (hcov : ∀ i, Covers F (a.Func i) (e i)) :
    ∀ x y, x ∈ a → F x y → rank y ∈ coverBound a e := by
  intro x y hx hxy
  refine hx.elim fun i ex => ?_
  refine Stable.of_nn (hcov i y (hresp ex hxy)) fun ⟨c, ec⟩ => ?_
  exact (mem_congr_left (rank_congr ec)).1 (rank_mem (func_mem (range fun p : Σ i, C i => e p.1 p.2) ⟨i, c⟩))

open Fml in
/-- Covers at the literal inputs of an admissible instance give `RankBounded`. -/
theorem rankBounded_of_covers {ψ : Fml} {e : Nat → PSet.{u}} {a : PSet.{u}} {C : a.Idx → Type u}
    {d : (i : a.Idx) → C i → PSet.{u}}
    (hcov : ∀ i, Covers (fun x y => HG y ∧ Sat HG ψ (Env.cons x (Env.cons y e))) (a.Func i) (d i)) :
    RankBounded ψ e a :=
  nn_intro ⟨coverBound a d, isOrd_coverBound a d, fun x y hx hy hs =>
    rank_mem_of_covers (fun ex ⟨hy, hs⟩ => ⟨hy, Sat.resp ψ (Env.cons_resp ex fun _ => Equiv.refl _) hs⟩)
      hcov x y hx ⟨hy, hs⟩⟩

/-- Existential composition of covers, by a dependent sum of candidate types. -/
theorem covers_comp {F G : PSet.{u} → PSet.{u} → Prop}
    (hG : ∀ {z z' y}, z ≈ z' → G z y → G z' y) {x : PSet.{u}}
    {CF : Type u} {eF : CF → PSet.{u}} (hF : Covers F x eF)
    {CG : PSet.{u} → Type u} {eG : (z : PSet.{u}) → CG z → PSet.{u}}
    (hGc : ∀ z, Covers G z (eG z)) :
    Covers (fun x y => ¬¬∃ z, F x z ∧ G z y) x
      (fun p : Σ c : CF, CG (eF c) => eG (eF p.1) p.2) := by
  intro y h
  refine Stable.of_nn h fun ⟨z, hxz, hzy⟩ => ?_
  refine Stable.of_nn (hF z hxz) fun ⟨c, ec⟩ => ?_
  exact nn_map (fun ⟨d, ed⟩ => ⟨⟨c, d⟩, ed⟩) (hGc (eF c) y (hG ec.symm hzy))

/-- Testing candidates by any predicate keeps the cover: the candidates of `F` cover
`F x y ∧ P x y`. -/
theorem covers_and {F : PSet.{u} → PSet.{u} → Prop} (P : PSet.{u} → PSet.{u} → Prop)
    {x : PSet.{u}} {C : Type u} {e : C → PSet.{u}} (hF : Covers F x e) :
    Covers (fun x y => F x y ∧ P x y) x e :=
  fun y h => hF y h.1

/-- Containment in a fixed set gives a cover: the literal elements of the set are the candidates,
and membership supplies the negative representative. -/
theorem covers_of_mem {F : PSet.{u} → PSet.{u} → Prop} {x K : PSet.{u}}
    (h : ∀ y, F x y → y ∈ K) : Covers F x K.Func :=
  fun y hy => nn_map (fun ⟨i, e⟩ => ⟨i, e.symm⟩) (h y hy)

/-- info: 'PSet.covers_of_mem' does not depend on any axioms -/
#guard_msgs in #print axioms covers_of_mem
/-- info: 'PSet.rankBounded_of_covers' does not depend on any axioms -/
#guard_msgs in #print axioms rankBounded_of_covers
/-- info: 'PSet.covers_comp' does not depend on any axioms -/
#guard_msgs in #print axioms covers_comp

end PSet
