import ConZF.Graph.Rank
/-!
Faithful collapse. Let `R` be a stable relation on a small type `T` with stable well-founded
induction, and `E` a stable equivalence relation on `T` such that `R` is a congruence for `E` and
`R` is relationally extensional: equal predecessor profiles give `E`. Then the graph collapse is
faithful: for the graph on `T` with edges `R`, pointing at `t` and at `u` gives equivalent graphs
exactly when `E t u` (`faithful_equiv`), and a member exactly when `R t u` (`faithful_mem`). The
reverse directions hold because `E` is itself a bisimulation; the forward direction is stable
induction on `t`, quantified over `u`, using both matching directions at predecessors of `t`.

Stability of `R` is an explicit hypothesis: the bisimulation gives a match negatively and the
transport back to an actual edge needs it. Faithfulness preserves the represented structure; it
does not identify a collapsed value with any ambient value.
-/
universe u

namespace GSet

/-- The data of a faithful collapse. -/
structure Collapse (T : Type u) where
  R : T → T → Prop
  E : T → T → Prop
  swf : Graph.SWF R
  stableR : ∀ t u, Stable (R t u)
  stableE : ∀ t u, Stable (E t u)
  refl : ∀ t, E t t
  symm : ∀ {t u}, E t u → E u t
  trans : ∀ {t u v}, E t u → E u v → E t v
  congr_left : ∀ {t t' u}, E t t' → R t u → R t' u
  congr_right : ∀ {t u u'}, E u u' → R t u → R t u'
  ext : ∀ t u, (∀ v, R v t ↔ R v u) → E t u

namespace Collapse
variable {T : Type u} (c : Collapse T)

/-- The graph on `T`, pointed at `t`. -/
def q (t : T) : GSet.{u} := ⟨T, c.R, t, c.swf⟩

/-- `E` is a bisimulation of the graph with itself. -/
theorem isBisim_E : IsBisim (c.q t) (c.q u) c.E :=
  ⟨c.stableE,
   fun _ _ hab a' ha' => nn_intro ⟨a', c.congr_right hab ha', c.refl a'⟩,
   fun _ _ hab b' hb' => nn_intro ⟨b', c.congr_right (c.symm hab) hb', c.refl b'⟩⟩

theorem equiv_of_E {t u : T} (h : c.E t u) : Equiv (c.q t) (c.q u) :=
  nn_intro ⟨c.E, c.isBisim_E, h⟩

/-- **Faithful collapse.** Equivalent pointed graphs have `E`-related points. -/
theorem E_of_equiv : ∀ t u : T, Equiv (c.q t) (c.q u) → c.E t u := by
  have hs : ∀ t, Stable (∀ u, Equiv (c.q t) (c.q u) → c.E t u) := fun t =>
    have : ∀ u, Stable (c.E t u) := c.stableE t
    inferInstance
  refine c.swf (fun t => ∀ u, Equiv (c.q t) (c.q u) → c.E t u) hs fun t ih u he => ?_
  have : Stable (c.E t u) := c.stableE t u
  refine Stable.of_nn he fun ⟨Z, hZ, htu⟩ => ?_
  refine c.ext t u fun v => ⟨fun hv => ?_, fun hv => ?_⟩
  · have : Stable (c.R v u) := c.stableR v u
    refine Stable.of_nn (hZ.forth t u htu v hv) fun ⟨v', hv', hz⟩ => ?_
    exact c.congr_left (c.symm (ih v hv v' (hZ.at' hz))) hv'
  · have : Stable (c.R v t) := c.stableR v t
    refine Stable.of_nn (hZ.back t u htu v hv) fun ⟨v', hv', hz⟩ => ?_
    exact c.congr_left (ih v' hv' v (hZ.at' hz)) hv'

theorem faithful_equiv {t u : T} : Equiv (c.q t) (c.q u) ↔ c.E t u :=
  ⟨c.E_of_equiv t u, c.equiv_of_E⟩

/-- **Membership reflection.** -/
theorem faithful_mem {t u : T} : Mem (c.q t) (c.q u) ↔ c.R t u := by
  have : Stable (c.R t u) := c.stableR t u
  constructor
  · intro h
    exact Stable.of_nn h fun ⟨v, hv, e⟩ => c.congr_left (c.symm (c.E_of_equiv t v e)) hv
  · intro h
    exact nn_intro ⟨t, h, Equiv.refl _⟩

end Collapse

/-- info: 'GSet.Collapse.faithful_equiv' does not depend on any axioms -/
#guard_msgs in #print axioms Collapse.faithful_equiv
/-- info: 'GSet.Collapse.faithful_mem' does not depend on any axioms -/
#guard_msgs in #print axioms Collapse.faithful_mem

end GSet
