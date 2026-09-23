import ConZF.Graph.Levels
/-!
Finite-name transport. Along a bisimulation `Z` between two presentations, two names *correspond*
(`NameEquiv Z`) when their births are `Z`-related, their formulas and arities are literally equal,
and their arguments correspond pointwise; argument functions are never compared for equality.
Every valid name transports, negatively, to a corresponding valid name born at any `Z`-match of
its birth (`transport`): each argument's birth is matched beneath the already matched parent
stage by `IsBisim.path`, and finitely many negative matches are combined (`nn_fin_choice`).
Corresponding valid names denote equivalent sets (`nameVal_equiv_of_nameEquiv`), by induction on
the name using `nameVal_spec` and presentation invariance of the levels. Formula, arity, and
label equivalence are preserved by construction, which is what the later shortlex comparison
of codes will be defined from.
-/
universe u

namespace GSet
open PSet.Fml

/-- Finitely many negative choices combine into a negative choice of a finite family. -/
theorem nn_fin_choice {β : Sort _} : ∀ (n : Nat) (P : Fin n → β → Prop),
    (∀ i, ¬¬∃ x, P i x) → ¬¬∃ f : Fin n → β, ∀ i, P i (f i)
  | 0, _, _ => nn_intro ⟨(fun i => nomatch i), (fun i => nomatch i)⟩
  | n+1, P, h => by
    refine nn_bind (nn_fin_choice n (fun i => P ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
      fun i => h _) fun ⟨f, hf⟩ => ?_
    refine nn_map (fun ⟨x, hx⟩ => ⟨fun i => ?_, fun i => ?_⟩) (h ⟨0, Nat.zero_lt_succ n⟩)
    · exact match i with
        | ⟨0, _⟩ => x
        | ⟨i+1, hi⟩ => f ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    · exact match i with
        | ⟨0, _⟩ => hx
        | ⟨i+1, hi⟩ => hf ⟨i, Nat.lt_of_succ_lt_succ hi⟩

section
variable {α α' : GSet.{u}} (Z : α.A → α'.A → Prop)

/-- Corresponding names: related births, equal formulas and arities, corresponding arguments. -/
def NameEquiv : Name α.A → Name α'.A → Prop
  | .def' a φ n args, .def' a' φ' n' args' =>
    Z a a' ∧ φ = φ' ∧ ∃ e : n = n', ∀ i : Fin n, NameEquiv (args i) (args' ⟨i.1, e ▸ i.2⟩)

theorem NameEquiv.birth {t : Name α.A} {t' : Name α'.A} (h : NameEquiv Z t t') : Z t.birth t'.birth := by
  cases t; cases t'; exact h.1

theorem NameEquiv.fml {t : Name α.A} {t' : Name α'.A} (h : NameEquiv Z t t') : t.fml = t'.fml := by
  cases t; cases t'; exact h.2.1

theorem NameEquiv.arity {t : Name α.A} {t' : Name α'.A} (h : NameEquiv Z t t') : t.arity = t'.arity := by
  cases t; cases t'; exact h.2.2.1

variable (hZ : IsBisim α α' Z)
include hZ

/-- **Transport.** A valid name transports to a corresponding valid name born at any match of its
birth. -/
theorem transport : ∀ (t : Name α.A), Valid α t → ∀ a', Z t.birth a' →
    ¬¬∃ t' : Name α'.A, NameEquiv Z t t' ∧ Valid α' t' ∧ t'.birth = a'
  | .def' a φ n args, hv, a', haa' => by
    have step : ∀ i : Fin n, ¬¬∃ t' : Name α'.A,
        NameEquiv Z (args i) t' ∧ Valid α' t' ∧ Stage α' t'.birth a' := fun i => by
      refine Stable.of_nn (hv.2 i).2 fun p => ?_
      refine nn_bind (hZ.path p a' haa') fun ⟨b', hp, hb⟩ => ?_
      exact nn_map (fun ⟨t', h1, h2, h3⟩ => ⟨t', h1, h2, h3 ▸ nn_intro hp⟩)
        (transport (args i) (hv.2 i).1 b' hb)
    refine nn_map (fun ⟨f, hf⟩ => ⟨.def' a' φ n f, ⟨haa', rfl, rfl, fun i => (hf i).1⟩,
      ⟨hv.1, fun i => ⟨(hf i).2.1, (hf i).2.2⟩⟩, rfl⟩) (nn_fin_choice n _ step)

/-- Corresponding valid names denote equivalent sets. -/
theorem nameVal_equiv_of_nameEquiv : ∀ (t : Name α.A) (t' : Name α'.A), Valid α t → Valid α' t' →
    NameEquiv Z t t' → Equiv (nameVal α t) (nameVal α' t')
  | .def' a φ n args, .def' a' φ' n' args', hv, hv', ⟨haa', hφ, e, hargs⟩ => by
    subst hφ; subst e
    have hL : Equiv (L α a) (L α' a') := L_congr_of_bisim hZ a a' haa'
    refine ext fun K => (nameVal_spec α hv K).trans (Iff.trans ?_ (nameVal_spec α' hv' K).symm)
    refine and_congr (mem_congr_right hL) ?_
    refine Sat.resp_iff (fun _ => mem_congr_right hL) φ fun i => ?_
    cases i with
    | zero => exact Equiv.refl _
    | succ i =>
      show Equiv (if h : i < n then nameVal α (args ⟨i, h⟩) else L α a)
        (if h : i < n then nameVal α' (args' ⟨i, h⟩) else L α' a')
      split
      · rename_i h
        exact nameVal_equiv_of_nameEquiv (args ⟨i, h⟩) (args' ⟨i, h⟩) (hv.2 _).1 (hv'.2 _).1
          (hargs ⟨i, h⟩)
      · exact hL

end

/-- info: 'GSet.transport' does not depend on any axioms -/
#guard_msgs in #print axioms transport
/-- info: 'GSet.nameVal_equiv_of_nameEquiv' does not depend on any axioms -/
#guard_msgs in #print axioms nameVal_equiv_of_nameEquiv

end GSet
