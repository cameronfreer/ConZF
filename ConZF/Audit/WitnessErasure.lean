-- Reviewer audit probe (2026-09-26), incorporated verbatim from the small-machine audit after conzf25;
-- its scope is stated in its own docstring. Empty axiom reports.
import ConZF.Witness
import ConZF.Ord

/-!
Witness-preserving deletion of an arbitrary object from a runtime context cannot
compress all the resulting closures into one small family at a fixed base context.
The conclusion holds even when code/trace transport is only double-negatively
existential. It does not preclude weakening, renaming, or deleting a variable while
allowing the selected witness to change.
-/
universe u
namespace PSet.WitnessErasureAudit

theorem no_small_cover (I : Type u) (out : I → PSet.{u})
    (covers : ∀ x : PSet.{u}, ¬¬∃ i, x ≈ out i) : False :=
  not_mem_self (range out) (covers (range out))

theorem no_small_menu_cover (Code : Type u)
    (menus : Code → Witness.Menu.{u,u+1} PSet.{u})
    (covers : ∀ x : PSet.{u}, ¬¬∃ c, ∃ i : (menus c).I, x ≈ (menus c).val i) : False := by
  apply no_small_cover (Σ c, (menus c).I) (fun t => (menus t.1).val t.2)
  intro x
  exact nn_map (fun ⟨c, i, hi⟩ => ⟨⟨c, i⟩, hi⟩) (covers x)

/-- A proposed witness-preserving erasure for arbitrary added objects already gives a cover. -/
theorem no_witness_preserving_erasure (Code : Type u)
    (base : Code → Witness.Menu.{u,u+1} PSet.{u})
    (extended : PSet.{u} → Code → Witness.Menu.{u,u+1} PSet.{u})
    (introCode : Code)
    (introduced : ∀ x, ∃ i : (extended x introCode).I,
      (extended x introCode).val i ≈ x)
    (erase : ∀ x c (i : (extended x c).I),
      ¬¬∃ d, ∃ j : (base d).I,
        (extended x c).val i ≈ (base d).val j) : False := by
  apply no_small_menu_cover Code base
  intro x
  obtain ⟨i, hi⟩ := introduced x
  exact nn_map (fun ⟨d, j, hj⟩ => ⟨d, j, hi.symm.trans hj⟩) (erase x introCode i)

#print axioms no_small_cover
#print axioms no_small_menu_cover
#print axioms no_witness_preserving_erasure

end PSet.WitnessErasureAudit
