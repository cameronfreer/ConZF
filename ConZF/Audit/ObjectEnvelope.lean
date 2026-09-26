import ConZF.NegCore
import ConZF.Ord

/-!
Reviewer audit of conzf29 (checked against a77b0fa, incorporated verbatim).

At any fixed environment, all existing object descriptors of `NegCore` have a native set of values
and a native common union bound, the envelope. Because `Obj` is closed under singleton formation
(`upair q q`), this union also **contains** every descriptor value, so it has no descriptor in the
same `Obj` grammar at that environment, and no descriptor even bounds all descriptor values by
inclusion.

This separates native construction of a common bound (available: `Witness.Certified`) from
reifying that bound back into the current descriptor grammar (not available without more syntax
and its preservation theorems). It is a fixed-grammar, fixed-environment result: it permits a
larger descriptor grammar or an added environment parameter, and is not an obstruction to every
candidate forcing model.
-/
universe u
namespace PSet.ObjectEnvelopeAudit
open NegCore

/-- The native set of values of all descriptors at `e`. -/
def values (e : Env.{u}) : PSet.{u} :=
  range fun q : ULift.{u} Obj => Obj.eval q.down e

/-- Their union. -/
def envelope (e : Env.{u}) : PSet.{u} := sUnion (values e)

theorem eval_subset_envelope (e : Env.{u}) (q : Obj) (x : PSet.{u})
    (hx : x ∈ Obj.eval q e) : x ∈ envelope e :=
  mem_sUnion.2 (nn_intro ⟨Obj.eval q e, func_mem (values e) ⟨q⟩, hx⟩)

theorem eval_mem_envelope (e : Env.{u}) (q : Obj) : Obj.eval q e ∈ envelope e :=
  eval_subset_envelope e (.upair q q) _ (mem_upair_left _ _)

theorem envelope_not_representable (e : Env.{u}) (q : Obj) :
    ¬ Obj.eval q e ≈ envelope e := by
  intro h
  exact not_mem_self (envelope e) ((mem_congr_left h).1 (eval_mem_envelope e q))

/-- No current descriptor even contains all the current descriptor values as subsets. -/
theorem no_descriptor_common_bound (e : Env.{u}) (q : Obj)
    (h : ∀ r : Obj, ∀ x : PSet.{u}, x ∈ Obj.eval r e → x ∈ Obj.eval q e) : False :=
  not_mem_self (Obj.eval q e) (h (.upair q q) _ (mem_upair_left _ _))

/-- info: 'PSet.ObjectEnvelopeAudit.eval_subset_envelope' does not depend on any axioms -/
#guard_msgs in #print axioms eval_subset_envelope
/-- info: 'PSet.ObjectEnvelopeAudit.eval_mem_envelope' does not depend on any axioms -/
#guard_msgs in #print axioms eval_mem_envelope
/-- info: 'PSet.ObjectEnvelopeAudit.envelope_not_representable' does not depend on any axioms -/
#guard_msgs in #print axioms envelope_not_representable
/-- info: 'PSet.ObjectEnvelopeAudit.no_descriptor_common_bound' does not depend on any axioms -/
#guard_msgs in #print axioms no_descriptor_common_bound

end PSet.ObjectEnvelopeAudit
