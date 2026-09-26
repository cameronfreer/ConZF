import ConZF.DecodeSpectrum

/-!
The reviewer's calibration of nc2's atomic-bottom clause (checked against 1e1b6f6), incorporated
verbatim. No forcing relation is assumed or implemented here.

For any small total readback family `read : C → PSet`, with the trace `Tr_U(b) := ∀ κ ∈ b, Ord κ →
Emb κ U` and `refutes read U := ¬¬∃ c, Tr_U (read c) → False` (exactly nc2's bottom clause at the
singleton no-barrier condition): refutation is negative existence of a described bound containing
an ordinal with no injection into `U` (`refutes_iff_barrier_in_readback`); refutation makes the
preconstructed ordinal `rank (range read)` an actual native barrier (`barrier_of_refutes`); and any
injectable ordinal stage containing every readback blocks refutation, independently of the syntax
(`not_refutes_of_stage`). So this route must establish native barrier strength whatever the grammar.
Also the generic negative-certificate equivalence `negative_certificate_iff`, used by `ObjMajorant`.
-/
universe u v
namespace PSet.CertificateAudit
open OrdDecode

theorem negative_certificate_iff {C : Sort v} (ne : Nonempty C)
    (R : C → Prop) [∀ c, Stable (R c)] (Q : Prop) [Stable Q] :
    (¬¬∃ c, R c → Q) ↔ ((∀ c, R c) → Q) := by
  constructor
  · exact fun h ha => Stable.of_nn h fun ⟨c, hc⟩ => hc (ha c)
  · intro h hn
    have ha : ∀ c, R c := fun c => Stable.dne fun hnc => hn ⟨c, fun hc => (hnc hc).elim⟩
    have hq := h ha
    rcases ne with ⟨c⟩
    exact hn ⟨c, fun _ => hq⟩

/-- The native reading of the trace of H_U on b. -/
def trace (U b : PSet.{u}) : Prop := ∀ κ, κ ∈ b → IsOrd κ → Emb κ U

instance {U b : PSet.{u}} : Stable (trace U b) :=
  inferInstanceAs (Stable (∀ κ, κ ∈ b → IsOrd κ → Emb κ U))

/-- Exactly the atomic-bottom clause of nc2 at the singleton condition H_U. -/
def refutes {C : Type u} (read : C → PSet.{u}) (U : PSet.{u}) : Prop :=
  ¬¬∃ c, trace U (read c) → False

/-- Refutation is precisely negative existence of a described bound containing a native barrier.
No bounded truth theorem or source-adequacy premise occurs in this calculation. -/
theorem refutes_iff_barrier_in_readback {C : Type u} (read : C → PSet.{u}) (U : PSet.{u}) :
    refutes read U ↔ ¬¬∃ c κ, κ ∈ read c ∧ IsOrd κ ∧ ¬ Emb κ U := by
  constructor
  · intro h
    refine nn_bind h fun ⟨c, hc⟩ => ?_
    intro hn
    apply hc
    intro κ hk ho
    exact Stable.dne fun he => hn ⟨c, κ, hk, ho, he⟩
  · exact nn_map fun ⟨c, κ, hk, ho, he⟩ => ⟨c, fun ht => he (ht κ hk ho)⟩

/-- This ordinal is an unconditional native term for every small readback family. -/
def readbackHeight {C : Type u} (read : C → PSet.{u}) : PSet.{u} := rank (range read)

/-- A successful refutation makes this PARTICULAR preconstructed ordinal a native barrier.
The conclusion is actual; only the input certificate was negatively existential. -/
theorem barrier_of_refutes {C : Type u} (read : C → PSet.{u}) (U : PSet.{u})
    (h : refutes read U) : Barrier (fun _ => True) U (readbackHeight read) := by
  refine ⟨isOrd_rank _, fun f _ hf => ?_⟩
  have hE : Emb (readbackHeight read) U := nn_intro ⟨f, hf⟩
  refine h fun ⟨c, hc⟩ => hc fun κ hk ho => ?_
  apply hE.down (isOrd_rank _)
  have h1 := rank_mem hk
  have h2 := rank_mem (func_mem (range read) c)
  exact (mem_congr_left ho.rank_equiv).1 ((isOrd_rank (range read)).trans _ h2 _ h1)

/-- In particular, injectivity of the readback height obstructs this atomic refutation. -/
theorem not_refutes_of_height_embeds {C : Type u} (read : C → PSet.{u}) (U : PSet.{u})
    (h : Emb (readbackHeight read) U) : ¬ refutes read U := by
  intro hr
  have hb := barrier_of_refutes read U hr
  exact h fun ⟨f, hf⟩ => hb.2 f trivial hf

/-- Any injectable rank stage containing every readback blocks this refutation, independently
of the syntax or the number of object constructors. Successor closure is needed only when
establishing the stage-containment hypothesis for a particular grammar. -/
theorem not_refutes_of_stage {C : Type u} (read : C → PSet.{u}) (U η : PSet.{u})
    (hη : IsOrd η) (hE : Emb η U) (he : ∀ c, read c ∈ Vl η) : ¬ refutes read U := by
  intro h
  refine h fun ⟨c, hc⟩ => hc fun κ hk ho => ?_
  apply hE.down hη
  exact (mem_congr_left ho.rank_equiv).1
    (hη.trans _ ((mem_Vl_ord hη).1 (he c)) _ (rank_mem hk))

/-- info: 'PSet.CertificateAudit.negative_certificate_iff' does not depend on any axioms -/
#guard_msgs in #print axioms negative_certificate_iff
/-- info: 'PSet.CertificateAudit.refutes_iff_barrier_in_readback' does not depend on any axioms -/
#guard_msgs in #print axioms refutes_iff_barrier_in_readback
/-- info: 'PSet.CertificateAudit.barrier_of_refutes' does not depend on any axioms -/
#guard_msgs in #print axioms barrier_of_refutes
/-- info: 'PSet.CertificateAudit.not_refutes_of_height_embeds' does not depend on any axioms -/
#guard_msgs in #print axioms not_refutes_of_height_embeds
/-- info: 'PSet.CertificateAudit.not_refutes_of_stage' does not depend on any axioms -/
#guard_msgs in #print axioms not_refutes_of_stage

end PSet.CertificateAudit
