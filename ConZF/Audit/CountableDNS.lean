import ConZF.Audit.SWFPullback
/-!
Countable double-negation shift gives the native barrier at `ω` (reviewer probe, integrated;
nc7 closeout). Shift is an explicit premise throughout, never an axiom, and nothing here proves it.

* `DNSOn A` is double-negation shift over `A`-indexed families of propositions. Irrefutable excluded
  middle gives it for every `A` (`dns_of_not_not_em`), and `DNSOn Prop` is **exactly** irrefutable
  excluded middle (`dns_prop_iff_not_not_em`): asking for shift on every small carrier would
  reintroduce the old logical premise. The countable instance `DNSOn Nat` is the localized endpoint.
* Shift transfers to predicates on a `Prop` subtype (`subtype_shift`), and with it stable
  well-founded induction gives negative ordinary well-foundedness (`nn_wf_of_swf`).
* **The `ω` endpoint**, reusing `Audit/SWFPullback.lean`: an injection of the fixed native ordinal
  `bStar = wfBound (ULift Nat)` into `ω` yields a stable but not well-founded pullback, which
  `DNSOn Nat` refutes; so `DNSOn Nat` gives the **particular** native barrier `bStar`
  (`nativeBarrier_of_countable_dns`) and hence the graph-envelope benchmark at
  `relHartogs (embed ω)` (`graph_envelope_of_countable_dns`). Contrapositively, absence of a native
  barrier refutes countable shift (`not_dns_of_no_nativeBarrier`).

External semantic observation (nc7, reviewed at 7f53c80; not formalized): in the full covariant
presheaf model over the natural-number chain, a stable predicate on a constant carrier cannot
acquire truth on a directed future cone, so the pullback relation is constant and full predicate
quantification lets stable induction be tested on the external accessibility subset; hence that
model validates the barrier for the actual `bStar` while refuting both irrefutable excluded middle
and countable shift. A world/numeral counting argument extends the exclusion to countable branching
frames and to frames small relative to the native universe, under fullness and size hypotheses
using external choice. So failure of excluded middle or of countable shift is not evidence for a
countermodel to the barrier; the sufficient implication proved here is not claimed to be necessary,
and no strictness or equivalence between countable shift and the barrier is claimed.
-/
universe u

namespace DNSAudit

/-- Double-negation shift over `A`-indexed families. -/
def DNSOn (A : Type u) : Prop := ∀ P : A → Prop, (∀ a, ¬¬P a) → ¬¬∀ a, P a

theorem dns_of_not_not_em {A : Type u} (hem : ¬¬(∀ p : Prop, p ∨ ¬p)) : DNSOn A := by
  haveI : Stable (DNSOn A) := inferInstanceAs (Stable (∀ P : A → Prop, (∀ a, ¬¬P a) → ¬¬∀ a, P a))
  refine Stable.of_nn hem fun em P hn => nn_intro fun a => ?_
  exact (em (P a)).elim id (fun hp => False.elim (hn a hp))

/-- Shift over `Prop` is exactly irrefutable excluded middle. -/
theorem dns_prop_iff_not_not_em : DNSOn Prop ↔ ¬¬(∀ p : Prop, p ∨ ¬p) := by
  constructor
  · intro dns
    exact dns (fun p => p ∨ ¬p) fun p =>
      Stable.by_cases p (fun hp => nn_intro (Or.inl hp)) (fun hp => nn_intro (Or.inr hp))
  · exact dns_of_not_not_em

/-- Shift transfers to a `Prop` subtype; no witness is chosen. -/
theorem subtype_shift {A : Type u} (dns : DNSOn A) (S : A → Prop) (P : {a : A // S a} → Prop)
    (h : ∀ a, ¬¬P a) : ¬¬∀ a, P a := by
  have point : ∀ a, ¬¬∀ hs : S a, P ⟨a, hs⟩ := fun a =>
    Stable.by_cases (S a) (fun hs => nn_map (fun hp _ => hp) (h ⟨a, hs⟩))
      (fun hn => nn_intro (fun hs => False.elim (hn hs)))
  exact nn_map (fun all a => all a.1 a.2) (dns _ point)

/-- With shift, stable well-founded induction gives negative ordinary well-foundedness. -/
theorem nn_wf_of_swf {A : Type u} (dns : DNSOn A) {S : A → Prop}
    {R : {a : A // S a} → {a : A // S a} → Prop} (h : Graph.SWF R) : ¬¬WellFounded R := by
  have point : ∀ a, ¬¬Acc R a := by
    refine h (fun a => ¬¬Acc R a) (fun _ => inferInstance) ?_
    intro a ih
    apply nn_map (fun hp => Acc.intro a hp)
    apply subtype_shift dns S
    intro b
    exact Stable.by_cases (R b a) (fun hb => nn_map (fun ha _ => ha) (ih b hb))
      (fun hn => nn_intro (fun hb => False.elim (hn hb)))
  exact nn_map (fun all => ⟨all⟩) (subtype_shift dns S _ point)

theorem ulift_shift (dns : DNSOn Nat) : DNSOn (ULift.{u} Nat) := by
  intro P h
  exact nn_map (fun all n => all n.down) (dns (fun n => P ⟨n⟩) (fun n => h ⟨n⟩))

end DNSAudit

namespace PSet.CountableDNSAudit
open PSet.OrdDecode SWFPullbackAudit DNSAudit

/-- Countable shift refutes any injection of `bStar` into `ω`. -/
theorem not_emb_bStar_of_dns (dns : DNSOn Nat) : ¬ Emb bStar.{u} omega := fun h =>
  emb_bStar_swf_not_wf h fun ⟨_, _, hswf, hnwf⟩ => nn_wf_of_swf (ulift_shift dns) hswf hnwf

/-- **The particular barrier**: under countable shift, `bStar = wfBound (ULift Nat)` is a native
barrier at `ω`. -/
theorem barrier_bStar_of_dns (dns : DNSOn Nat) : Barrier (fun _ => True) omega bStar.{u} :=
  ⟨bStar_ord, fun f _ hf => not_emb_bStar_of_dns dns (nn_intro ⟨f, hf⟩)⟩

theorem nativeBarrier_of_countable_dns (dns : DNSOn Nat) : GSet.Bridge.NativeBarrier.{u} :=
  nn_intro ⟨bStar, barrier_bStar_of_dns dns⟩

/-- The graph-envelope benchmark at `relHartogs (embed ω)`, conditional on countable shift. -/
theorem graph_envelope_of_countable_dns (dns : DNSOn Nat) :
    ¬¬∃ E : GSet.{u}, GSet.Envelope.RankCover GSet.Bridge.κ E :=
  GSet.Bridge.rankCover_of_nativeBarrier (nativeBarrier_of_countable_dns dns)

/-- Absence of a native barrier refutes countable shift. -/
theorem not_dns_of_no_nativeBarrier (h : ¬ GSet.Bridge.NativeBarrier.{u}) : ¬ DNSOn Nat :=
  fun dns => h (nativeBarrier_of_countable_dns dns)

/-- info: 'DNSAudit.dns_prop_iff_not_not_em' does not depend on any axioms -/
#guard_msgs in #print axioms DNSAudit.dns_prop_iff_not_not_em
/-- info: 'DNSAudit.nn_wf_of_swf' does not depend on any axioms -/
#guard_msgs in #print axioms DNSAudit.nn_wf_of_swf
/-- info: 'PSet.CountableDNSAudit.barrier_bStar_of_dns' does not depend on any axioms -/
#guard_msgs in #print axioms barrier_bStar_of_dns
/-- info: 'PSet.CountableDNSAudit.graph_envelope_of_countable_dns' does not depend on any axioms -/
#guard_msgs in #print axioms graph_envelope_of_countable_dns
/-- info: 'PSet.CountableDNSAudit.not_dns_of_no_nativeBarrier' does not depend on any axioms -/
#guard_msgs in #print axioms not_dns_of_no_nativeBarrier

end PSet.CountableDNSAudit
