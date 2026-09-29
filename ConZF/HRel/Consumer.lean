import ConZF.HRel.Core
import ConZF.HRel.Syntax

/-!
Graph validity of Axiom H and transitive containment, and the resulting consistency endpoints
(conzf30, first stage). Everything is interpreted through the existing consumer of
`GraphConsumer.lean`; graph validity of a formula is never presented as its derivability in a
smaller source theory.

* `hRel_gvalid`, `hOrdinary_gvalid`: the literal relational and ordinary Axiom H are graph-valid,
  both witnessed by `raw (e 0)`; the ordinary form forgets forward functionality.
* `tCo_gvalid`: transitive containment, witnessed by `span`.
* `TH := TDec + Hrel + TCo` and `THOrdinary := TDec + H + TCo`, by explicit axiom predicates, with
  `con_TH` and `con_THOrdinary`.
* `totalizedCollection_of_cover`: a constructed collector containing the default and every output
  validates the literal `coll (totalize ψ)`. It is a reusable lemma, not an assumed cover.

Not claimed: `Con ZF`, unrestricted Collection, KP or MOST, a native barrier, a graph rank
envelope, or any strict increase in consistency strength over the base theory.
-/
universe u
namespace GSet.HRel
open PSet.OrdDecode
open Consumer

/-- These are exact graph readings, not transferred native laws. -/
theorem trans_read (E : Nat → GSet.{u}) (i : Nat) :
    evalG (B.trans i) E ↔ Trans (E i) := Iff.rfl

theorem sub_read (E : Nat → GSet.{u}) (i j : Nat) :
    evalG (Syntax.sub i j) E ↔ Subset (E i) (E j) := Iff.rfl

/-- A forward reading is sufficient for Hrel validity and guarded Collection. -/
theorem rInj_of_eval (E : Nat → GSet.{u}) (r T U : Nat)
    (h : evalG (Syntax.rInj r T U) E) : RInj (E r) (E T) (E U) := by
  refine ⟨typed_readG E r T U h.1, total_readG E r T U h.2.1, ?_⟩
  intro t t' v ht ht' hv hp hp'
  let E' := Env.cons v (Env.cons t' (Env.cons t E))
  exact h.2.2 t ht t' ht' v hv
    ((edge_readG E' (r+3) 2 0).2 hp)
    ((edge_readG E' (r+3) 1 0).2 hp')

/-- Literal open axiom, universally valid in its parameter U. -/
theorem hRel_gvalid : GValid.{u} Syntax.hRelF := by
  intro e
  refine sat_ex.2 (nn_intro ⟨raw (e 0), trivial, sat_and.2 ⟨?_, ?_⟩⟩)
  · exact (evalG_read _ _).2 ((trans_read _ 0).2 (trans_raw (e 0)))
  · intro T _ r _ h
    have hh := sat_and.1 h
    have ht : Trans T := (trans_read _ 1).1 ((evalG_read _ _).1 hh.1)
    have hr : RInj r T (e 0) := rInj_of_eval _ 0 1 3 ((evalG_read _ _).1 hh.2)
    exact (evalG_read _ _).2 ((sub_read _ 1 2).2 (subset_raw_of_rInj ht hr))

/-- Ordinary H is graph-valid directly; do not postpone it for a Prf equivalence proof. -/
theorem hOrdinary_gvalid : GValid.{u} Syntax.hOrdinaryF := by
  intro e
  refine sat_ex.2 (nn_intro ⟨raw (e 0), trivial, sat_and.2 ⟨?_, ?_⟩⟩)
  · exact (evalG_read _ _).2 ((trans_read _ 0).2 (trans_raw (e 0)))
  · intro T _ r _ h
    have hh := sat_and.1 h
    have ht : Trans T := (trans_read _ 1).1 ((evalG_read _ _).1 hh.1)
    have ho := (evalG_read _ _).1 hh.2
    have hr : RInj r T (e 0) := rInj_of_eval _ 0 1 3 ho.1
    exact (evalG_read _ _).2 ((sub_read _ 1 2).2 (subset_raw_of_rInj ht hr))

theorem tCo_gvalid : GValid.{u} Syntax.tCoF := by
  intro e
  refine sat_ex.2 (nn_intro ⟨span (e 0), trivial, sat_and.2 ⟨?_, mem_span (e 0)⟩⟩)
  exact (evalG_read _ _).2 ((trans_read _ 0).2 (trans_span (e 0)))

/-- Preserve TDec by inclusion rather than copying its axiom list. -/
inductive TH : PSet.Fml → Prop
  | old {φ : PSet.Fml} : Consumer.TDec φ → TH φ
  | hrel : TH Syntax.hRelF
  | tco : TH Syntax.tCoF

theorem th_valid : ∀ φ, TH φ → GValid.{u} φ
  | _, .old h => Consumer.tdec_valid _ h
  | _, .hrel => hRel_gvalid
  | _, .tco => tCo_gvalid

theorem con_TH : PSet.Con TH := Consumer.Con.of_gvalid th_valid.{0}

/-- An ordinary-H endpoint without first formalizing the H-to-Hrel equivalence. -/
inductive THOrdinary : PSet.Fml → Prop
  | old {φ : PSet.Fml} : Consumer.TDec φ → THOrdinary φ
  | h : THOrdinary Syntax.hOrdinaryF
  | tco : THOrdinary Syntax.tCoF

theorem thOrdinary_valid : ∀ φ, THOrdinary φ → GValid.{u} φ
  | _, .old h => Consumer.tdec_valid _ h
  | _, .h => hOrdinary_gvalid
  | _, .tco => tCo_gvalid

theorem con_THOrdinary : PSet.Con THOrdinary :=
  Consumer.Con.of_gvalid thOrdinary_valid.{0}

/-! Generic elimination of duplicated totalization plumbing. -/

/-- Constructed all-output coverage plus the default gives the literal Collection instance.
This is a reusable lemma, not an axiom or an assumed cover for arbitrary formulas. -/
theorem totalizedCollection_of_cover (ψ : PSet.Fml) (collect : GSet.{u} → GSet.{u})
    (default_mem : ∀ a, Mem a (collect a))
    (covers : ∀ (e : Nat → GSet.{u}) d y, Mem d (e 0) →
      Sat (fun _ => True) ψ (Env.cons d (Env.cons y e)) → Mem y (collect (e 0))) :
    GValid.{u} (PSet.ZFAx.coll (PSet.ZFAx.totalize ψ)) := by
  intro e _
  refine sat_ex.2 (nn_intro ⟨collect (e 0), trivial, fun d _ hd => ?_⟩)
  refine sat_ex.2 fun hn => ?_
  have hall : ∀ y, ¬ Sat (fun _ => True) ψ (Env.cons d (Env.cons y e)) := by
    intro y hy
    exact hn ⟨y, trivial, sat_and.2 ⟨covers e d y hd hy,
      (sat_rename _ PSet.ZFAx.cB _).2
        (Sat.resp _ (Consumer.env_concl y d _ e) fun hnd => (hnd hy).elim)⟩⟩
  refine hn ⟨e 0, trivial, sat_and.2 ⟨default_mem (e 0),
    (sat_rename _ PSet.ZFAx.cB _).2
      (Sat.resp _ (Consumer.env_concl (e 0) d _ e) fun _ =>
        sat_and.2 ⟨Equiv.refl _, fun hex => ?_⟩)⟩⟩
  exact sat_ex.1 hex fun ⟨z, _, hz⟩ =>
    hall z (Sat.resp ψ (Consumer.env_inner d (e 0) z e)
      ((sat_rename ψ PSet.ZFAx.cB _).1 hz))

/-- info: 'GSet.HRel.hRel_gvalid' does not depend on any axioms -/
#guard_msgs in #print axioms hRel_gvalid
/-- info: 'GSet.HRel.hOrdinary_gvalid' does not depend on any axioms -/
#guard_msgs in #print axioms hOrdinary_gvalid
/-- info: 'GSet.HRel.tCo_gvalid' does not depend on any axioms -/
#guard_msgs in #print axioms tCo_gvalid
/-- info: 'GSet.HRel.con_TH' does not depend on any axioms -/
#guard_msgs in #print axioms con_TH
/-- info: 'GSet.HRel.con_THOrdinary' does not depend on any axioms -/
#guard_msgs in #print axioms con_THOrdinary
/-- info: 'GSet.HRel.totalizedCollection_of_cover' does not depend on any axioms -/
#guard_msgs in #print axioms totalizedCollection_of_cover

end GSet.HRel
