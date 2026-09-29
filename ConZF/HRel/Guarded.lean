import ConZF.HRel.Consumer
import ConZF.HRel.Support

/-!
Support-guarded Collection (conzf30, second stage).

The guarded matrix is `supportF ∧ θ` at `[x, y, params…]`, so its guard reads **"the output `y` has
weak transitive support bounded by the input `x`"**. For every source formula `θ`, the literal
`coll (totalize (guarded θ))` is graph-valid (`gvalid_guardedCollection`): for a source `a`, every
input `x ∈ a` is included in `⋃a`, support is monotone, and a supported set is a subset of the raw
envelope, so the box `powerset (raw (⋃a)) ∪ {a}` collects every guarded output and the default. The
test `θ` may be arbitrary because the guard alone supplies the bound. This is **not** unrestricted
Collection, and the exact support set is not needed.

`THSupport` extends `TH` by these instances through an explicit axiom predicate; `con_THSupport`
and the corresponding Replacement instances (`prf_guardedReplacement`) follow. Graph validity of the
schema is not a derivation of it in `TH`.
-/
universe u
namespace GSet.HRel
open PSet.OrdDecode
open Consumer

/-- Forward support reading; the reverse direction is not needed for this endpoint. -/
theorem support_of_sat (U y : GSet.{u}) (e : Nat → GSet.{u})
    (h : Sat (fun _ => True) Syntax.supportF (Env.cons U (Env.cons y e))) :
    Support U y := by
  refine nn_bind (sat_ex.1 h) fun ⟨T, _, hT⟩ => ?_
  refine nn_map (fun ⟨r, _, hr⟩ => ?_) (sat_ex.1 hT)
  have hb := (evalG_read _ _).1 hr
  exact ⟨T, r, (trans_read _ 1).1 hb.1,
    (sub_read _ 3 1).1 hb.2.1, rInj_of_eval _ 0 1 2 hb.2.2⟩

/-- First-use output box: powerset(raw U), without constructing the exact support cut. -/
def boxedCollector (U a : GSet.{u}) : GSet.{u} :=
  union (powerset (raw U)) (single a)

theorem default_mem_boxedCollector (U a : GSet.{u}) : Mem a (boxedCollector U a) :=
  (mem_union _ _).2 (nn_intro (.inr ((mem_single _).2 (Equiv.refl _))))

theorem gvalid_guardedCollection (θ : PSet.Fml) : GValid.{u} (Syntax.guardedCollection θ) := by
  apply totalizedCollection_of_cover (Syntax.guarded θ)
    (fun a => boxedCollector (sUnion a) a)
    (fun a => default_mem_boxedCollector _ a)
  intro e d y hd hy
  have hs : Support d y := support_of_sat d y e (sat_and.1 hy).1
  have sub : Subset d (sUnion (e 0)) := fun z hz =>
    (mem_sUnion _).2 (nn_intro ⟨d, hd, hz⟩)
  have hb := support_subset_raw (support_mono sub hs)
  exact (mem_union _ _).2 (nn_intro (.inl ((mem_powerset _).2 hb)))

/-- Explicit extension: graph validity alone is not a Prf TH derivation of a schema. -/
inductive THSupport : PSet.Fml → Prop
  | base {φ : PSet.Fml} : TH φ → THSupport φ
  | guarded (θ : PSet.Fml) : THSupport (Syntax.guardedCollection θ)

theorem thSupport_valid : ∀ φ, THSupport φ → GValid.{u} φ
  | _, .base h => th_valid _ h
  | _, .guarded θ => gvalid_guardedCollection θ

theorem con_THSupport : PSet.Con THSupport :=
  Consumer.Con.of_gvalid thSupport_valid.{0}

theorem prf_guardedReplacement (θ : PSet.Fml) :
    PSet.Prf THSupport (Syntax.guardedReplacement θ) :=
  PSet.ZFAx.repl_of_collection_of (Syntax.guarded θ) (PSet.Prf.ax (.guarded θ))

/-- info: 'GSet.HRel.gvalid_guardedCollection' does not depend on any axioms -/
#guard_msgs in #print axioms gvalid_guardedCollection
/-- info: 'GSet.HRel.con_THSupport' does not depend on any axioms -/
#guard_msgs in #print axioms con_THSupport
/-- info: 'GSet.HRel.prf_guardedReplacement' does not depend on any axioms -/
#guard_msgs in #print axioms prf_guardedReplacement

end GSet.HRel
