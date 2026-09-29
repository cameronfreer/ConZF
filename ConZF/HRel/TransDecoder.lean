import ConZF.HRel.Guarded

/-!
The transitive decoder and the combined endpoint (conzf30, third stage).

`transDecodeF` differs from the ordinal decoder only in replacing ordinalhood by transitivity;
purity, totality, functionality, onto and order clauses are all kept in the source formula, and only
their needed forward consequences are projected (`transBody_read`). For a transitive source,
inverse uniqueness of the isomorphism graph follows from Extensionality and order reflection
(`inverseUnique_of_order`), with no trichotomy. A decoding of a diagram in `a` is therefore a
transitive set with an injection relation into `⋃⋃⋃a` (`transDecoded_injRel`), hence a subset of the
raw envelope of that triple union, and the literal `coll (totalize transDecodeF)` is graph-valid
(`gvalid_transDecoded_collection`).

`THFull` is the combined theory, by an explicit axiom predicate: `TDec`, transitive containment,
both forms of Axiom H, every support-guarded Collection instance, and the transitive-decoder
Collection instance. `con_THFull` is the combined consistency endpoint, and `THFull` proves the
Replacement instance for the transitive decoder (`prf_transDecoded_replacement`).

Stopping point: no rank calibration, no generalized guards, no source-calculus proof that the two
forms of Axiom H are equivalent, and no claim of unrestricted Collection, KP or MOST, `Con ZF`, a
native barrier, or a graph rank envelope.
-/
universe u
namespace GSet.HRel
open PSet.OrdDecode
open Consumer

/-- Forward reading at [f,d,T,...]. -/
theorem transBody_read (E : Nat → GSet.{u}) (h : evalG Syntax.transBody E) :
    ¬¬∃ A r, Equiv (E 1) (opair A r) ∧ Trans (E 2) ∧
      TypedG (E 0) (E 2) A ∧ TotalG (E 0) (E 2) A ∧ OrderG (E 0) r (E 2) A := by
  refine nn_bind h fun ⟨S, _, hA⟩ => nn_bind hA fun ⟨A, _, hQ⟩ =>
    nn_bind hQ fun ⟨Q, _, hr⟩ => nn_map (fun ⟨r, _, hh⟩ => ?_) hr
  let E' := Env.cons r (Env.cons Q (Env.cons A (Env.cons S E)))
  exact ⟨A, r, (pair_readG E' 5 2 0).1 hh.1,
    (trans_read E' 6).1 hh.2.1,
    typed_readG E' 4 6 2 hh.2.2.1.1,
    total_readG E' 4 6 2 hh.2.2.1.2.1,
    order_readG E' 4 0 6 2 hh.2.2.2.2.2⟩

/-- Inverse uniqueness for a transitive source follows from extensionality. -/
theorem inverseUnique_of_order {f r T A : GSet.{u}}
    (hT : Trans T) (ht : TypedG f T A) (hto : TotalG f T A) (ho : OrderG f r T A)
    {i j v : GSet.{u}} (hi : Mem i T) (hj : Mem j T)
    (hp : Mem (opair i v) f) (hq : Mem (opair j v) f) : Equiv i j := by
  have hv : Mem v A := (edge_typed ht hp).2
  refine ext fun z => ⟨?_, ?_⟩
  · intro hzi
    have hzT := hT i hi z hzi
    refine Stable.of_nn (hto z hzT) fun ⟨w, hw, hzw⟩ => ?_
    exact (ho z j w v hzT hj hw hv hzw hq).1
      ((ho z i w v hzT hi hw hv hzw hp).2 hzi)
  · intro hzj
    have hzT := hT j hj z hzj
    refine Stable.of_nn (hto z hzT) fun ⟨w, hw, hzw⟩ => ?_
    exact (ho z i w v hzT hi hw hv hzw hp).1
      ((ho z j w v hzT hj hw hv hzw hq).2 hzj)

def TransDecoded (d T : GSet.{u}) (e : Nat → GSet.{u}) : Prop :=
  Sat (fun _ => True) Syntax.transDecodeF (Env.cons d (Env.cons T e))

/-- The same actual diagram source; the codomain box is the existing triple union. -/
theorem transDecoded_injRel {a d T : GSet.{u}} {e : Nat → GSet.{u}}
    (hd : Mem d a) (h : TransDecoded d T e) : Trans T ∧ InjRel T (base3 a) := by
  refine Stable.of_nn (sat_ex.1 h) fun ⟨f, _, hb⟩ => ?_
  refine Stable.of_nn (transBody_read _ ((evalG_read _ _).1 hb))
    fun ⟨A, r, ed, hT, ht, hto, ho⟩ => ?_
  refine ⟨hT, nn_intro ⟨fun ξ i => Mem (opair ξ ((base3 a).at' i)) f, ?_⟩⟩
  refine ⟨fun _ _ => inferInstance, ?_, ?_, ?_, ?_⟩
  · intro ξ ξ' i e' hf
    exact Mem.congr_left (opair_congr _ _ e' (Equiv.refl _)) hf
  · intro ξ i j e' hf
    exact Mem.congr_left (opair_congr _ _ (Equiv.refl _) e') hf
  · intro ξ hξ
    refine nn_bind (hto ξ hξ) fun ⟨v, hv, hf⟩ => ?_
    exact nn_map (fun ⟨i, hi, ei⟩ =>
      ⟨i, hi, Mem.congr_left (opair_congr _ _ (Equiv.refl _) ei) hf⟩)
      (mem_base3 hd ed hv)
  · intro ξ ξ' i hξ hξ' h1 h2
    exact inverseUnique_of_order hT ht hto ho hξ hξ' h1 h2

theorem transDecoded_mem_box {a d T : GSet.{u}} {e : Nat → GSet.{u}}
    (hd : Mem d a) (h : TransDecoded d T e) : Mem T (powerset (raw (base3 a))) := by
  have hT := transDecoded_injRel hd h
  exact (mem_powerset _).2 (subset_raw hT.1 hT.2)

theorem gvalid_transDecoded_collection :
    GValid.{u} (PSet.ZFAx.coll (PSet.ZFAx.totalize Syntax.transDecodeF)) := by
  apply totalizedCollection_of_cover Syntax.transDecodeF
    (fun a => boxedCollector (base3 a) a)
    (fun a => default_mem_boxedCollector _ a)
  intro e d T hd h
  exact (mem_union _ _).2 (nn_intro (.inl (transDecoded_mem_box hd h)))

/-- The combined theory. Added source formulas are explicit axioms; no derivability in a smaller
theory is claimed. -/
inductive THFull : PSet.Fml → Prop
  | base {φ : PSet.Fml} : THSupport φ → THFull φ
  | hOrdinary : THFull Syntax.hOrdinaryF
  | transColl : THFull (PSet.ZFAx.coll (PSet.ZFAx.totalize Syntax.transDecodeF))

theorem thFull_valid : ∀ φ, THFull φ → GValid.{u} φ
  | _, .base h => thSupport_valid _ h
  | _, .hOrdinary => hOrdinary_gvalid
  | _, .transColl => gvalid_transDecoded_collection

theorem con_THFull : PSet.Con THFull := Consumer.Con.of_gvalid thFull_valid.{0}

theorem prf_transDecoded_replacement :
    PSet.Prf THFull (PSet.ZFAx.repl Syntax.transDecodeF) :=
  PSet.ZFAx.repl_of_collection_of Syntax.transDecodeF (PSet.Prf.ax THFull.transColl)

/-- info: 'GSet.HRel.inverseUnique_of_order' does not depend on any axioms -/
#guard_msgs in #print axioms inverseUnique_of_order
/-- info: 'GSet.HRel.gvalid_transDecoded_collection' does not depend on any axioms -/
#guard_msgs in #print axioms gvalid_transDecoded_collection
/-- info: 'GSet.HRel.con_THFull' does not depend on any axioms -/
#guard_msgs in #print axioms con_THFull
/-- info: 'GSet.HRel.prf_transDecoded_replacement' does not depend on any axioms -/
#guard_msgs in #print axioms prf_transDecoded_replacement

end GSet.HRel
