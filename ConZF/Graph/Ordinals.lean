import ConZF.Graph.Levels
import ConZF.EnvFml
/-!
The ordinals of a level. The parameter-free formula `ordF 0` ("is an ordinal": a transitive set
of transitive sets) is correct over any transitive graph set (`sat_ordF`), so it names, at every
stage `a`, the ordinal part of `L α a`. That ordinal part is the rank of the presentation at `a`
(`ordinals_of_L`): an ordinal in `Def (L α b)` is a subset of `L α b`, whose ordinals lie below
the ordinal at `b` by induction, and that ordinal is itself definable over `L α b` by `ordF`.
For an ordinal presentation, normalization recovers `Ord ∩ L_a = a`
(`ordinals_of_L_root`).

Two canonical, parameter-free names are exported: `ordName a` denotes the ordinal at `a`
(`nameVal_ordName`), and `levelName a`, with the always-true formula, denotes `L α a` itself
(`nameVal_levelName`). A name born at `a` is available at levels strictly above `a`
(`ord_mem_L`, `L_mem_L`); neither the ordinal at `a` nor `L α a` is claimed as a member of
`L α a`.
-/
universe u

namespace GSet
open PSet.Fml

/-! ### The ordinal formula over transitive graph sets -/

section
variable {M : GSet.{u}} (hM : Trans M) {e : Nat → GSet.{u}}
include hM

theorem sat_transF {t : Nat} (ht : Mem (e t) M) : Sat (Mem · M) (transF t) e ↔ Trans (e t) :=
  ⟨fun h K hK K' hK' => h K (hM _ ht K hK) hK K' (hM _ (hM _ ht K hK) K' hK') hK',
   fun h K _ hK K' _ hK' => h K hK K' hK'⟩

/-- **Ordinal-formula correctness** over a transitive graph set. -/
theorem sat_ordF {r : Nat} (hr : Mem (e r) M) : Sat (Mem · M) (ordF r) e ↔ IsOrd (e r) :=
  sat_and.trans ⟨fun ⟨h1, h2⟩ => ⟨(sat_transF hM hr).1 h1, fun K hK =>
      (sat_transF (e := Env.cons K e) (t := 0) hM (hM _ hr K hK)).1 (h2 K (hM _ hr K hK) hK)⟩,
    fun h => ⟨(sat_transF hM hr).2 h.1, fun K hK hK' =>
      (sat_transF (e := Env.cons K e) (t := 0) hM hK).2 (h.2 K hK')⟩⟩

end

/-! ### Ordinal inclusion -/

theorem isOrd_rank_at' (G : GSet.{u}) (a : G.A) : IsOrd ((rank G).at' a) := isOrd_rank (G.at' a)

/-- For graph ordinals, inclusion is membership or equivalence. -/
theorem IsOrd.subset {a b : GSet.{u}} (ha : IsOrd a) (hb : IsOrd b) (h : Subset a b) :
    ¬¬(Mem a b ∨ Equiv a b) :=
  nn_map (fun
    | .inl h' => .inl h'
    | .inr (.inl h') => .inr h'
    | .inr (.inr h') => (not_mem_self b (h b h')).elim) (ha.trichotomy hb)

/-! ### Canonical names -/

section
variable (α : GSet.{u})

/-- The name of the ordinal at `a`: "is an ordinal", parameter-free. -/
def ordName (a : α.A) : Name α.A := .def' a (ordF 0) 0 fun i => nomatch i

/-- The name of the level `L α a`: the always-true formula, parameter-free. -/
def levelName (a : α.A) : Name α.A := .def' a (imp fls fls) 0 fun i => nomatch i

theorem valid_ordName (a : α.A) : Valid α (ordName α a) := ⟨by decide, fun i => nomatch i⟩

theorem valid_levelName (a : α.A) : Valid α (levelName α a) := ⟨by decide, fun i => nomatch i⟩

/-- The level name denotes the level. -/
theorem nameVal_levelName (a : α.A) : Equiv (nameVal α (levelName α a)) (L α a) :=
  ext fun K => (nameVal_spec α (valid_levelName α a) K).trans ⟨And.left, fun h => ⟨h, id⟩⟩

theorem L_mem_L {a a' : α.A} (h : Stage α a a') : Mem (L α a) (L α a') :=
  (mem_L α).2 (nn_intro ⟨levelName α a, valid_levelName α a, h, (nameVal_levelName α a).symm⟩)

/-- The ordinal name denotes the ordinal part of the level at its birth. -/
theorem mem_nameVal_ordName (a : α.A) (K : GSet.{u}) :
    Mem K (nameVal α (ordName α a)) ↔ Mem K (L α a) ∧ IsOrd K :=
  (nameVal_spec α (valid_ordName α a) K).trans (and_congr_right fun hK =>
    sat_ordF (e := Env.cons K (valEnv α (ordName α a))) (r := 0) (trans_L α a) hK)

/-- **The ordinals of a level** are the rank of the presentation at that stage. -/
theorem ordinals_of_L : ∀ a : α.A, ∀ K, (Mem K (L α a) ∧ IsOrd K) ↔ Mem K ((rank α).at' a) := by
  refine swf_tc α.swf (fun a => ∀ K, (Mem K (L α a) ∧ IsOrd K) ↔ Mem K ((rank α).at' a))
    (fun _ => inferInstance) fun a ih K => ?_
  constructor
  · rintro ⟨hK, hKo⟩
    refine Stable.of_nn ((mem_L_iff_Def α).1 hK) fun ⟨b, hb, hKb⟩ => ?_
    have sub : Subset K ((rank α).at' b) := fun K' hK' =>
      (ih b hb K').1 ⟨subset_of_mem_Def _ hKb K' hK', hKo.mem hK'⟩
    have hb' : Mem ((rank α).at' b) ((rank α).at' a) := at'_mem (G := (rank α).at' a) hb
    refine Stable.of_nn (hKo.subset (isOrd_rank_at' α b) sub) fun
      | .inl h => trans_rank_at' α a _ hb' K h
      | .inr e => Mem.congr_left e.symm hb'
  · intro hK
    refine Stable.of_nn hK fun ⟨c, hc, e⟩ => ?_
    have hval : Equiv (nameVal α (ordName α c)) ((rank α).at' c) :=
      ext fun K' => (mem_nameVal_ordName α c K').trans (ih c hc K')
    refine ⟨(mem_L α).2 (nn_intro ⟨ordName α c, valid_ordName α c, hc, e.trans hval.symm⟩),
      (isOrd_rank_at' α c).congr e.symm⟩

/-- The ordinal name denotes the ordinal at its birth. -/
theorem nameVal_ordName (a : α.A) : Equiv (nameVal α (ordName α a)) ((rank α).at' a) :=
  ext fun K => (mem_nameVal_ordName α a K).trans (ordinals_of_L α a K)

theorem ord_mem_L {a a' : α.A} (h : Stage α a a') : Mem ((rank α).at' a) (L α a') :=
  (mem_L α).2 (nn_intro ⟨ordName α a, valid_ordName α a, h, (nameVal_ordName α a).symm⟩)

/-- **`Ord ∩ L_α = α`** for an ordinal presentation, at the root, by normalization. -/
theorem ordinals_of_L_root (hα : IsOrd α) (K : GSet.{u}) :
    (Mem K (L α α.r) ∧ IsOrd K) ↔ Mem K α :=
  (ordinals_of_L α α.r K).trans (mem_congr_right (rank_equiv_of_isOrd hα))

end

/-- info: 'GSet.sat_ordF' does not depend on any axioms -/
#guard_msgs in #print axioms sat_ordF
/-- info: 'GSet.ordinals_of_L' does not depend on any axioms -/
#guard_msgs in #print axioms ordinals_of_L
/-- info: 'GSet.ordinals_of_L_root' does not depend on any axioms -/
#guard_msgs in #print axioms ordinals_of_L_root

end GSet
