import ConZF.Graph.Rank
/-!
Pairs, products, and unions of graph sets, all as small ranges (`GSet.range`): the unordered
pair, the singleton, the Kuratowski ordered pair with its congruence and injectivity laws, the
binary product, the binary union, and the union of a set. Each has the expected negative
membership law. Also the reachable support of a graph set: the vertices strictly below the root
along finite paths, which negatively represents every member and is closed under members
(`supp_of_mem`, `supp_closed`); this is the predecessor coverage used by envelopes.
-/
universe u

namespace GSet

/-- A two-element index type in `Type u`. -/
inductive Two : Type u
  | fst
  | snd

section pair
variable (G H : GSet.{u})

/-- The unordered pair. -/
def pair : GSet.{u} := range fun i : Two.{u} => match i with
  | .fst => G
  | .snd => H

theorem mem_pair {K : GSet.{u}} : Mem K (pair G H) ↔ ¬¬(Equiv K G ∨ Equiv K H) := by
  refine (mem_range _).trans (nn_congr ⟨fun ⟨i, e⟩ => ?_, fun h => ?_⟩)
  · cases i with
    | fst => exact .inl e
    | snd => exact .inr e
  · rcases h with e | e
    · exact ⟨.fst, e⟩
    · exact ⟨.snd, e⟩

theorem pair_congr {G' H' : GSet.{u}} (eG : Equiv G G') (eH : Equiv H H') :
    Equiv (pair G H) (pair G' H') :=
  ext fun _ => (mem_pair G H).trans ((nn_congr (or_congr ⟨fun e => e.trans eG, fun e => e.trans eG.symm⟩
    ⟨fun e => e.trans eH, fun e => e.trans eH.symm⟩)).trans (mem_pair G' H').symm)

theorem pair_comm : Equiv (pair G H) (pair H G) :=
  ext fun _ => (mem_pair G H).trans ((nn_congr or_comm).trans (mem_pair H G).symm)

theorem mem_pair_left : Mem G (pair G H) := (mem_pair G H).2 (nn_intro (.inl (Equiv.refl G)))
theorem mem_pair_right : Mem H (pair G H) := (mem_pair G H).2 (nn_intro (.inr (Equiv.refl H)))

/-- The singleton. -/
def single : GSet.{u} := pair G G

theorem mem_single {K : GSet.{u}} : Mem K (single G) ↔ Equiv K G :=
  (mem_pair G G).trans ⟨fun h => Stable.of_nn h fun h => h.elim id id, fun e => nn_intro (.inl e)⟩

/-- The Kuratowski ordered pair. -/
def opair : GSet.{u} := pair (single G) (pair G H)

theorem opair_congr {G' H' : GSet.{u}} (eG : Equiv G G') (eH : Equiv H H') :
    Equiv (opair G H) (opair G' H') :=
  pair_congr _ _ (pair_congr _ _ eG eG) (pair_congr _ _ eG eH)

/-- Equivalent unordered pairs with a common first component have equivalent seconds. -/
theorem pair_inj_right {H' : GSet.{u}} (e : Equiv (pair G H) (pair G H')) : Equiv H H' := by
  have h1 : Mem H (pair G H') := Mem.congr_right e (mem_pair_right G H)
  have h2 : Mem H' (pair G H) := Mem.congr_right e.symm (mem_pair_right G H')
  refine Stable.of_nn ((mem_pair G H').1 h1) fun
    | .inl eH => Stable.of_nn ((mem_pair G H).1 h2) fun
      | .inl eH' => eH.trans eH'.symm
      | .inr eH' => eH'.symm
    | .inr eH => eH

/-- **Injectivity of the ordered pair.** -/
theorem opair_inj {G' H' : GSet.{u}} (e : Equiv (opair G H) (opair G' H')) :
    Equiv G G' ∧ Equiv H H' := by
  -- the singleton of `G` is a member of the other pair, so `G ≈ G'`
  have hs : Mem (single G) (opair G' H') := Mem.congr_right e (mem_pair_left _ _)
  have eG : Equiv G G' := by
    refine Stable.of_nn ((mem_pair _ _).1 hs) fun
      | .inl e1 => (mem_single G').1 (Mem.congr_right e1 (mem_single G |>.2 (Equiv.refl G)))
      | .inr e1 => ((mem_single G).1 (Mem.congr_right e1.symm (mem_pair_left G' H'))).symm
  refine ⟨eG, ?_⟩
  -- transport the second components to a common first component
  have e' : Equiv (pair G H) (pair G H') :=
    pair_inj_right (single G) _ (e.trans (opair_congr G' H' eG.symm (Equiv.refl H')))
  exact pair_inj_right G H e'

end pair

/-! ### Products and unions -/

section prod
variable (G H : GSet.{u})

/-- The binary product: ordered pairs of members. -/
def prod : GSet.{u} :=
  range fun p : {a : G.A // G.R a G.r} × {b : H.A // H.R b H.r} => opair (G.at' p.1.1) (H.at' p.2.1)

theorem mem_prod {K : GSet.{u}} : Mem K (prod G H) ↔
    ¬¬∃ (a : G.A) (b : H.A), G.R a G.r ∧ H.R b H.r ∧ Equiv K (opair (G.at' a) (H.at' b)) :=
  (mem_range _).trans (nn_congr ⟨fun ⟨p, e⟩ => ⟨p.1.1, p.2.1, p.1.2, p.2.2, e⟩,
    fun ⟨a, b, ha, hb, e⟩ => ⟨(⟨a, ha⟩, ⟨b, hb⟩), e⟩⟩)

theorem opair_mem_prod {A B : GSet.{u}} (hA : Mem A G) (hB : Mem B H) : Mem (opair A B) (prod G H) :=
  (mem_prod G H).2 (Stable.of_nn hA fun ⟨a, ha, eA⟩ => Stable.of_nn hB fun ⟨b, hb, eB⟩ =>
    nn_intro ⟨a, b, ha, hb, opair_congr _ _ eA eB⟩)

/-- The binary union. -/
def union : GSet.{u} :=
  range fun s : {a : G.A // G.R a G.r} ⊕ {b : H.A // H.R b H.r} => match s with
    | .inl a => G.at' a.1
    | .inr b => H.at' b.1

theorem mem_union {K : GSet.{u}} : Mem K (union G H) ↔ ¬¬(Mem K G ∨ Mem K H) := by
  refine (mem_range _).trans ⟨nn_map fun ⟨s, e⟩ => ?_, fun h => nn_bind h fun h => ?_⟩
  · cases s with
    | inl a => exact .inl (nn_intro ⟨a.1, a.2, e⟩)
    | inr b => exact .inr (nn_intro ⟨b.1, b.2, e⟩)
  · rcases h with h | h
    · exact nn_map (fun ⟨a, ha, e⟩ => ⟨.inl ⟨a, ha⟩, e⟩) h
    · exact nn_map (fun ⟨b, hb, e⟩ => ⟨.inr ⟨b, hb⟩, e⟩) h

/-- The union of a set: the members of its members. -/
def sUnion : GSet.{u} :=
  range fun p : Σ a : {a : G.A // G.R a G.r}, {b : G.A // G.R b a.1} => G.at' p.2.1

theorem mem_sUnion {K : GSet.{u}} : Mem K (sUnion G) ↔ ¬¬∃ Y, Mem Y G ∧ Mem K Y := by
  refine (mem_range _).trans ⟨nn_map fun ⟨p, e⟩ => ?_, fun h => nn_bind h fun ⟨Y, hY, hK⟩ => ?_⟩
  · exact ⟨G.at' p.1.1, at'_mem p.1.2, Mem.congr_left e.symm (at'_mem p.2.2)⟩
  · refine Stable.of_nn hY fun ⟨a, ha, eY⟩ => ?_
    refine Stable.of_nn (Mem.congr_right eY hK) fun ⟨b, hb, eK⟩ => ?_
    exact nn_intro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, eK⟩

end prod

/-! ### The reachable support -/

section supp
variable (E : GSet.{u})

/-- The reachable support: vertices strictly below the root along finite paths. -/
abbrev Supp : Type u := {j : E.A // TC E.R j E.r}

/-- Every member is negatively represented by a support vertex. -/
theorem supp_of_mem {z : GSet.{u}} (h : Mem z E) : ¬¬∃ j : Supp E, Equiv z (E.at' j.1) :=
  nn_map (fun ⟨a, ha, e⟩ => ⟨⟨a, TC.of_rel ha⟩, e⟩) h

/-- Members of a represented set are represented by lower support vertices. -/
theorem supp_closed {j : Supp E} {z w : GSet.{u}} (e : Equiv z (E.at' j.1)) (hw : Mem w z) :
    ¬¬∃ k : Supp E, Equiv w (E.at' k.1) :=
  nn_map (fun ⟨a, ha, e'⟩ => ⟨⟨a, (TC.of_rel ha).trans j.2⟩, e'⟩) (Mem.congr_right e hw)

end supp

/-- info: 'GSet.opair_inj' does not depend on any axioms -/
#guard_msgs in #print axioms opair_inj
/-- info: 'GSet.mem_sUnion' does not depend on any axioms -/
#guard_msgs in #print axioms mem_sUnion

end GSet
