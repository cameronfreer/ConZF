import ConZF.Sim
/-!
A producer from semantic hypotheses: the finite-predecessor fragment. For a relation `R` on a small
carrier with *negatively finite* predecessor families (each family is not not covered by a finite
list, not chosen as a function of the point) and induction for stable predicates, every point has
not not a finite height (`finHt_of_sInd`). Finite height gives a simulation into `natCode` at that
height (`sim_natCode_of_finHt`); its certificate is on the same carrier `ULift Nat` for every
point, so no enlargement is needed here. Soundness then bounds every semantic collapse value by a
finite ordinal, hence the collapse by `ω` (`collapse_subset_omega`). The collapse values are a
relation in `Prop` throughout: no native function assigning ordinals to points, and no
accessibility of `R`, is assumed; stable induction on `R` is itself derived from descent into the
collapse values (`sInd_of_desc`).

The scope is the fragment: the resulting order type is at most `ω`. Arbitrary countable
well-orders, whose predecessor families need not be finite, are not covered.
-/
universe u v

namespace PSet

section
variable {I : Type v} (R : I → I → Prop)

/-- Finite height, as a stable predicate: no predecessors, or every predecessor of height `n`. -/
def FinHt : I → Nat → Prop
  | i, 0 => ∀ j, ¬ R j i
  | i, n+1 => ∀ j, R j i → FinHt j n

instance finHt_stable : ∀ {i : I} {n : Nat}, Stable (FinHt R i n)
  | _, 0 => inferInstanceAs (Stable (∀ _, ¬_))
  | _, n+1 => by
    have : ∀ j, Stable (FinHt R j n) := fun _ => finHt_stable
    exact inferInstanceAs (Stable (∀ j, _ → FinHt R j n))

theorem FinHt.mono : ∀ {n m : Nat} {i : I}, n ≤ m → FinHt R i n → FinHt R i m
  | 0, 0, _, _, h => h
  | 0, _+1, _, _, h => fun j hj => (h j hj).elim
  | _+1, 0, _, h, _ => (Nat.not_succ_le_zero _ h).elim
  | _+1, _+1, _, h, hf => fun j hj => FinHt.mono (Nat.le_of_succ_le_succ h) (hf j hj)

/-- Induction on `R` for stable predicates. -/
def SInd : Prop :=
  ∀ P : I → Prop, (∀ i, Stable (P i)) → (∀ i, (∀ j, R j i → P j) → P i) → ∀ i, P i

/-- Negatively finite predecessor families: a covering list exists, not not, at each point. -/
def NegFin : Prop := ∀ i, ¬¬∃ l : List I, ∀ j, R j i → j ∈ l

/-- Finitely many points of not not finite height have not not a common finite height. -/
theorem finHt_list {i : I} (ih : ∀ j, R j i → ¬¬∃ n, FinHt R j n) :
    ∀ l : List I, ¬¬∃ M, ∀ j, j ∈ l → R j i → FinHt R j M
  | [] => nn_intro ⟨0, fun _ h => nomatch h⟩
  | j :: l => by
    refine nn_bind (finHt_list ih l) fun ⟨M, hM⟩ => ?_
    refine Stable.by_cases (R j i) (fun hj => ?_) fun hj => ?_
    · refine nn_map (fun ⟨n, hn⟩ => ⟨M + n, fun k hk hkj => ?_⟩) (ih j hj)
      cases hk with
      | head => exact FinHt.mono R (Nat.le_add_left n M) hn
      | tail _ hk => exact FinHt.mono R (Nat.le_add_right M n) (hM k hk hkj)
    · refine nn_intro ⟨M, fun k hk hkj => ?_⟩
      cases hk with
      | head => exact (hj hkj).elim
      | tail _ hk => exact hM k hk hkj

/-- **Finite heights.** Stable induction and negatively finite predecessors give every point not
not a finite height. No accessibility of `R` is used. -/
theorem finHt_of_sInd (hind : SInd R) (hfin : NegFin R) : ∀ i, ¬¬∃ n, FinHt R i n := by
  refine hind (fun i => ¬¬∃ n, FinHt R i n) (fun _ => inferInstance) fun i ih => ?_
  refine nn_bind (hfin i) fun ⟨l, hl⟩ => ?_
  refine nn_map (fun ⟨M, hM⟩ => ⟨M + 1, fun j hj => hM j (hl j hj) hj⟩) (finHt_list R ih l)

/-- The node of `natCode` at `n`. -/
def natNode (n : Nat) : {x : ULift.{u} Nat // natCode.S x} := ⟨⟨n⟩, trivial⟩

/-- Finite height `n` is a simulation into `natCode` at `n`. -/
theorem sim_natCode_of_finHt : ∀ {n : Nat} {i : I}, FinHt R i n → Sim R natCode.{u} i (natNode n)
  | 0, _, h => (sim_iff R natCode).2 fun j hj => (h j hj).elim
  | n+1, _, h => (sim_iff R natCode).2 fun j hj =>
      nn_intro ⟨⟨natNode n, Nat.lt_succ_self n⟩, sim_natCode_of_finHt (h j hj)⟩

theorem ht_natNode (n : Nat) : natCode.{u}.ht (natNode n) ≈ ofNat n :=
  rank_natCode_tree n (natNode n) rfl

/-! ### The collapse -/

variable {α : I → PSet.{u} → Prop}

/-- Stable induction on `R` from descent into targets: if every point has a target and the
target of a predecessor is an element of the target, then `∈`-induction on the targets gives
induction on `R` for stable predicates. -/
theorem sInd_of_desc (htot : ∀ i, ¬¬∃ t, α i t)
    (desc : ∀ j i t t', R j i → α j t → α i t' → t ∈ t') : SInd R := by
  intro P hs H i
  have key : ∀ t : PSet.{u}, ∀ i, α i t → P i := fun t =>
    mem_induction (P := fun t => ∀ i, α i t → P i) (fun t ih i hit => H i fun j hj =>
      Stable.of_nn (htot j) fun ⟨t', hjt⟩ => ih t' (desc j i t' t hj hjt hit) j hjt) t
  exact Stable.of_nn (htot i) fun ⟨t, hit⟩ => key t i hit

/-- **The bound.** Every collapse value is included in a finite ordinal, hence is an element of
`ω`, from coverage, descent, totality, ordinal-valuedness, and negatively finite predecessors. -/
theorem collapse_value_mem_omega (hc : Cover R α) (hord : ∀ i t, α i t → IsOrd t)
    (htot : ∀ i, ¬¬∃ t, α i t) (desc : ∀ j i t t', R j i → α j t → α i t' → t ∈ t')
    (hfin : NegFin R) : ∀ i t, α i t → t ∈ omega.{u} := by
  intro i t hit
  refine Stable.of_nn (finHt_of_sInd R (sInd_of_desc R htot desc) hfin i) fun ⟨n, hn⟩ => ?_
  have sub := subset_ht_of_sim R natCode hc hord (natNode n) i t hit (sim_natCode_of_finHt R hn)
  have : t ∈ succ (ofNat n) := (hord i t hit).mem_succ_of_subset (isOrd_ofNat n)
    fun ξ hξ => (mem_congr_right (ht_natNode n)).1 (sub ξ hξ)
  exact mem_ofNat_mem_omega (n := n+1) this

/-- The collapse of the whole carrier, the union of the successors of the values, is included
in `ω`. -/
theorem collapse_subset_omega (hc : Cover R α) (hord : ∀ i t, α i t → IsOrd t)
    (htot : ∀ i, ¬¬∃ t, α i t) (desc : ∀ j i t t', R j i → α j t → α i t' → t ∈ t')
    (hfin : NegFin R) {η : PSet.{u}} (hη : ∀ ξ, ξ ∈ η → ¬¬∃ i t, α i t ∧ ξ ∈ succ t) :
    ∀ ξ, ξ ∈ η → ξ ∈ omega.{u} := by
  intro ξ hξ
  refine Stable.of_nn (hη ξ hξ) fun ⟨i, t, hit, hξ⟩ => ?_
  have ht := collapse_value_mem_omega R hc hord htot desc hfin i t hit
  exact Stable.of_nn (mem_succ.1 hξ) fun
    | .inl h => isOrd_omega.trans t ht ξ h
    | .inr e => (mem_congr_left e).2 ht

end

/-- info: 'PSet.finHt_of_sInd' does not depend on any axioms -/
#guard_msgs in #print axioms finHt_of_sInd
/-- info: 'PSet.collapse_subset_omega' does not depend on any axioms -/
#guard_msgs in #print axioms collapse_subset_omega

end PSet
