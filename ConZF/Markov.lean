import ConZF.Acc
/-!
A guarded search-length construction for the negative membership relation.
Actual accessibility of omega supplies Markov witnesses, including witnesses
in Type via large elimination of Acc. `AccHyp` consequently supplies
uniform double-negated Markov and DNS for families of decidable searches.
These are lower bounds on the hypothesis, not proofs that it is independent
of Lean's constructive core, and not a proof of the hypothesis itself.
-/
universe v
namespace PSet

/-- Uniform Markov principle for predicates equipped with decision procedures. -/
def Markov : Prop :=
  ∀ P : Nat → Prop, (∀ n, Decidable (P n)) → (¬¬∃ n, P n) → ∃ n, P n

/-- Uniform Markov principle with decidability expressed by disjunctions in Prop. -/
def PropMarkov : Prop :=
  ∀ P : Nat → Prop, (∀ n, P n ∨ ¬P n) → (¬¬∃ n, P n) → ∃ n, P n

theorem PropMarkov.markov (h : PropMarkov) : Markov := fun P dec =>
  h P fun n => match dec n with
    | .isTrue hp => .inl hp
    | .isFalse hn => .inr hn

private def First (P : Nat → Prop) (k d : Nat) : Prop :=
  P (k+d) ∧ ∀ j, j < d → ¬ P (k+j)

private theorem first_succ {P : Nat → Prop} {k d : Nat} :
    First P k (d+1) ↔ ¬P k ∧ First P (k+1) d := by
  constructor
  · intro h
    exact ⟨h.2 0 (Nat.zero_lt_succ d), (Nat.succ_add k d).symm ▸ h.1,
      fun j hj => (Nat.succ_add k j).symm ▸ h.2 (j+1) (Nat.succ_lt_succ hj)⟩
  · rintro ⟨hn, hp, hrest⟩
    constructor
    · rw [Nat.add_succ]
      exact Nat.succ_add k d ▸ hp
    · intro j hj
      cases j with
      | zero => exact hn
      | succ j =>
        rw [Nat.add_succ]
        exact Nat.succ_add k j ▸ hrest j (Nat.lt_of_succ_lt_succ hj)

private theorem first_unique {P : Nat → Prop} {k d e : Nat}
    (hd : First P k d) (he : First P k e) : d = e := by
  rcases Nat.lt_trichotomy d e with h | h | h
  · exact (he.2 d h hd.1).elim
  · exact h
  · exact (hd.2 e h he.1).elim

private theorem first_exists (P : Nat → Prop) (dec : ∀ n, P n ∨ ¬P n) :
    ∀ d k, P (k+d) → ∃ e, First P k e := by
  intro d
  induction d with
  | zero => exact fun k hk => ⟨0, hk, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | succ d ih =>
    intro k hk
    rcases dec k with hp | hn
    · exact ⟨0, hp, fun _ h => (Nat.not_lt_zero _ h).elim⟩
    · obtain ⟨e, he⟩ := ih (k+1) ((Nat.succ_add k d).symm ▸ hk)
      exact ⟨e+1, first_succ.2 ⟨hn, he⟩⟩

/-- A guarded, computable ordinal representing the remaining search length when it exists. -/
private def searchRank (P : Nat → Prop) (k : Nat) : PSet.{0} :=
  iUnion (fun d : Nat => guard (First P k d) (fun _ => ofNat d))

private theorem searchRank_eq {P : Nat → Prop} {k d : Nat} (hd : First P k d) :
    searchRank P k ≈ ofNat d := by
  refine ext fun z => ⟨?_, ?_⟩
  · intro hz
    refine Stable.of_nn (mem_iUnion.1 hz) fun ⟨e, he⟩ => ?_
    refine Stable.of_nn (mem_guard.1 he) fun ⟨he, hz⟩ => ?_
    exact (first_unique he hd) ▸ hz
  · intro hz
    exact mem_iUnion.2 (nn_intro ⟨d, mem_guard.2 (nn_intro ⟨hd, hz⟩)⟩)

private theorem searchRank_mem_omega (P : Nat → Prop) (dec : ∀ n, P n ∨ ¬P n) (k : Nat)
    (h : ¬¬∃ d, P (k+d)) : searchRank P k ∈ omega := by
  refine Stable.of_nn h fun ⟨d, hd⟩ => ?_
  obtain ⟨e, he⟩ := first_exists P dec d k hd
  exact mem_omega.2 (nn_intro ⟨e, searchRank_eq he⟩)

private theorem searchRank_desc (P : Nat → Prop) (dec : ∀ n, P n ∨ ¬P n) (k : Nat)
    (hn : ¬P k) (h : ¬¬∃ d, P (k+d)) : searchRank P (k+1) ∈ searchRank P k := by
  refine Stable.of_nn h fun ⟨d, hd⟩ => ?_
  obtain ⟨e, he⟩ := first_exists P dec d k hd
  cases e with
  | zero => exact (hn he.1).elim
  | succ e =>
    have hc := searchRank_eq (first_succ.1 he).2
    have hp := searchRank_eq he
    exact (mem_congr_left hc).2 ((mem_congr_right hp).2 (self_mem_succ (ofNat e)))

private theorem tail_search {P : Nat → Prop} {k : Nat} (hn : ¬P k)
    (h : ¬¬∃ d, P (k+d)) : ¬¬∃ d, P ((k+1)+d) := by
  refine nn_map ?_ h
  rintro ⟨d, hd⟩
  cases d with
  | zero => exact (hn hd).elim
  | succ d => exact ⟨d, (Nat.succ_add k d).symm ▸ hd⟩

private theorem search_of_acc (P : Nat → Prop) (dec : ∀ n, P n ∨ ¬P n)
    {a : PSet.{0}} (ha : Acc (· ∈ ·) a) :
    ∀ k, a = searchRank P k → (¬¬∃ d, P (k+d)) → ∃ n, P n := by
  induction ha with
  | intro a _ ih =>
    intro k he h
    rcases dec k with hp | hn
    · exact ⟨k, hp⟩
    · exact ih _ (he.symm ▸ searchRank_desc P dec k hn h) (k+1) rfl (tail_search hn h)

/-- Accessibility of omega supplies Markov's principle with propositional decisions. -/
theorem prop_markov_of_acc_omega (ha : Acc (· ∈ ·) omega.{0})
    (P : Nat → Prop) (dec : ∀ n, P n ∨ ¬P n) (h : ¬¬∃ n, P n) : ∃ n, P n := by
  have h0 : ¬¬∃ d, P (0+d) := nn_map (fun ⟨d, hd⟩ => ⟨d, (Nat.zero_add d).symm ▸ hd⟩) h
  exact search_of_acc P dec (ha.inv (searchRank_mem_omega P dec 0 h0)) 0 rfl h0

/-- The same recursion can return a witness in Type when the predicate has a decision
procedure. The first-hit witnesses used in descent remain entirely inside Prop. -/
private def witness_of_acc (P : Nat → Prop) (dec : ∀ n, Decidable (P n))
    {a : PSet.{0}} (ha : Acc (· ∈ ·) a) :
    ∀ k, a = searchRank P k → (¬¬∃ d, P (k+d)) → {n : Nat // P n} := by
  have choices : ∀ n, P n ∨ ¬P n := fun n =>
    match dec n with
    | .isTrue hp => .inl hp
    | .isFalse hn => .inr hn
  induction ha with
  | intro a _ ih =>
    intro k he h
    cases dec k with
    | isTrue hp => exact ⟨k, hp⟩
    | isFalse hn =>
      exact ih _ (he.symm ▸ searchRank_desc P choices k hn h) (k+1) rfl (tail_search hn h)

def witness_of_acc_omega (ha : Acc (· ∈ ·) omega.{0})
    (P : Nat → Prop) (dec : ∀ n, Decidable (P n)) (h : ¬¬∃ n, P n) : {n : Nat // P n} := by
  have choices : ∀ n, P n ∨ ¬P n := fun n =>
    match dec n with
    | .isTrue hp => .inl hp
    | .isFalse hn => .inr hn
  have h0 : ¬¬∃ d, P (0+d) := nn_map (fun ⟨d, hd⟩ => ⟨d, (Nat.zero_add d).symm ▸ hd⟩) h
  exact witness_of_acc P dec (ha.inv (searchRank_mem_omega P choices 0 h0)) 0 rfl h0

theorem markov_of_acc_omega (ha : Acc (· ∈ ·) omega.{0}) : Markov :=
  PropMarkov.markov (prop_markov_of_acc_omega ha)

theorem not_not_prop_markov_of_not_not_acc_omega
    (h : ¬¬Acc (· ∈ ·) omega.{0}) : ¬¬PropMarkov :=
  nn_map prop_markov_of_acc_omega h

theorem not_not_markov_of_not_not_acc_omega (h : ¬¬Acc (· ∈ ·) omega.{0}) : ¬¬Markov :=
  nn_map markov_of_acc_omega h

theorem not_not_prop_markov_of_accHyp (h : AccHyp.{0}) : ¬¬PropMarkov :=
  not_not_prop_markov_of_not_not_acc_omega (not_not_acc_of_accHyp h omega)

theorem not_not_markov_of_accHyp (h : AccHyp.{0}) : ¬¬Markov :=
  nn_map PropMarkov.markov (not_not_prop_markov_of_accHyp h)

/-- The pointwise hypothesis does not escape the obstruction: at `ω`, which is hereditarily good,
it is double-negated accessibility of `ω`. -/
theorem not_not_prop_markov_of_pointwise (h : PointwiseHGAcc.{0}) : ¬¬PropMarkov :=
  not_not_prop_markov_of_not_not_acc_omega (h omega cls_omega)

/-- Double-negation shift for families of decidable searches. -/
theorem search_dns_of_accHyp {α : Sort v} (hacc : AccHyp.{0})
    (P : α → Nat → Prop) (dec : ∀ i n, P i n ∨ ¬P i n)
    (h : ∀ i, ¬¬∃ n, P i n) : ¬¬∀ i, ∃ n, P i n :=
  nn_map (fun mp i => mp (P i) (dec i) (h i)) (not_not_prop_markov_of_accHyp hacc)

/-- info: 'PSet.prop_markov_of_acc_omega' does not depend on any axioms -/
#guard_msgs in #print axioms prop_markov_of_acc_omega
/-- info: 'PSet.not_not_prop_markov_of_accHyp' does not depend on any axioms -/
#guard_msgs in #print axioms not_not_prop_markov_of_accHyp
/-- info: 'PSet.markov_of_acc_omega' does not depend on any axioms -/
#guard_msgs in #print axioms markov_of_acc_omega
/-- info: 'PSet.witness_of_acc_omega' does not depend on any axioms -/
#guard_msgs in #print axioms witness_of_acc_omega
/-- info: 'PSet.search_dns_of_accHyp' does not depend on any axioms -/
#guard_msgs in #print axioms search_dns_of_accHyp
/-- info: 'PSet.not_not_markov_of_accHyp' does not depend on any axioms -/
#guard_msgs in #print axioms not_not_markov_of_accHyp
/-- info: 'PSet.not_not_prop_markov_of_pointwise' does not depend on any axioms -/
#guard_msgs in #print axioms not_not_prop_markov_of_pointwise
end PSet
