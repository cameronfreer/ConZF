import ConZF.Bar
import ConZF.RankGraph
import ConZF.NativeBound
/-!
The scope check: a countable source concentrates at the zero real. Start from an arbitrary
functional relation `Φ` on `ω`, possibly partial, and totalize it by `Tot Φ n z`: `z` is empty
if there is no output, the singleton of the output otherwise (a negative disjunction; no least
rank, no first-order rank). Define `Lift Φ X z` on the negative Cantor space: `z` is empty at
the zero real, and `Tot Φ n z` where `n` is the first `1` of `X` otherwise. `Lift Φ` is
negatively total and functional. Then

    Φ has a cap  ↔  Lift Φ has a local cap at the zero real  ↔  Lift Φ has a source-wide cap

(`countable_reduction`). Every nonzero point has a local cap (`locCap_of_firstOne`), so
totality, functionality, and local caps at every other point do not discharge the local cap at
the last point: proving it would already solve the countable-source cap problem. This is a
reduction, not an impossibility result. It also explains why `Lift Φ` is outside the
finite-observation fragment: the zero branch is a condition on all bits.
-/
universe u

namespace PSet

/-! ### Words below a prefix -/

theorem prec_of_agree : ∀ (s : List Bool) {X Y : PSet.{u}},
    (∀ k, k < s.length → (ofNat k ∈ X ↔ ofNat k ∈ Y)) → Prec s X → Prec s Y
  | [], _, _, _, _ => trivial
  | _ :: s, _, _, h, ⟨hp, hb⟩ =>
    ⟨prec_of_agree s (fun k hk => h k (Nat.lt_succ_of_lt hk)) hp,
     hb.trans (h s.length (Nat.lt_succ_self _))⟩

/-- The word of `k` zeros. -/
def zeros : Nat → List Bool
  | 0 => []
  | k+1 => false :: zeros k

theorem zeros_length : ∀ k, (zeros k).length = k
  | 0 => rfl
  | k+1 => congrArg Nat.succ (zeros_length k)

theorem prec_zeros {X : PSet.{u}} :
    ∀ k : Nat, (∀ j, j < k → ¬ ofNat j ∈ X) → Prec (zeros k) X
  | 0, _ => trivial
  | k+1, h => ⟨prec_zeros k fun j hj => h j (Nat.lt_succ_of_lt hj),
      ⟨fun e => Bool.noConfusion e, fun hx => (h _ (cast (congrArg (· < k+1) (zeros_length k).symm)
        (Nat.lt_succ_self k)) hx).elim⟩⟩

theorem not_mem_of_prec_zeros {X : PSet.{u}} :
    ∀ k : Nat, Prec (zeros k) X → ∀ j, j < k → ¬ ofNat j ∈ X
  | 0, _, _, hj => (Nat.not_lt_zero _ hj).elim
  | k+1, ⟨hp, hb⟩, j, hj => by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | hj
    · exact not_mem_of_prec_zeros k hp j hj
    · subst hj
      exact fun hx => Bool.noConfusion (hb.2 (cast (congrArg (fun m => ofNat m ∈ X)
        (zeros_length j).symm) hx))

/-! ### First elements -/

/-- `n` is the first element of `X`. -/
def FirstOne (X n : PSet.{u}) : Prop := n ∈ omega ∧ n ∈ X ∧ ∀ m, m ∈ n → ¬ m ∈ X

theorem firstOne_unique {X n n' : PSet.{u}} (h : FirstOne X n) (h' : FirstOne X n') : n ≈ n' :=
  Stable.of_nn ((isOrd_omega.mem h.1).trichotomy (isOrd_omega.mem h'.1)) fun
    | .inl hlt => (h'.2.2 n hlt h.2.1).elim
    | .inr (.inl e) => e
    | .inr (.inr hlt) => (h.2.2 n' hlt h'.2.1).elim

theorem firstOne_of_ofNat_mem {X : PSet.{u}} : ∀ k : Nat, ofNat.{u} k ∈ X → ¬¬∃ n, FirstOne X n := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    refine Stable.by_cases (∃ j, j < k ∧ ofNat j ∈ X) (fun ⟨j, hj, hjX⟩ => ih j hj hjX) fun hno => ?_
    refine nn_intro ⟨ofNat k, ofNat_mem_omega k, hk, fun m hm hmX => ?_⟩
    exact Stable.of_nn (mem_ofNat.1 hm) fun ⟨j, hj, e⟩ => hno ⟨j, hj, (mem_congr_left e).1 hmX⟩

theorem prec_of_firstOne {X : PSet.{u}} {k : Nat} (h : FirstOne X (ofNat k)) :
    Prec (true :: zeros k) X :=
  ⟨prec_zeros k fun j hj hx => h.2.2 _ (mem_ofNat.2 (nn_intro ⟨j, hj, Equiv.refl _⟩)) hx,
   ⟨fun _ => cast (congrArg (fun m => ofNat m ∈ X) (zeros_length k).symm) h.2.1, fun _ => rfl⟩⟩

theorem firstOne_of_prec {X : PSet.{u}} {k : Nat} (h : Prec (true :: zeros k) X) :
    FirstOne X (ofNat k) :=
  ⟨ofNat_mem_omega k, cast (congrArg (fun m => ofNat m ∈ X) (zeros_length k)) (h.2.1 rfl),
   fun m hm hmX => Stable.of_nn (mem_ofNat.1 hm) fun ⟨j, hj, e⟩ =>
      not_mem_of_prec_zeros k h.1 j hj ((mem_congr_left e).1 hmX)⟩

theorem singleton_ofNat_mem_powerset (k : Nat) : singleton (ofNat.{u} k) ∈ powerset omega :=
  mem_powerset.2 fun _ hz => (mem_congr_left (mem_singleton.1 hz)).2 (ofNat_mem_omega k)

/-- Every nonempty negative subset of `ω` has, negatively, a first element. -/
theorem exists_firstOne {X : PSet.{u}} (hX : X ∈ powerset omega.{u}) (h : ¬¬∃ n, n ∈ X) :
    ¬¬∃ n, FirstOne X n :=
  Stable.of_nn h fun ⟨n, hn⟩ => Stable.of_nn (mem_omega.1 (mem_powerset.1 hX n hn)) fun ⟨k, e⟩ =>
    firstOne_of_ofNat_mem k ((mem_congr_left e).1 hn)

/-! ### The totalization and the lift -/

section
variable (Φ : PSet.{u} → PSet.{u} → Prop)

/-- Empty if there is no output, the singleton of the output otherwise. -/
def Tot (n z : PSet.{u}) : Prop :=
  ¬¬((¬(¬¬∃ y, Φ n y) ∧ z ≈ empty) ∨ ∃ y, Φ n y ∧ z ≈ singleton y)

instance {n z : PSet.{u}} : Stable (Tot Φ n z) := inferInstanceAs (Stable (¬_))

/-- The lift to the Cantor space: empty at the zero real, `Tot Φ` at the first `1` otherwise. -/
def Lift (X z : PSet.{u}) : Prop :=
  ¬¬((X ≈ empty ∧ z ≈ empty) ∨ ∃ n, FirstOne X n ∧ Tot Φ n z)

variable (hΦr : ∀ {n n' y}, n ≈ n' → Φ n y → Φ n' y)
  (hΦf : ∀ n y y', n ∈ omega.{u} → Φ n y → Φ n y' → y ≈ y')
include hΦr

theorem Tot.resp {n n' z : PSet.{u}} (e : n ≈ n') (h : Tot Φ n z) : Tot Φ n' z :=
  nn_map (Or.imp (fun ⟨h1, h2⟩ => ⟨fun h => h1 (nn_map (fun ⟨y, hy⟩ => ⟨y, hΦr e.symm hy⟩) h),
    h2⟩) fun ⟨y, hy, hz⟩ => ⟨y, hΦr e hy, hz⟩) h

omit hΦr in
theorem tot_total (n : PSet.{u}) : ¬¬∃ z, Tot Φ n z :=
  Stable.by_cases (∃ y, Φ n y) (fun ⟨y, hy⟩ => nn_intro ⟨singleton y, nn_intro (.inr ⟨y, hy, Equiv.refl _⟩)⟩)
    fun hn => nn_intro ⟨empty, nn_intro (.inl ⟨fun h => h hn, Equiv.refl _⟩)⟩

include hΦf in
omit hΦr in
theorem tot_func {n z z' : PSet.{u}} (hn : n ∈ omega.{u}) (h : Tot Φ n z) (h' : Tot Φ n z') :
    z ≈ z' := by
  refine Stable.of_nn h fun h => Stable.of_nn h' fun h' => ?_
  rcases h with ⟨h1, h2⟩ | ⟨y, hy, hz⟩ <;> rcases h' with ⟨h1', h2'⟩ | ⟨y', hy', hz'⟩
  · exact h2.trans h2'.symm
  · exact (h1 (nn_intro ⟨y', hy'⟩)).elim
  · exact (h1' (nn_intro ⟨y, hy⟩)).elim
  · exact hz.trans ((singleton_congr (hΦf n y y' hn hy hy')).trans hz'.symm)

omit hΦr in
theorem lift_total {X : PSet.{u}} (hX : X ∈ powerset omega.{u}) : ¬¬∃ z, Lift Φ X z := by
  refine Stable.by_cases (¬¬∃ n, n ∈ X) (fun h => ?_) fun h => ?_
  · refine Stable.of_nn (exists_firstOne hX h) fun ⟨n, hn⟩ => ?_
    exact nn_map (fun ⟨z, hz⟩ => ⟨z, nn_intro (.inr ⟨n, hn, hz⟩)⟩) (tot_total Φ n)
  · refine nn_intro ⟨empty, nn_intro (.inl ⟨ext fun z => ⟨fun hz => (h (nn_intro ⟨z, hz⟩)).elim,
      fun hz => (not_mem_empty z hz).elim⟩, Equiv.refl _⟩)⟩

include hΦf in
theorem lift_func {X z z' : PSet.{u}} (h : Lift Φ X z) (h' : Lift Φ X z') : z ≈ z' := by
  refine Stable.of_nn h fun h => Stable.of_nn h' fun h' => ?_
  rcases h with ⟨e, hz⟩ | ⟨n, hn, hz⟩ <;> rcases h' with ⟨e', hz'⟩ | ⟨n', hn', hz'⟩
  · exact hz.trans hz'.symm
  · exact (not_mem_empty _ ((mem_congr_right e).1 hn'.2.1)).elim
  · exact (not_mem_empty _ ((mem_congr_right e').1 hn.2.1)).elim
  · exact tot_func Φ hΦf hn.1 hz (hz'.resp Φ hΦr (firstOne_unique hn' hn))

/-! ### Caps -/

/-- A cap for `Φ`: all outputs at points of `ω` have rank below `κ`. -/
def HasCap : Prop := ¬¬∃ κ, IsOrd κ ∧ ∀ n y, n ∈ omega.{u} → Φ n y → rank y ∈ κ

instance : Stable (HasCap Φ) := inferInstanceAs (Stable (¬_))

omit hΦr in
theorem rank_tot_mem {κ n z : PSet.{u}} (hκ : IsOrd κ)
    (hb : ∀ y, Φ n y → rank y ∈ κ) (h : Tot Φ n z) : rank z ∈ succ κ := by
  refine Stable.of_nn h fun
    | .inl ⟨_, e⟩ => ?_
    | .inr ⟨y, hy, e⟩ => ?_
  · exact (mem_congr_left (rank_congr e)).2 ((isOrd_rank empty).mem_succ_of_subset hκ
      fun z hz => (not_mem_empty z ((mem_congr_right isOrd_empty.rank_equiv).1 hz)).elim)
  · exact (mem_congr_left (rank_congr e)).2 (rank_singleton_mem hκ (hb y hy))

omit hΦr in
/-- Every nonzero point has a local cap: at the cylinder fixing its first `1`, the lift is a
single-input specification, whose one output caps the cylinder. -/
theorem locCap_of_firstOne {X : PSet.{u}} (hX : X ∈ powerset omega.{u}) (h : ¬¬∃ n, n ∈ X) :
    ¬¬∃ s, Prec s X ∧ LocCap (Lift Φ) s := by
  refine Stable.of_nn (exists_firstOne hX h) fun ⟨n, hn⟩ => ?_
  refine Stable.of_nn (mem_omega.1 hn.1) fun ⟨k, e⟩ => ?_
  have hk : FirstOne X (ofNat k) := ⟨ofNat_mem_omega k, (mem_congr_left e).1 hn.2.1,
    fun m hm => hn.2.2 m ((mem_congr_right e).2 hm)⟩
  refine nn_intro ⟨_, prec_of_firstOne hk, ?_⟩
  refine Stable.of_nn (tot_total Φ (ofNat k)) fun ⟨z, hz⟩ => ?_
  refine nn_intro ⟨succ (rank z), (isOrd_rank z).succ, fun Z _ hp _ => ?_⟩
  exact nn_intro ⟨z, nn_intro (.inr ⟨ofNat k, firstOne_of_prec hp, hz⟩), self_mem_succ _⟩

include hΦf

omit hΦr in
/-- The outputs at the first `N` inputs are bounded: finitely many negative witnesses combine. -/
theorem head_bound : ∀ N : Nat, ¬¬∃ κ, IsOrd κ ∧ ∀ k, k < N → ∀ y, Φ (ofNat k) y → rank y ∈ κ
  | 0 => nn_intro ⟨empty, isOrd_empty, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | N+1 => by
    refine nn_bind (head_bound N) fun ⟨κ, hκ, hb⟩ => ?_
    refine Stable.of_nn (tot_total Φ (ofNat N)) fun ⟨z, hz⟩ => ?_
    refine nn_intro ⟨union κ (rank z), isOrd_union hκ (isOrd_rank z), fun k hk y hy => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
    · exact mem_union.2 (nn_intro (.inl (hb k hk y hy)))
    · have e := tot_func Φ hΦf (ofNat_mem_omega k) (nn_intro (.inr ⟨y, hy, Equiv.refl _⟩)) hz
      exact mem_union.2 (nn_intro (.inr ((mem_congr_right (rank_congr e)).1
        (rank_mem (self_mem_singleton y)))))

/-- A local cap at the zero real bounds the tail, and the finitely many earlier inputs are
bounded separately. -/
theorem hasCap_of_locCap_zero (hz : ¬¬∃ s, Prec s empty.{u} ∧ LocCap (Lift Φ) s) : HasCap Φ := by
  refine Stable.of_nn hz fun ⟨s, hs, hloc⟩ => Stable.of_nn hloc fun ⟨κ, hκ, hc⟩ => ?_
  refine nn_bind (head_bound Φ hΦf s.length) fun ⟨κ', hκ', hb⟩ => ?_
  refine nn_intro ⟨union κ κ', isOrd_union hκ hκ', fun n y hn hy => ?_⟩
  refine Stable.of_nn (mem_omega.1 hn) fun ⟨k, e⟩ => ?_
  have hy' : Φ (ofNat k) y := hΦr e hy
  rcases Nat.lt_or_ge k s.length with hk | hk
  · exact mem_union.2 (nn_intro (.inr (hb k hk y hy')))
  · -- the singleton real `{k}` lies in the cylinder of `s`
    have hX := singleton_ofNat_mem_powerset.{u} k
    have hp : Prec s (singleton (ofNat k)) := prec_of_agree s (fun j hj =>
      ⟨fun h => (not_mem_empty _ h).elim, fun h => (Nat.ne_of_lt (Nat.lt_of_lt_of_le hj hk)
        (ofNat_inj (mem_singleton.1 h))).elim⟩) hs
    refine Stable.of_nn (hc _ hX hp (lift_total Φ hX)) fun ⟨z, hz, hr⟩ => ?_
    refine Stable.of_nn hz fun
      | .inl ⟨e', _⟩ => (not_mem_empty _ ((mem_congr_right e').1 (self_mem_singleton _))).elim
      | .inr ⟨n', hn', ht⟩ => ?_
    have en : n' ≈ ofNat k := mem_singleton.1 hn'.2.1
    have e2 := tot_func Φ hΦf (ofNat_mem_omega k) (nn_intro (.inr ⟨y, hy', Equiv.refl _⟩))
      (ht.resp Φ hΦr en)
    have hyz : rank y ∈ rank z :=
      (mem_congr_right (rank_congr e2)).1 (rank_mem (self_mem_singleton y))
    exact mem_union.2 (nn_intro (.inl (hκ.trans _ hr _ hyz)))

omit hΦr hΦf in
theorem cap_lift_of_hasCap (h : HasCap Φ) : ¬¬∃ κ, IsOrd κ ∧ CapAt (Lift Φ) κ [] := by
  refine nn_map (fun ⟨κ, hκ, hb⟩ => ⟨succ (succ κ), hκ.succ.succ, fun X hX _ _ => ?_⟩) h
  refine nn_map (fun ⟨z, hz⟩ => ⟨z, hz, ?_⟩) (lift_total Φ hX)
  refine Stable.of_nn hz fun
    | .inl ⟨_, e⟩ => ?_
    | .inr ⟨n, hn, ht⟩ => ?_
  · exact (mem_congr_left (rank_congr e)).2 ((isOrd_rank empty).mem_succ_of_subset hκ.succ
      fun z hz => (not_mem_empty z ((mem_congr_right isOrd_empty.rank_equiv).1 hz)).elim)
  · exact mem_succ_of_mem (rank_tot_mem Φ hκ (fun y hy => hb n y hn.1 hy) ht)

/-- **The reduction.** -/
theorem countable_reduction :
    (HasCap Φ ↔ ¬¬∃ s, Prec s empty.{u} ∧ LocCap (Lift Φ) s) ∧
    (HasCap Φ ↔ ¬¬∃ κ, IsOrd κ ∧ CapAt (Lift Φ) κ []) :=
  ⟨⟨fun h => nn_map (fun ⟨κ, hκ, hc⟩ => ⟨[], trivial, nn_intro ⟨κ, hκ, hc⟩⟩)
      (cap_lift_of_hasCap Φ h), hasCap_of_locCap_zero Φ hΦr hΦf⟩,
   ⟨cap_lift_of_hasCap Φ, fun h => hasCap_of_locCap_zero Φ hΦr hΦf
      (nn_map (fun ⟨κ, hκ, hc⟩ => ⟨[], trivial, nn_intro ⟨κ, hκ, hc⟩⟩) h)⟩⟩

/-- info: 'PSet.countable_reduction' does not depend on any axioms -/
#guard_msgs in #print axioms countable_reduction
/-- info: 'PSet.locCap_of_firstOne' does not depend on any axioms -/
#guard_msgs in #print axioms locCap_of_firstOne

end

end PSet
