import ConZF.CofinalCut
/-!
Witness envelopes. For a stable, extensional predicate `P` on sets (the witnesses of a first-order
existential problem), the canonical functional output is the set of all witnesses of least rank,
or the empty set if there are none (`Env P W`). It exists negatively and is functional, with no
witness selected (`env_exists`, `env_func`), and it stays in `HG` when the witnesses do
(`env_hg`). For a functional `P` the envelope is a singleton (`env_singleton`), so bounds on
envelopes bound the original outputs.

At every ordinal cap `κ` there is an unconditional native approximation: `capRank P κ` is the
initial segment of `κ` below every capped witness rank (one Separation), and `capWit P κ` the
capped witnesses of that rank. The approximation is empty while no witness fits in the cap
(`capWit_of_empty`) and is the entire least-rank witness set as soon as one does
(`mem_capWit_iff`, `capRank_attained`). The exact criterion (`env_capWit_iff`): the capped
approximation is the envelope precisely when the cap meets the witness class whenever that class
is nonempty. Finally `rankBounded_of_cap`: a source-wide cap meeting each nonempty functional
witness class gives `RankBounded`, the hypothesis consumed by the model.
-/
universe u

namespace PSet
open Fml

section
variable (P : PSet.{u} → Prop)

/-! ### Capped witnesses -/

/-- The witnesses inside the cap. -/
def Capped (κ y : PSet.{u}) : Prop := P y ∧ y ∈ Vl κ

/-- The initial segment of the cap below every capped witness rank. -/
def capRank (κ : PSet.{u}) : PSet.{u} := sep (fun α => ∀ y, Capped P κ y → α ∈ rank y) κ

theorem mem_capRank {κ α : PSet.{u}} :
    α ∈ capRank P κ ↔ α ∈ κ ∧ ∀ y, Capped P κ y → α ∈ rank y :=
  mem_sep fun _ _ e h y hy => (mem_congr_left e).1 (h y hy)

theorem isOrd_capRank {κ : PSet.{u}} (hκ : IsOrd κ) : IsOrd (capRank P κ) := by
  refine ⟨fun β hβ γ hγ => ?_, fun β hβ => hκ.mem_trans β (mem_capRank P |>.1 hβ).1⟩
  have h := (mem_capRank P).1 hβ
  exact (mem_capRank P).2 ⟨hκ.trans β h.1 γ hγ, fun y hy => (isOrd_rank y).trans β (h.2 y hy) γ hγ⟩

/-- The cap rank is below the rank of every witness, capped or not. -/
theorem capRank_subset {κ : PSet.{u}} (hκ : IsOrd κ) {y : PSet.{u}} (hy : P y) :
    ∀ α, α ∈ capRank P κ → α ∈ rank y := by
  intro α hα
  have h := (mem_capRank P).1 hα
  refine Stable.of_nn ((isOrd_rank y).trichotomy hκ) fun
    | .inl h' => h.2 y ⟨hy, (mem_Vl_ord hκ).2 h'⟩
    | .inr (.inl e) => (mem_congr_right e).2 h.1
    | .inr (.inr h') => (isOrd_rank y).trans κ h' α h.1

/-- **Attainment.** If some witness fits in the cap, the cap rank is the rank of a capped
witness: otherwise it would belong to itself. -/
theorem capRank_attained {κ : PSet.{u}} (hκ : IsOrd κ) (h : ¬¬∃ y, Capped P κ y) :
    ¬¬∃ y, Capped P κ y ∧ rank y ≈ capRank P κ := by
  intro hn
  refine h fun ⟨y0, hy0⟩ => ?_
  have hmem : ∀ y, Capped P κ y → capRank P κ ∈ rank y := fun y hy =>
    Stable.of_nn ((isOrd_capRank P hκ).subset (isOrd_rank y) (capRank_subset P hκ hy.1)) fun
      | .inl h => h
      | .inr e => (hn ⟨y, hy, e.symm⟩).elim
  exact not_mem_self _ ((mem_capRank P).2
    ⟨hκ.trans _ ((mem_Vl_ord hκ).1 hy0.2) _ (hmem y0 hy0), hmem⟩)

theorem capRank_mem {κ : PSet.{u}} (hκ : IsOrd κ) (h : ¬¬∃ y, Capped P κ y) : capRank P κ ∈ κ :=
  Stable.of_nn (capRank_attained P hκ h) fun ⟨_, hy, e⟩ =>
    (mem_congr_left e).1 ((mem_Vl_ord hκ).1 hy.2)

/-- No witness fits: the cap rank is the cap. -/
theorem capRank_of_empty {κ : PSet.{u}} (h : ∀ y, ¬ Capped P κ y) : capRank P κ ≈ κ :=
  ext fun _ => (mem_capRank P).trans ⟨And.left, fun hα => ⟨hα, fun y hy => (h y hy).elim⟩⟩

variable [∀ y, Stable (P y)] (hP : ∀ {y y'}, P y → y ≈ y' → P y')
include hP

/-- The capped least-rank witness set. -/
def capWit (κ : PSet.{u}) : PSet.{u} := sep (fun y => P y ∧ rank y ≈ capRank P κ) (Vl κ)

theorem mem_capWit {κ y : PSet.{u}} :
    y ∈ capWit P κ ↔ y ∈ Vl κ ∧ P y ∧ rank y ≈ capRank P κ :=
  mem_sep fun _ _ e ⟨h1, h2⟩ => ⟨hP h1 e, (rank_congr e).symm.trans h2⟩

/-- No witness fits: the approximation is empty. -/
theorem capWit_of_empty {κ : PSet.{u}} (h : ∀ y, ¬ Capped P κ y) : ∀ y, ¬ y ∈ capWit P κ :=
  fun y hy => have h' := (mem_capWit P hP).1 hy; h y ⟨h'.2.1, h'.1⟩

/-- Some witness fits: the approximation is the entire least-rank witness set. -/
theorem mem_capWit_iff {κ : PSet.{u}} (hκ : IsOrd κ) (h : ¬¬∃ y, Capped P κ y) {y : PSet.{u}} :
    y ∈ capWit P κ ↔ P y ∧ rank y ≈ capRank P κ :=
  (mem_capWit P hP).trans ⟨And.right, fun ⟨hy, e⟩ =>
    ⟨(mem_Vl_ord hκ).2 ((mem_congr_left e).2 (capRank_mem P hκ h)), hy, e⟩⟩

/-! ### The envelope -/

/-- `ρ` is the least witness rank: attained, and below the rank of every witness. -/
def IsLeast (ρ : PSet.{u}) : Prop :=
  IsOrd ρ ∧ (¬¬∃ y, P y ∧ rank y ≈ ρ) ∧ ∀ y, P y → ∀ α, α ∈ ρ → α ∈ rank y

/-- The envelope: no witnesses and `W` empty, or `W` is the set of witnesses of least rank. A
negative disjunction; nothing is decided. -/
def Env (W : PSet.{u}) : Prop :=
  ¬¬(((∀ y, ¬ P y) ∧ ∀ z, ¬ z ∈ W) ∨ ∃ ρ, IsLeast P ρ ∧ ∀ y, y ∈ W ↔ P y ∧ rank y ≈ ρ)

omit hP [∀ y, Stable (P y)] in
instance {W : PSet.{u}} : Stable (Env P W) := inferInstanceAs (Stable (¬_))

omit hP [∀ y, Stable (P y)] in
theorem IsLeast.equiv {ρ ρ' : PSet.{u}} (h : IsLeast P ρ) (h' : IsLeast P ρ') : ρ ≈ ρ' := by
  have sub : ∀ {ρ ρ'}, IsLeast P ρ → IsLeast P ρ' → ∀ α, α ∈ ρ → α ∈ ρ' := fun h h' α hα =>
    Stable.of_nn h'.2.1 fun ⟨y, hy, e⟩ => (mem_congr_right e).1 (h.2.2 y hy α hα)
  exact ext fun α => ⟨sub h h' α, sub h' h α⟩

/-- **The exact criterion.** The capped approximation is the envelope precisely when the cap
meets the witness class whenever that class is nonempty. -/
theorem env_capWit_iff {κ : PSet.{u}} (hκ : IsOrd κ) :
    Env P (capWit P κ) ↔ ((¬¬∃ y, P y) → ¬¬∃ y, Capped P κ y) := by
  constructor
  · intro henv hex
    refine Stable.of_nn henv fun
      | .inl ⟨h1, _⟩ => Stable.of_nn hex fun ⟨y, hy⟩ => (h1 y hy).elim
      | .inr ⟨ρ, hρ, hW⟩ => nn_map (fun ⟨y, hy, e⟩ =>
          ⟨y, hy, ((mem_capWit P hP).1 ((hW y).2 ⟨hy, e⟩)).1⟩) hρ.2.1
  · intro hcrit
    refine Stable.by_cases (∃ y, P y) (fun hex => ?_) fun hn => ?_
    · refine Stable.of_nn (hcrit (nn_intro hex)) fun hc => nn_intro (.inr ⟨capRank P κ, ?_, ?_⟩)
      · exact ⟨isOrd_capRank P hκ, nn_map (fun ⟨y, hy, e⟩ => ⟨y, hy.1, e⟩)
          (capRank_attained P hκ (nn_intro hc)), fun y hy => capRank_subset P hκ hy⟩
      · exact fun y => mem_capWit_iff P hP hκ (nn_intro hc)
    · exact nn_intro (.inl ⟨fun y hy => hn ⟨y, hy⟩,
        fun z hz => hn ⟨z, ((mem_capWit P hP).1 hz).2.1⟩⟩)

/-- The envelope exists, negatively: cap at the successor of the rank of a witness. -/
theorem env_exists : ¬¬∃ W, Env P W := by
  refine Stable.by_cases (∃ y, P y) (fun ⟨y0, hy0⟩ => ?_) fun hn => ?_
  · refine nn_intro ⟨capWit P (succ (rank y0)), (env_capWit_iff P hP (isOrd_rank y0).succ).2 ?_⟩
    exact fun _ => nn_intro ⟨y0, hy0, (mem_Vl_ord (isOrd_rank y0).succ).2 (self_mem_succ _)⟩
  · exact nn_intro ⟨empty, nn_intro (.inl ⟨fun y hy => hn ⟨y, hy⟩, not_mem_empty⟩)⟩

omit hP [∀ y, Stable (P y)] in
/-- The envelope is functional. -/
theorem env_func {W W' : PSet.{u}} (h : Env P W) (h' : Env P W') : W ≈ W' := by
  refine Stable.of_nn h fun h => Stable.of_nn h' fun h' => ?_
  rcases h with ⟨h1, h2⟩ | ⟨ρ, hρ, hW⟩ <;> rcases h' with ⟨h1', h2'⟩ | ⟨ρ', hρ', hW'⟩
  · exact ext fun z => ⟨fun hz => (h2 z hz).elim, fun hz => (h2' z hz).elim⟩
  · exact Stable.of_nn hρ'.2.1 fun ⟨y, hy, _⟩ => (h1 y hy).elim
  · exact Stable.of_nn hρ.2.1 fun ⟨y, hy, _⟩ => (h1' y hy).elim
  · have e := hρ.equiv P hρ'
    exact ext fun y => (hW y).trans (Iff.trans (and_congr_right fun _ =>
      ⟨fun h => h.trans e, fun h => h.trans e.symm⟩) (hW' y).symm)

omit hP [∀ y, Stable (P y)] in
/-- The envelope of witnesses in `HG` is in `HG`. -/
theorem env_hg (hH : ∀ y, P y → HG y) {W : PSet.{u}} (h : Env P W) : HG W := by
  refine Stable.of_nn h fun
    | .inl ⟨_, h2⟩ => HG.of_bound cls_empty fun z hz => (h2 z hz).elim
    | .inr ⟨ρ, hρ, hW⟩ => ?_
  refine Stable.of_nn hρ.2.1 fun ⟨y1, hy1, e1⟩ => ?_
  have hc : Cls ISat ρ := Cls.resp e1 (hH y1 hy1)
  exact HG.of_bound hc.succ fun z hz => mem_succ_of_equiv ((hW z).1 hz).2

omit [∀ y, Stable (P y)] in
/-- For a functional predicate the envelope of a witness is its singleton. -/
theorem env_singleton (hfun : ∀ y y', P y → P y' → y ≈ y') {y : PSet.{u}} (hy : P y) :
    Env P (singleton y) :=
  nn_intro (.inr ⟨rank y, ⟨isOrd_rank y, nn_intro ⟨y, hy, Equiv.refl _⟩,
    fun y' hy' _ hα => (mem_congr_right (rank_congr (hfun y y' hy hy'))).1 hα⟩,
    fun z => mem_singleton.trans ⟨fun e => ⟨hP hy e.symm, rank_congr e⟩,
      fun ⟨hz, _⟩ => hfun z y hz hy⟩⟩)

end

/-! ### The adapter to the model -/

/-- A cap meeting each nonempty witness class of a functional instance bounds its output ranks. -/
theorem rankBounded_of_cap {ψ : Fml} {e : Nat → PSet.{u}} {a κ : PSet.{u}} (hκ : IsOrd κ)
    (hf : ∀ x y y', x ∈ a → HG y → HG y' → Sat HG ψ (Env.cons x (Env.cons y e)) →
      Sat HG ψ (Env.cons x (Env.cons y' e)) → y ≈ y')
    (hcap : ∀ x, x ∈ a → (¬¬∃ y, HG y ∧ Sat HG ψ (Env.cons x (Env.cons y e))) →
      ¬¬∃ y, HG y ∧ Sat HG ψ (Env.cons x (Env.cons y e)) ∧ y ∈ Vl κ) :
    RankBounded ψ e a :=
  nn_intro ⟨κ, hκ, fun x y hx hy hs =>
    Stable.of_nn (hcap x hx (nn_intro ⟨y, hy, hs⟩)) fun ⟨y', hy', hs', hV⟩ =>
      (mem_congr_left (rank_congr (hf x y' y hx hy' hy hs' hs))).1 ((mem_Vl_ord hκ).1 hV)⟩

/-- info: 'PSet.env_capWit_iff' does not depend on any axioms -/
#guard_msgs in #print axioms env_capWit_iff
/-- info: 'PSet.env_hg' does not depend on any axioms -/
#guard_msgs in #print axioms env_hg
/-- info: 'PSet.rankBounded_of_cap' does not depend on any axioms -/
#guard_msgs in #print axioms rankBounded_of_cap

end PSet
