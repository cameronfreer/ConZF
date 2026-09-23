import ConZF.OmegaRec
/-!
Finite assignments as sets (conzf15 gate 2, step A). An assignment into a domain set `A` is a
pure set-coded function from a numeral `n ∈ ω` into `A` (`IsAssign`, formula `assignF`). The
set of all assignments into `A` exists in a `SynZF` class (`assignSet_exists`): it is the
separation of the internal powerset of the internal product `ω × A` by `assignF`, and its
members are exactly the assignments in the class. The value of an assignment at a numeral is
read by pair membership; consing a new value shifts the domain by one (`IsCons`, formula
`consF`), and the cons of an assignment in the class exists in the class (`cons_exists`). The
decoding of an assignment into a native environment (`decode`) satisfies
`decode (cons x e) ≈ Env.cons x (decode e)` pointwise below the domain (`decode_cons`).
-/
universe u

namespace PSet
open Fml CardF RecF

/-- The ambient reading: a pure function from `n` into `A`. -/
def IsAssign (A e n : PSet.{u}) : Prop :=
  n ∈ omega ∧
  (∀ q, q ∈ e → ¬¬∃ i v, i ∈ n ∧ v ∈ A ∧ q ≈ pair i v) ∧
  (∀ i, i ∈ n → ¬¬∃ v, pair i v ∈ e) ∧
  (∀ i v v', pair i v ∈ e → pair i v' ∈ e → v ≈ v')

instance {A e n : PSet.{u}} : Stable (IsAssign A e n) := inferInstanceAs (Stable (_ ∧ _ ∧ _ ∧ _))

namespace AssignF

/-- `e` is an assignment into `A` with domain `n` (variables `e, n, A, ω`). -/
def assignF (e n A ω : Nat) : Fml :=
  and (mem n ω)
    (and (all (imp (mem 0 (e+1)) (ex (and (mem 0 (n+2)) (ex (and (mem 0 (A+3)) (pairF 2 1 0)))))))
      (and (all (imp (mem 0 (n+1)) (ex (pairMemF (e+2) 1 0))))
        (all (all (all (imp (pairMemF (e+3) 2 1) (imp (pairMemF (e+3) 2 0) (eq 1 0))))))))

/-- `e'` is the cons of `x` onto `e`: `⟨∅, x⟩ ∈ e'`, and `⟨i, v⟩ ∈ e ↔ ⟨succ i, v⟩ ∈ e'`, with
every member of `e'` of one of these forms (variables `e', x, e`). -/
def consF (e' x e : Nat) : Fml :=
  and (all (imp (emptyF 0) (pairMemF (e'+1) 0 (x+1))))
    (and (all (all (imp (pairMemF (e+2) 1 0) (all (imp (succF 0 2) (pairMemF (e'+3) 0 1))))))
      (and (all (all (all (imp (succF 1 2) (imp (pairMemF (e'+3) 1 0) (pairMemF (e+3) 2 0))))))
        (all (imp (mem 0 (e'+1)) (or (ex (and (emptyF 0) (pairF 1 0 (x+2))))
          (ex (ex (ex (and (succF 1 2) (and (pairMemF (e+4) 2 0) (pairF 3 1 0)))))))))))

end AssignF

open AssignF

/-- The ambient reading of `consF`. -/
def IsCons (e' x e : PSet.{u}) : Prop :=
  pair empty x ∈ e' ∧
  (∀ i v, pair i v ∈ e → pair (succ i) v ∈ e') ∧
  (∀ i v, pair (succ i) v ∈ e' → pair i v ∈ e) ∧
  (∀ q, q ∈ e' → ¬¬(q ≈ pair empty x ∨ ¬¬∃ i v, pair i v ∈ e ∧ q ≈ pair (succ i) v))

instance {e' x e : PSet.{u}} : Stable (IsCons e' x e) := inferInstanceAs (Stable (_ ∧ _ ∧ _ ∧ _))

theorem empty_mem_ofNat_succ : ∀ k : Nat, empty ∈ ofNat.{u} (k+1)
  | 0 => self_mem_succ _
  | k+1 => mem_succ_of_mem (empty_mem_ofNat_succ k)

theorem empty_mem_succ_of_mem_omega {n : PSet.{u}} (hn : n ∈ omega) : empty ∈ succ n :=
  Stable.of_nn (mem_omega.1 hn) fun ⟨m, em⟩ => by
    cases m with
    | zero => exact mem_succ_of_equiv em.symm
    | succ k => exact mem_succ_of_mem ((mem_congr_right em).2 (empty_mem_ofNat_succ k))

/-- The native environment read off an assignment (value at the numeral `i`, `∅` elsewhere).
It is a proposition-level reading: `decode e i ≈ v` for the unique value. -/
def Reads (e : PSet.{u}) (i : Nat) (v : PSet.{u}) : Prop := pair (ofNat i) v ∈ e

namespace TransClass
variable {M : PSet.{u} → Prop} (hN : TransClass M) {E : Nat → PSet.{u}} (hE : ∀ i, M (E i))
include hN hE

theorem sat_assignF (e n A ω : Nat) (hω : E ω ≈ omega) :
    Sat M (assignF e n A ω) E ↔ IsAssign (E A) (E e) (E n) := by
  refine sat_and.trans (and_congr (mem_congr_right hω) (sat_and.trans (and_congr ?_
    (sat_and.trans (and_congr (hN.sat_totalF hE e n) (hN.sat_funcF hE e))))))
  constructor
  · intro h q hq
    refine Stable.of_nn (sat_ex.1 (h q (hN.trans (hE e) hq) hq)) fun ⟨i, hi, hs⟩ => ?_
    have ⟨hin, hs⟩ := sat_and.1 hs
    refine Stable.of_nn (sat_ex.1 hs) fun ⟨v, hv, hs⟩ => ?_
    have ⟨hvA, hs⟩ := sat_and.1 hs
    exact nn_intro ⟨i, v, hin, hvA, (hN.sat_pairF (Env.cons_mem hv (Env.cons_mem hi
      (Env.cons_mem (hN.trans (hE e) hq) hE))) 2 1 0).1 hs⟩
  · intro h q hq hq'
    refine sat_ex.2 (nn_bind (h q hq') fun ⟨i, v, hin, hvA, e'⟩ => ?_)
    have ⟨hi, hv⟩ := hN.of_pair_mem (hE e) ((mem_congr_left e').1 hq')
    exact nn_intro ⟨i, hi, sat_and.2 ⟨hin, sat_ex.2 (nn_intro ⟨v, hv, sat_and.2 ⟨hvA,
      (hN.sat_pairF (Env.cons_mem hv (Env.cons_mem hi (Env.cons_mem hq hE))) 2 1 0).2 e'⟩⟩)⟩⟩

theorem sat_consF (e' x e : Nat) (hsucc : ∀ {y}, M y → M (succ y)) (h0 : M empty) :
    Sat M (consF e' x e) E ↔ IsCons (E e') (E x) (E e) := by
  refine sat_and.trans (and_congr ?_ (sat_and.trans (and_congr ?_ (sat_and.trans (and_congr ?_ ?_)))))
  · -- the head
    constructor
    · intro h
      exact (hN.sat_pairMemF (Env.cons_mem h0 hE) (e'+1) 0 (x+1)).1 (h empty h0 ((hN.sat_emptyF (Env.cons_mem h0 hE) 0).2 (Equiv.refl _)))
    · intro h z hz hz0
      have e0 := (hN.sat_emptyF (Env.cons_mem hz hE) 0).1 hz0
      exact (hN.sat_pairMemF (Env.cons_mem hz hE) (e'+1) 0 (x+1)).2 ((mem_congr_left (pair_congr e0.symm (Equiv.refl _))).1 h)
  · -- shifting up
    constructor
    · intro h i v hiv
      have ⟨hi, hv⟩ := hN.of_pair_mem (hE e) hiv
      have he2 := Env.cons_mem hv (Env.cons_mem hi hE)
      have he3 := Env.cons_mem (hsucc hi) he2
      exact (hN.sat_pairMemF he3 (e'+3) 0 1).1 (h i hi v hv ((hN.sat_pairMemF he2 (e+2) 1 0).2 hiv)
        (succ i) (hsucc hi) ((hN.sat_succF he3 0 2).2 (Equiv.refl _)))
    · intro h i hi v hv hiv s hs hsi
      have he2 := Env.cons_mem hv (Env.cons_mem hi hE)
      have he3 := Env.cons_mem hs he2
      have es := (hN.sat_succF he3 0 2).1 hsi
      exact (hN.sat_pairMemF he3 (e'+3) 0 1).2 ((mem_congr_left (pair_congr es.symm (Equiv.refl _))).1
        (h i v ((hN.sat_pairMemF he2 (e+2) 1 0).1 hiv)))
  · -- shifting down
    constructor
    · intro h i v hsv
      have ⟨hs, hv⟩ := hN.of_pair_mem (hE e') hsv
      have hi : M i := hN.trans hs (self_mem_succ i)
      have he3 := Env.cons_mem hv (Env.cons_mem hs (Env.cons_mem hi hE))
      exact (hN.sat_pairMemF he3 (e+3) 2 0).1 (h i hi (succ i) hs v hv ((hN.sat_succF he3 1 2).2 (Equiv.refl _))
        ((hN.sat_pairMemF he3 (e'+3) 1 0).2 hsv))
    · intro h i hi s hs v hv hsi hsv
      have he3 := Env.cons_mem hv (Env.cons_mem hs (Env.cons_mem hi hE))
      have es := (hN.sat_succF he3 1 2).1 hsi
      exact (hN.sat_pairMemF he3 (e+3) 2 0).2 (h i v ((mem_congr_left (pair_congr es (Equiv.refl _))).1
        ((hN.sat_pairMemF he3 (e'+3) 1 0).1 hsv)))
  · -- every member is of one of the two forms
    constructor
    · intro h q hq
      have hqM := hN.trans (hE e') hq
      have he1 := Env.cons_mem hqM hE
      refine nn_bind (sat_or.1 (h q hqM hq)) fun
        | .inl h1 => nn_map (fun ⟨z, hz, hs⟩ => ?_) (sat_ex.1 h1)
        | .inr h2 => nn_intro (.inr (nn_bind (sat_ex.1 h2) fun ⟨i, hi, hs⟩ => nn_bind (sat_ex.1 hs)
            fun ⟨s', hs', hs⟩ => nn_map (fun ⟨v, hv, hs⟩ => ?_) (sat_ex.1 hs)))
      · have ⟨h1, h2⟩ := sat_and.1 hs
        have he2 := Env.cons_mem hz he1
        have e0 := (hN.sat_emptyF he2 0).1 h1
        exact .inl (((hN.sat_pairF he2 1 0 (x+2)).1 h2).trans (pair_congr e0 (Equiv.refl _)))
      · have he4 := Env.cons_mem hv (Env.cons_mem hs' (Env.cons_mem hi he1))
        have ⟨h1, h2⟩ := sat_and.1 hs
        have ⟨h2, h3⟩ := sat_and.1 h2
        have es := (hN.sat_succF he4 1 2).1 h1
        exact ⟨i, v, (hN.sat_pairMemF he4 (e+4) 2 0).1 h2,
          ((hN.sat_pairF he4 3 1 0).1 h3).trans (pair_congr es (Equiv.refl _))⟩
    · intro h q hqM hq
      have he1 := Env.cons_mem hqM hE
      refine sat_or.2 (nn_bind (h q hq) fun
        | .inl e1 => nn_intro (.inl (sat_ex.2 (nn_intro ⟨empty, h0, sat_and.2
            ⟨(hN.sat_emptyF (Env.cons_mem h0 he1) 0).2 (Equiv.refl _),
             (hN.sat_pairF (Env.cons_mem h0 he1) 1 0 (x+2)).2 e1⟩⟩)))
        | .inr h2 => nn_map (fun ⟨i, v, hiv, e2⟩ => .inr ?_) h2)
      have ⟨hi, hv⟩ := hN.of_pair_mem (hE e) hiv
      have he4 := Env.cons_mem hv (Env.cons_mem (hsucc hi) (Env.cons_mem hi he1))
      exact sat_ex.2 (nn_intro ⟨i, hi, sat_ex.2 (nn_intro ⟨succ i, hsucc hi, sat_ex.2 (nn_intro ⟨v, hv,
        sat_and.2 ⟨(hN.sat_succF he4 1 2).2 (Equiv.refl _), sat_and.2 ⟨(hN.sat_pairMemF he4 (e+4) 2 0).2 hiv,
          (hN.sat_pairF he4 3 1 0).2 e2⟩⟩⟩)⟩)⟩)

end TransClass

/-! ### Reading values -/

theorem IsCons.reads_zero {e' x e v : PSet.{u}} (h : IsCons e' x e)
    (hf : ∀ i v v', pair i v ∈ e' → pair i v' ∈ e' → v ≈ v') : Reads e' 0 v ↔ v ≈ x :=
  ⟨fun hv => hf _ v x hv h.1, fun ev => (mem_congr_left (pair_congr (Equiv.refl _) ev.symm)).1 h.1⟩

theorem IsCons.reads_succ {e' x e v : PSet.{u}} (h : IsCons e' x e) (i : Nat) :
    Reads e' (i+1) v ↔ Reads e i v :=
  ⟨fun hv => h.2.2.1 _ v hv, fun hv => h.2.1 _ v hv⟩

/-! ### Existence in the class -/

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

/-- **The set of assignments into `A`.** Its members are exactly the assignments in the class. -/
theorem assignSet_exists {A : PSet.{u}} (hA : M A) :
    ¬¬∃ V, M V ∧ ∀ e, e ∈ V ↔ (M e ∧ ¬¬∃ n, IsAssign A e n) := by
  have hT := hM.toTransClass
  refine nn_bind (hM.prodM hM.omega hA) fun ⟨p, hp, hpm⟩ => nn_bind (hM.powM hp) fun ⟨P, hP, hPm⟩ => ?_
  let E : Nat → PSet.{u} := Env.cons P (Env.cons A (Env.cons PSet.omega envω))
  have hE : ∀ i, M (E i) := Env.cons_mem hP (Env.cons_mem hA (Env.cons_mem hM.omega hM.envω_mem))
  let ψ : Fml := ex (assignF 1 0 3 4)
  have key : ∀ e, M e → (Sat M ψ (Env.cons e E) ↔ ¬¬∃ n, IsAssign A e n) := fun e he =>
    sat_ex.trans ⟨fun h => nn_map (fun ⟨n, hn, hs⟩ =>
        ⟨n, (hT.sat_assignF (Env.cons_mem hn (Env.cons_mem he hE)) 1 0 3 4 (Equiv.refl _)).1 hs⟩) h,
      fun h => nn_map (fun ⟨n, hn⟩ => ⟨n, hM.trans hM.omega hn.1,
        (hT.sat_assignF (Env.cons_mem (hM.trans hM.omega hn.1) (Env.cons_mem he hE)) 1 0 3 4 (Equiv.refl _)).2 hn⟩) h⟩
  have hψ : ∀ e e' : PSet.{u}, e ≈ e' → Sat M ψ (Env.cons e E) → Sat M ψ (Env.cons e' E) := fun _ _ e h =>
    Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) h
  refine nn_intro ⟨_, hM.sepM ψ hE, fun e => (mem_sep hψ).trans ⟨fun ⟨heP, hs⟩ => ?_, fun ⟨he, h⟩ => ?_⟩⟩
  · have he := hM.trans hP heP
    exact ⟨he, (key e he).1 hs⟩
  · refine ⟨(hPm e he).2 fun q hq => ?_, (key e he).2 h⟩
    refine Stable.of_nn h fun ⟨n, hn⟩ => Stable.of_nn (hn.2.1 q hq) fun ⟨i, v, hi, hv, e'⟩ => ?_
    exact (hpm q).2 (nn_intro ⟨i, v, isOrd_omega.trans _ hn.1 i hi, hv, e'⟩)

/-- **Cons in the class.** The cons of a member onto an assignment in the class is an assignment
in the class on the successor domain. -/
theorem cons_exists {A e n x : PSet.{u}} (hA : M A) (he : M e) (hx : M x) (h : IsAssign A e n) (hxA : x ∈ A) :
    ¬¬∃ e', M e' ∧ IsCons e' x e ∧ IsAssign A e' (succ n) := by
  have hT := hM.toTransClass
  refine nn_map (fun ⟨p, hp, hpm⟩ => ?_) (hM.prodM hM.omega hA)
  -- the shifted copy of `e`, separated from the product
  let E : Nat → PSet.{u} := Env.cons p (Env.cons e envω)
  have hE : ∀ i, M (E i) := Env.cons_mem hp (Env.cons_mem he hM.envω_mem)
  let ψ : Fml := ex (ex (ex (and (succF 1 2) (and (pairMemF 5 2 0) (pairF 3 1 0)))))
  have key : ∀ q, M q → (Sat M ψ (Env.cons q E) ↔ ¬¬∃ i v, PSet.pair i v ∈ e ∧ q ≈ PSet.pair (succ i) v) := by
    intro q hq
    have he1 := Env.cons_mem hq hE
    refine sat_ex.trans ⟨fun h => nn_bind h fun ⟨i, hi, hs⟩ => nn_bind (sat_ex.1 hs) fun ⟨s', hs', hs⟩ =>
      nn_map (fun ⟨v, hv, hs⟩ => ?_) (sat_ex.1 hs), fun h => nn_bind h fun ⟨i, v, hiv, e2⟩ => ?_⟩
    · have he4 := Env.cons_mem hv (Env.cons_mem hs' (Env.cons_mem hi he1))
      have ⟨h1, h2⟩ := sat_and.1 hs
      have ⟨h2, h3⟩ := sat_and.1 h2
      exact ⟨i, v, (hT.sat_pairMemF he4 5 2 0).1 h2,
        ((hT.sat_pairF he4 3 1 0).1 h3).trans (pair_congr ((hT.sat_succF he4 1 2).1 h1) (Equiv.refl _))⟩
    · have ⟨hi, hv⟩ := hT.of_pair_mem he hiv
      have he4 := Env.cons_mem hv (Env.cons_mem (hM.succ_mem hi) (Env.cons_mem hi he1))
      exact nn_intro ⟨i, hi, sat_ex.2 (nn_intro ⟨succ i, hM.succ_mem hi, sat_ex.2 (nn_intro ⟨v, hv,
        sat_and.2 ⟨(hT.sat_succF he4 1 2).2 (Equiv.refl _), sat_and.2 ⟨(hT.sat_pairMemF he4 5 2 0).2 hiv,
          (hT.sat_pairF he4 3 1 0).2 e2⟩⟩⟩)⟩)⟩
  have hψ : ∀ q q' : PSet.{u}, q ≈ q' → Sat M ψ (Env.cons q E) → Sat M ψ (Env.cons q' E) := fun _ _ e h =>
    Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) h
  let sh := sep (fun q => Sat M ψ (Env.cons q E)) p
  have hsh : M sh := hM.sepM ψ hE
  have memsh : ∀ q, q ∈ sh ↔ ¬¬∃ i v, PSet.pair i v ∈ e ∧ q ≈ PSet.pair (succ i) v := by
    intro q
    refine (mem_sep hψ).trans ⟨fun ⟨hqp, hs⟩ => (key q (hM.trans hp hqp)).1 hs, fun hq => ?_⟩
    have hqM : M q := (hM.stable q).dne (nn_map (fun ⟨i, v, hiv, e2⟩ =>
      hM.resp e2.symm (hM.pair (hM.succ_mem (hT.of_pair_mem he hiv).1) (hT.of_pair_mem he hiv).2)) hq)
    refine ⟨(hpm q).2 (nn_bind hq fun ⟨i, v, hiv, e2⟩ => ?_), (key q hqM).2 hq⟩
    refine Stable.of_nn (h.2.1 _ hiv) fun ⟨i', v', hi', hv', e3⟩ => ?_
    have ⟨ei, ev⟩ := pair_inj e3
    exact nn_intro ⟨succ i, v, succ_mem_omega ((mem_congr_left ei).2 (isOrd_omega.trans _ h.1 _ hi')),
      (mem_congr_left ev).2 hv', e2⟩
  let e' := PSet.union (singleton (PSet.pair PSet.empty x)) sh
  have he' : M e' := hM.union (hM.single (hM.pair hM.empty hx)) hsh
  have meme' : ∀ q, q ∈ e' ↔ ¬¬(q ≈ PSet.pair PSet.empty x ∨ ¬¬∃ i v, PSet.pair i v ∈ e ∧ q ≈ PSet.pair (succ i) v) :=
    fun q => mem_union.trans (nn_congr (or_congr mem_singleton (memsh q)))
  have hcons : IsCons e' x e := by
    refine ⟨(meme' _).2 (nn_intro (.inl (Equiv.refl _))), fun i v hiv => (meme' _).2 (nn_intro (.inr (nn_intro ⟨i, v, hiv, Equiv.refl _⟩))),
      fun i v hsv => ?_, fun q hq => (meme' q).1 hq⟩
    refine Stable.of_nn ((meme' _).1 hsv) fun
      | .inl e1 => (not_mem_empty i ((mem_congr_right (pair_inj e1).1).1 (self_mem_succ i))).elim
      | .inr h2 => Stable.of_nn h2 fun ⟨i', v', hiv', e2⟩ => ?_
    have ⟨es, ev⟩ := pair_inj e2
    exact (mem_congr_left (pair_congr (succ_inj es).symm ev.symm)).1 hiv'
  have hno : IsOrd n := isOrd_omega.mem h.1
  refine ⟨e', he', hcons, succ_mem_omega h.1, fun q hq => ?_, fun i hi => ?_, fun i v v' h1 h2 => ?_⟩
  · -- pure pairs with first component in `succ n`
    refine nn_bind ((meme' q).1 hq) fun
      | .inl e1 => nn_intro ⟨PSet.empty, x, empty_mem_succ_of_mem_omega h.1, hxA, e1⟩
      | .inr h2 => nn_bind h2 fun ⟨i, v, hiv, e2⟩ => nn_bind (h.2.1 _ hiv) fun ⟨i', v', hi', hv', e3⟩ => ?_
    have ⟨ei, ev⟩ := pair_inj e3
    have hin : i ∈ n := (mem_congr_left ei).2 hi'
    refine nn_map (fun hs => ⟨succ i, v, hs, (mem_congr_left ev).2 hv', e2⟩) ?_
    exact nn_map (fun
      | .inl hs => mem_succ_of_mem hs
      | .inr es => mem_succ_of_equiv es) ((hno.mem hin).succ.subset hno fun z hz => Stable.of_nn (mem_succ.1 hz) fun
        | .inl hz => hno.trans i hin z hz
        | .inr ez => (mem_congr_left ez).2 hin)
  · -- total on `succ n`
    have hiω : i ∈ PSet.omega := isOrd_omega.trans _ (succ_mem_omega h.1) i hi
    refine Stable.of_nn (mem_omega.1 hiω) fun ⟨m, em⟩ => ?_
    cases m with
    | zero => exact nn_intro ⟨x, (meme' _).2 (nn_intro (.inl (pair_congr em (Equiv.refl _))))⟩
    | succ k =>
      have hk : ofNat k ∈ n := by
        have hk' : ofNat k ∈ i := (mem_congr_right em).2 (self_mem_succ _)
        exact Stable.of_nn (mem_succ.1 hi) fun
          | .inl hin => hno.trans i hin _ hk'
          | .inr ein => (mem_congr_right ein).1 hk'
      refine nn_map (fun ⟨v, hv⟩ => ⟨v, ?_⟩) (h.2.2.1 _ hk)
      exact (meme' _).2 (nn_intro (.inr (nn_intro ⟨ofNat k, v, hv, pair_congr em (Equiv.refl _)⟩)))
  · -- functional
    refine Stable.of_nn ((meme' _).1 h1) fun h1 => Stable.of_nn ((meme' _).1 h2) fun h2 => ?_
    rcases h1 with e1 | h1 <;> rcases h2 with e2 | h2
    · exact (pair_inj e1).2.trans (pair_inj e2).2.symm
    · refine Stable.of_nn h2 fun ⟨i₂, v₂, _, e2⟩ => ?_
      exact (not_mem_empty i₂ ((mem_congr_right ((pair_inj e1).1.symm.trans (pair_inj e2).1)).2 (self_mem_succ i₂))).elim
    · refine Stable.of_nn h1 fun ⟨i₁, v₁, _, e1⟩ => ?_
      exact (not_mem_empty i₁ ((mem_congr_right ((pair_inj e2).1.symm.trans (pair_inj e1).1)).2 (self_mem_succ i₁))).elim
    · refine Stable.of_nn h1 fun ⟨i₁, v₁, hiv₁, e1⟩ => Stable.of_nn h2 fun ⟨i₂, v₂, hiv₂, e2⟩ => ?_
      have ⟨ei1, ev1⟩ := pair_inj e1
      have ⟨ei2, ev2⟩ := pair_inj e2
      have ei : i₁ ≈ i₂ := succ_inj (ei1.symm.trans ei2)
      have hiv₂' : PSet.pair i₁ v₂ ∈ e := (mem_congr_left (pair_congr ei.symm (Equiv.refl _))).1 hiv₂
      exact ev1.trans ((h.2.2.2 i₁ v₁ v₂ hiv₁ hiv₂').trans ev2.symm)

end SynZF

/-- info: 'PSet.SynZF.cons_exists' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.cons_exists
/-- info: 'PSet.SynZF.assignSet_exists' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.assignSet_exists

end PSet
