import ConZF.ZF
/-!
The arithmetic endpoint of consistency (conzf20). Proofs in the Hilbert calculus are coded by
natural numbers through a native Cantor pairing (`pair`, `unpair`, with the inverse computed by a
bounded search), formulas by `encF` and proof trees by `encP`, both with fuelled decoders and exact
round trips. A recursive Boolean checker `checkZF` decodes a number, computes the conclusion of the
coded tree by a structural recursion with explicit schema-instance tags for Separation and
Replacement (`concl`), and tests whether it is `⊥`. The bridge `prf_fls_iff_code` states
`Prf ZF ⊥ ↔ ∃ n, checkZF n = true`: soundness by structural recursion on the code, completeness by
induction on the derivation, using only propositional existence of a code. Hence
`Con ZF ↔ ∀ n, checkZF n = false`, a `Π⁰₁` arithmetic sentence. Nothing here uses excluded middle,
propositional extensionality, or choice.
-/

namespace PSet
open Fml

namespace Code

/-! ### Cantor pairing without division -/

/-- Triangular numbers. -/
def tri : Nat → Nat
  | 0 => 0
  | n+1 => tri n + n + 1

/-- Cantor pairing. -/
def pair (a b : Nat) : Nat := tri (a + b) + b

/-- The next pair in the Cantor enumeration. -/
def nextPair : Nat → Nat → Nat × Nat
  | 0, b => (b+1, 0)
  | a+1, b => (a, b+1)

theorem pair_next (a b : Nat) : pair (nextPair a b).1 (nextPair a b).2 = pair a b + 1 := by
  cases a with
  | zero =>
    show tri (b + 1 + 0) + 0 = tri (0 + b) + b + 1
    rw [Nat.add_zero, Nat.add_zero, Nat.zero_add]
    rfl
  | succ a =>
    show tri (a + (b + 1)) + (b + 1) = tri (a + 1 + b) + b + 1
    rw [Nat.add_succ, Nat.succ_add]
    rfl

/-- Bounded search for the pair with a given code. -/
def findPair (n : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, a, b => (a, b)
  | k+1, a, b => if Nat.beq (pair a b) n then (a, b) else findPair n k (nextPair a b).1 (nextPair a b).2

theorem natBeq_self : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n+1 => natBeq_self n

theorem findPair_spec (n : Nat) : ∀ (k a b : Nat), n = pair a b + k →
    pair (findPair n k a b).1 (findPair n k a b).2 = n
  | 0, a, b, h => by
    show pair a b = n
    exact h.symm
  | k+1, a, b, h => by
    show pair (if Nat.beq (pair a b) n then (a, b) else findPair n k (nextPair a b).1 (nextPair a b).2).1
      (if Nat.beq (pair a b) n then (a, b) else findPair n k (nextPair a b).1 (nextPair a b).2).2 = n
    split
    · exact Nat.eq_of_beq_eq_true ‹_›
    · refine findPair_spec n k _ _ ?_
      rw [pair_next, h, Nat.add_succ, Nat.succ_add]

/-- The inverse of the pairing. -/
def unpair (n : Nat) : Nat × Nat := findPair n n 0 0

theorem pair_unpair (n : Nat) : pair (unpair n).1 (unpair n).2 = n :=
  findPair_spec n n 0 0 (Nat.zero_add n).symm

theorem tri_succ_le {s t : Nat} (h : s ≤ t) : tri s ≤ tri t := by
  induction t with
  | zero => cases s with
    | zero => exact Nat.le_refl _
    | succ s => exact absurd h (Nat.not_succ_le_zero s)
  | succ t ih =>
    rcases Nat.lt_or_ge s (t+1) with h' | h'
    · refine Nat.le_trans (ih (Nat.le_of_lt_succ h')) ?_
      show tri t ≤ tri t + t + 1
      exact Nat.le_succ_of_le (Nat.le_add_right _ _)
    · have : s = t + 1 := Nat.le_antisymm h h'
      rw [this]; exact Nat.le_refl _

theorem le_tri : ∀ s : Nat, s ≤ tri s
  | 0 => Nat.le_refl 0
  | s+1 => Nat.succ_le_succ (Nat.le_trans (le_tri s) (Nat.le_add_right _ _))

theorem add_left_cancel' : ∀ (n a b : Nat), n + a = n + b → a = b
  | 0, a, b, h => by rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | n+1, a, b, h => by
    rw [Nat.succ_add, Nat.succ_add] at h
    exact add_left_cancel' n a b (Nat.succ.inj h)

theorem pair_inj {a b a' b' : Nat} (h : pair a b = pair a' b') : a = a' ∧ b = b' := by
  have key : ∀ {a b a' b' : Nat}, pair a b = pair a' b' → ¬ a + b < a' + b' := by
    intro a b a' b' h hlt
    have h1 : pair a b < tri (a + b + 1) :=
      Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_left b a) _) (Nat.lt_succ_self _)
    have h2 : tri (a + b + 1) ≤ pair a' b' := Nat.le_trans (tri_succ_le (Nat.succ_le_of_lt hlt)) (Nat.le_add_right _ _)
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (h ▸ h1) h2)
  have hs : a + b = a' + b' := by
    rcases Nat.lt_or_ge (a + b) (a' + b') with h1 | h1
    · exact (key h h1).elim
    · rcases Nat.lt_or_ge (a' + b') (a + b) with h2 | h2
      · exact (key h.symm h2).elim
      · exact Nat.le_antisymm h2 h1
  have hb : b = b' := by
    have : tri (a + b) + b = tri (a + b) + b' := by
      show pair a b = tri (a + b) + b'
      rw [h]
      show tri (a' + b') + b' = tri (a + b) + b'
      rw [hs]
    exact add_left_cancel' _ _ _ this
  refine ⟨?_, hb⟩
  rw [hb] at hs
  rw [Nat.add_comm a b', Nat.add_comm a' b'] at hs
  exact add_left_cancel' _ _ _ hs

theorem unpair_pair (a b : Nat) : unpair (pair a b) = (a, b) := by
  have h := pair_inj (pair_unpair (pair a b))
  match unpair (pair a b), h with
  | (x, y), ⟨e1, e2⟩ =>
    have e1' : x = a := e1
    have e2' : y = b := e2
    rw [e1', e2']

theorem le_pair_right (a b : Nat) : b ≤ pair a b := Nat.le_add_left b _

theorem le_pair_left (a b : Nat) : a ≤ pair a b :=
  Nat.le_trans (Nat.le_trans (Nat.le_add_right a b) (le_tri _)) (Nat.le_add_right _ _)

/-- A payload is strictly below its tagged code when the tag is positive. -/
theorem lt_pair_succ (t r : Nat) : r < pair (t+1) r := by
  have h1 : tri (r + 1) ≤ tri (t + 1 + r) := tri_succ_le (by rw [Nat.succ_add]; exact Nat.succ_le_succ (Nat.le_add_left r t))
  have h2 : r < tri (r + 1) := by
    show r < tri r + r + 1
    exact Nat.lt_succ_of_le (Nat.le_add_left r (tri r))
  exact Nat.lt_of_lt_of_le h2 (Nat.le_trans h1 (Nat.le_add_right _ _))

/-- Bind on options, by non-overlapping patterns. -/
def obind {α β : Type} : Option α → (α → Option β) → Option β
  | none, _ => none
  | some a, f => f a

/-- Map on options, by non-overlapping patterns. -/
def omap {α β : Type} (f : α → β) : Option α → Option β
  | none => none
  | some a => some (f a)

/-! ### Formula codes -/

/-- Boolean equality of formulas, by exhaustive non-overlapping patterns. -/
def beqF : Fml → Fml → Bool
  | .mem i j, .mem i' j' => Nat.beq i i' && Nat.beq j j'
  | .mem _ _, .eq _ _ => false
  | .mem _ _, .fls => false
  | .mem _ _, .imp _ _ => false
  | .mem _ _, .all _ => false
  | .eq _ _, .mem _ _ => false
  | .eq i j, .eq i' j' => Nat.beq i i' && Nat.beq j j'
  | .eq _ _, .fls => false
  | .eq _ _, .imp _ _ => false
  | .eq _ _, .all _ => false
  | .fls, .mem _ _ => false
  | .fls, .eq _ _ => false
  | .fls, .fls => true
  | .fls, .imp _ _ => false
  | .fls, .all _ => false
  | .imp _ _, .mem _ _ => false
  | .imp _ _, .eq _ _ => false
  | .imp _ _, .fls => false
  | .imp a b, .imp a' b' => beqF a a' && beqF b b'
  | .imp _ _, .all _ => false
  | .all _, .mem _ _ => false
  | .all _, .eq _ _ => false
  | .all _, .fls => false
  | .all _, .imp _ _ => false
  | .all a, .all a' => beqF a a'

theorem and_eq_true {x y : Bool} (h : (x && y) = true) : x = true ∧ y = true := by
  cases x <;> cases y
  · exact nomatch h
  · exact nomatch h
  · exact nomatch h
  · exact ⟨rfl, rfl⟩

theorem beqF_self : ∀ φ : Fml, beqF φ φ = true
  | .mem i j => by show (Nat.beq i i && Nat.beq j j) = true; rw [natBeq_self, natBeq_self]; rfl
  | .eq i j => by show (Nat.beq i i && Nat.beq j j) = true; rw [natBeq_self, natBeq_self]; rfl
  | .fls => rfl
  | .imp a b => by show (beqF a a && beqF b b) = true; rw [beqF_self a, beqF_self b]; rfl
  | .all a => beqF_self a

theorem eq_of_beqF : ∀ a b : Fml, beqF a b = true → a = b
  | .mem i j, .mem i' j', h => by
    have ⟨h1, h2⟩ := and_eq_true h
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  | .eq i j, .eq i' j', h => by
    have ⟨h1, h2⟩ := and_eq_true h
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  | .fls, .fls, _ => rfl
  | .imp a b, .imp a' b', h => by
    have ⟨h1, h2⟩ := and_eq_true h
    rw [eq_of_beqF a a' h1, eq_of_beqF b b' h2]
  | .all a, .all a', h => by rw [eq_of_beqF a a' h]
  | .mem _ _, .eq _ _, h | .mem _ _, .fls, h | .mem _ _, .imp _ _, h | .mem _ _, .all _, h => nomatch h
  | .eq _ _, .mem _ _, h | .eq _ _, .fls, h | .eq _ _, .imp _ _, h | .eq _ _, .all _, h => nomatch h
  | .fls, .mem _ _, h | .fls, .eq _ _, h | .fls, .imp _ _, h | .fls, .all _, h => nomatch h
  | .imp _ _, .mem _ _, h | .imp _ _, .eq _ _, h | .imp _ _, .fls, h | .imp _ _, .all _, h => nomatch h
  | .all _, .mem _ _, h | .all _, .eq _ _, h | .all _, .fls, h | .all _, .imp _ _, h => nomatch h

/-- The code of a formula. -/
def encF : Fml → Nat
  | .mem i j => pair 0 (pair i j)
  | .eq i j => pair 1 (pair i j)
  | .fls => pair 2 0
  | .imp φ ψ => pair 3 (pair (encF φ) (encF ψ))
  | .all φ => pair 4 (encF φ)

/-- The decoder branches on the tag and payload, with fuel for subformulas. -/
def decFAux (dec : Nat → Option Fml) : Nat × Nat → Option Fml
  | (0, r) => some (.mem (unpair r).1 (unpair r).2)
  | (1, r) => some (.eq (unpair r).1 (unpair r).2)
  | (2, _) => some .fls
  | (3, r) => obind (dec (unpair r).1) fun φ => omap (Fml.imp φ) (dec (unpair r).2)
  | (4, r) => omap Fml.all (dec r)
  | (_+5, _) => none

/-- The fuelled decoder of formula codes. -/
def decF : Nat → Nat → Option Fml
  | 0, _ => none
  | f+1, n => decFAux (decF f) (unpair n)

theorem decF_encF : ∀ (φ : Fml) (f : Nat), encF φ < f → decF f (encF φ) = some φ
  | _, 0, h => (Nat.not_lt_zero _ h).elim
  | .mem i j, f+1, _ => by
    show decFAux (decF f) (unpair (pair 0 (pair i j))) = some (.mem i j)
    rw [unpair_pair]
    show some (Fml.mem (unpair (pair i j)).1 (unpair (pair i j)).2) = some (.mem i j)
    rw [unpair_pair]
  | .eq i j, f+1, _ => by
    show decFAux (decF f) (unpair (pair 1 (pair i j))) = some (.eq i j)
    rw [unpair_pair]
    show some (Fml.eq (unpair (pair i j)).1 (unpair (pair i j)).2) = some (.eq i j)
    rw [unpair_pair]
  | .fls, f+1, _ => by
    show decFAux (decF f) (unpair (pair 2 0)) = some .fls
    rw [unpair_pair]
    rfl
  | .imp φ ψ, f+1, h => by
    have h1 : encF φ < encF (.imp φ ψ) := Nat.lt_of_le_of_lt (le_pair_left (encF φ) (encF ψ)) (lt_pair_succ 2 (pair (encF φ) (encF ψ)))
    have h2 : encF ψ < encF (.imp φ ψ) := Nat.lt_of_le_of_lt (le_pair_right (encF φ) (encF ψ)) (lt_pair_succ 2 (pair (encF φ) (encF ψ)))
    have hφ : encF φ < f := Nat.lt_of_lt_of_le h1 (Nat.le_of_lt_succ h)
    have hψ : encF ψ < f := Nat.lt_of_lt_of_le h2 (Nat.le_of_lt_succ h)
    show decFAux (decF f) (unpair (pair 3 (pair (encF φ) (encF ψ)))) = some (.imp φ ψ)
    rw [unpair_pair]
    show obind (decF f (unpair (pair (encF φ) (encF ψ))).1) (fun χ => omap (Fml.imp χ) (decF f (unpair (pair (encF φ) (encF ψ))).2)) = some (.imp φ ψ)
    rw [unpair_pair]
    show obind (decF f (encF φ)) (fun χ => omap (Fml.imp χ) (decF f (encF ψ))) = some (.imp φ ψ)
    rw [decF_encF φ f hφ, decF_encF ψ f hψ]
    rfl
  | .all φ, f+1, h => by
    have h1 : encF φ < encF (.all φ) := lt_pair_succ 3 (encF φ)
    have hφ : encF φ < f := Nat.lt_of_lt_of_le h1 (Nat.le_of_lt_succ h)
    show decFAux (decF f) (unpair (pair 4 (encF φ))) = some (.all φ)
    rw [unpair_pair]
    show omap Fml.all (decF f (encF φ)) = some (.all φ)
    rw [decF_encF φ f hφ]
    rfl

/-- Decoding with the code as its own fuel. -/
def decF' (c : Nat) : Option Fml := decF (c+1) c

theorem decF'_encF (φ : Fml) : decF' (encF φ) = some φ := decF_encF φ _ (Nat.lt_succ_self _)

/-! ### Proof codes -/

/-- Proof trees with explicit payloads: axiom tags (`0`–`5` the closed axioms, `6` Separation and
`7` Replacement with their schema formula), the logical axioms with their formulas, and the rules. -/
inductive PC : Type
  | ax (t : Nat) (ψ : Fml)
  | k (φ ψ : Fml)
  | s (φ ψ χ : Fml)
  | dne (φ : Fml)
  | mp (p q : PC)
  | gen (p : PC)
  | inst (φ : Fml) (j : Nat)
  | dist (φ ψ : Fml)
  | refl (i : Nat)
  | eml (i j k : Nat)
  | emr (i j k : Nat)
  | eqq (i j k : Nat)

/-- The axiom of `ZF` with a tag and a schema formula. -/
def axiomOf : Nat → Fml → Option Fml
  | 0, _ => some ZFAx.ext
  | 1, _ => some ZFAx.found
  | 2, _ => some ZFAx.pair
  | 3, _ => some ZFAx.union
  | 4, _ => some ZFAx.power
  | 5, _ => some ZFAx.inf
  | 6, ψ => some (ZFAx.sep ψ)
  | 7, ψ => some (ZFAx.repl ψ)
  | _+8, _ => none

/-- Modus ponens on a conclusion and an optional premise. -/
def conclMp : Fml → Option Fml → Option Fml
  | .imp a b, o => obind o fun a' => if beqF a a' then some b else none
  | .mem _ _, _ => none
  | .eq _ _, _ => none
  | .fls, _ => none
  | .all _, _ => none

/-- **The conclusion of a proof tree**, by structural recursion. -/
def concl : PC → Option Fml
  | .ax t ψ => axiomOf t ψ
  | .k φ ψ => some (imp φ (imp ψ φ))
  | .s φ ψ χ => some (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  | .dne φ => some (imp (neg (neg φ)) φ)
  | .mp p q => obind (concl p) fun c => conclMp c (concl q)
  | .gen p => omap Fml.all (concl p)
  | .inst φ j => some (imp (all φ) (rename (Fml.inst j) φ))
  | .dist φ ψ => some (imp (all (imp (lift φ) ψ)) (imp φ (all ψ)))
  | .refl i => some (eq i i)
  | .eml i j k => some (imp (eq i j) (imp (mem i k) (mem j k)))
  | .emr i j k => some (imp (eq i j) (imp (mem k i) (mem k j)))
  | .eqq i j k => some (imp (eq i j) (imp (eq i k) (eq j k)))

theorem zf_of_axiomOf : ∀ (t : Nat) (ψ φ : Fml), axiomOf t ψ = some φ → ZF φ
  | 0, _, _, h => (Option.some.inj h) ▸ ZF.ext
  | 1, _, _, h => (Option.some.inj h) ▸ ZF.found
  | 2, _, _, h => (Option.some.inj h) ▸ ZF.pair
  | 3, _, _, h => (Option.some.inj h) ▸ ZF.union
  | 4, _, _, h => (Option.some.inj h) ▸ ZF.power
  | 5, _, _, h => (Option.some.inj h) ▸ ZF.inf
  | 6, ψ, _, h => (Option.some.inj h) ▸ ZF.sep ψ
  | 7, ψ, _, h => (Option.some.inj h) ▸ ZF.repl ψ
  | _+8, _, _, h => nomatch h

/-- **Soundness of the checker**: a coded conclusion is a theorem. -/
theorem prf_of_concl : ∀ (p : PC) (φ : Fml), concl p = some φ → Prf ZF φ
  | .ax t ψ, φ, h => Prf.ax (zf_of_axiomOf t ψ φ h)
  | .k _ _, _, h => (Option.some.inj h) ▸ Prf.k
  | .s _ _ _, _, h => (Option.some.inj h) ▸ Prf.s
  | .dne _, _, h => (Option.some.inj h) ▸ Prf.dne
  | .inst _ j, _, h => (Option.some.inj h) ▸ Prf.inst j
  | .dist _ _, _, h => (Option.some.inj h) ▸ Prf.dist
  | .refl i, _, h => (Option.some.inj h) ▸ Prf.refl i
  | .eml i j k, _, h => (Option.some.inj h) ▸ Prf.eq_mem_l i j k
  | .emr i j k, _, h => (Option.some.inj h) ▸ Prf.eq_mem_r i j k
  | .eqq i j k, _, h => (Option.some.inj h) ▸ Prf.eq_eq i j k
  | .gen p, φ, h => by
    have h' : omap Fml.all (concl p) = some φ := h
    cases hc : concl p with
    | none => rw [hc] at h'; exact nomatch h'
    | some ψ =>
      rw [hc] at h'
      exact (Option.some.inj h') ▸ Prf.gen (prf_of_concl p ψ hc)
  | .mp p q, φ, h => by
    have h' : obind (concl p) (fun c => conclMp c (concl q)) = some φ := h
    cases hp : concl p with
    | none => rw [hp] at h'; exact nomatch h'
    | some c =>
      rw [hp] at h'
      have h'' : conclMp c (concl q) = some φ := h'
      cases c with
      | imp a b =>
        have h3 : obind (concl q) (fun a' => if beqF a a' then some b else none) = some φ := h''
        cases hq : concl q with
        | none => rw [hq] at h3; exact nomatch h3
        | some a' =>
          rw [hq] at h3
          have h4 : (if beqF a a' then some b else none) = some φ := h3
          cases hb : beqF a a' with
          | false => rw [hb] at h4; exact nomatch h4
          | true =>
            rw [hb] at h4
            have e : b = φ := Option.some.inj h4
            have ea : a = a' := eq_of_beqF a a' hb
            exact e ▸ Prf.mp (prf_of_concl p _ hp) (ea ▸ prf_of_concl q _ hq)
      | mem _ _ => exact nomatch h''
      | eq _ _ => exact nomatch h''
      | fls => exact nomatch h''
      | all _ => exact nomatch h''

/-- **Completeness of the checker**: every theorem has a coded proof tree, propositionally. -/
theorem concl_of_prf {φ : Fml} (h : Prf ZF φ) : ∃ p : PC, concl p = some φ := by
  induction h with
  | ax h =>
    cases h with
    | ext => exact ⟨.ax 0 .fls, rfl⟩
    | found => exact ⟨.ax 1 .fls, rfl⟩
    | pair => exact ⟨.ax 2 .fls, rfl⟩
    | union => exact ⟨.ax 3 .fls, rfl⟩
    | power => exact ⟨.ax 4 .fls, rfl⟩
    | inf => exact ⟨.ax 5 .fls, rfl⟩
    | sep ψ => exact ⟨.ax 6 ψ, rfl⟩
    | repl ψ => exact ⟨.ax 7 ψ, rfl⟩
  | @k φ ψ => exact ⟨.k φ ψ, rfl⟩
  | @s φ ψ χ => exact ⟨.s φ ψ χ, rfl⟩
  | @dne φ => exact ⟨.dne φ, rfl⟩
  | @mp φ ψ _ _ ih1 ih2 =>
    obtain ⟨p, hp⟩ := ih1
    obtain ⟨q, hq⟩ := ih2
    refine ⟨.mp p q, ?_⟩
    show obind (concl p) (fun c => conclMp c (concl q)) = some ψ
    rw [hp, hq]
    show (if beqF φ φ then some ψ else none) = some ψ
    rw [beqF_self]
    rfl
  | @gen φ _ ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨.gen p, ?_⟩
    show omap Fml.all (concl p) = some (all φ)
    rw [hp]
    rfl
  | @inst φ j => exact ⟨.inst φ j, rfl⟩
  | @dist φ ψ => exact ⟨.dist φ ψ, rfl⟩
  | refl i => exact ⟨.refl i, rfl⟩
  | eq_mem_l i j k => exact ⟨.eml i j k, rfl⟩
  | eq_mem_r i j k => exact ⟨.emr i j k, rfl⟩
  | eq_eq i j k => exact ⟨.eqq i j k, rfl⟩

/-! ### Proof codes as numbers -/

/-- The code of a proof tree. -/
def encP : PC → Nat
  | .ax t ψ => pair 0 (pair t (encF ψ))
  | .k φ ψ => pair 1 (pair (encF φ) (encF ψ))
  | .s φ ψ χ => pair 2 (pair (encF φ) (pair (encF ψ) (encF χ)))
  | .dne φ => pair 3 (encF φ)
  | .mp p q => pair 4 (pair (encP p) (encP q))
  | .gen p => pair 5 (encP p)
  | .inst φ j => pair 6 (pair (encF φ) j)
  | .dist φ ψ => pair 7 (pair (encF φ) (encF ψ))
  | .refl i => pair 8 i
  | .eml i j k => pair 9 (pair i (pair j k))
  | .emr i j k => pair 10 (pair i (pair j k))
  | .eqq i j k => pair 11 (pair i (pair j k))

/-- One formula from a code. -/
def dF1 (r : Nat) (g : Fml → PC) : Option PC := omap g (decF' r)

/-- Two formulas from a paired code. -/
def dF2 (r : Nat) (g : Fml → Fml → PC) : Option PC :=
  obind (decF' (unpair r).1) fun φ => omap (g φ) (decF' (unpair r).2)

/-- The decoder branches, on the tag and payload, with fuel for subproofs. -/
def decPAux (dec : Nat → Option PC) : Nat × Nat → Option PC
  | (0, r) => dF1 (unpair r).2 fun ψ => .ax (unpair r).1 ψ
  | (1, r) => dF2 r .k
  | (2, r) => obind (decF' (unpair r).1) fun φ => dF2 (unpair r).2 (PC.s φ)
  | (3, r) => dF1 r .dne
  | (4, r) => obind (dec (unpair r).1) fun p => omap (PC.mp p) (dec (unpair r).2)
  | (5, r) => omap PC.gen (dec r)
  | (6, r) => dF1 (unpair r).1 fun φ => .inst φ (unpair r).2
  | (7, r) => dF2 r .dist
  | (8, r) => some (.refl r)
  | (9, r) => some (.eml (unpair r).1 (unpair (unpair r).2).1 (unpair (unpair r).2).2)
  | (10, r) => some (.emr (unpair r).1 (unpair (unpair r).2).1 (unpair (unpair r).2).2)
  | (11, r) => some (.eqq (unpair r).1 (unpair (unpair r).2).1 (unpair (unpair r).2).2)
  | (_+12, _) => none

/-- The fuelled decoder of proof codes. -/
def decP : Nat → Nat → Option PC
  | 0, _ => none
  | f+1, n => decPAux (decP f) (unpair n)

theorem dF1_encF (φ : Fml) (g : Fml → PC) : dF1 (encF φ) g = some (g φ) := by
  show omap g (decF' (encF φ)) = some (g φ)
  rw [decF'_encF]
  rfl

theorem dF2_encF (φ ψ : Fml) (g : Fml → Fml → PC) : dF2 (pair (encF φ) (encF ψ)) g = some (g φ ψ) := by
  show obind (decF' (unpair (pair (encF φ) (encF ψ))).1) (fun χ => omap (g χ) (decF' (unpair (pair (encF φ) (encF ψ))).2)) = some (g φ ψ)
  rw [unpair_pair]
  show obind (decF' (encF φ)) (fun χ => omap (g χ) (decF' (encF ψ))) = some (g φ ψ)
  rw [decF'_encF, decF'_encF]
  rfl

theorem decP_encP : ∀ (p : PC) (f : Nat), encP p < f → decP f (encP p) = some p
  | _, 0, h => (Nat.not_lt_zero _ h).elim
  | .ax t ψ, f+1, _ => by
    show decPAux (decP f) (unpair (pair 0 (pair t (encF ψ)))) = some (.ax t ψ)
    rw [unpair_pair]
    show dF1 (unpair (pair t (encF ψ))).2 (fun χ => .ax (unpair (pair t (encF ψ))).1 χ) = some (.ax t ψ)
    rw [unpair_pair]
    exact dF1_encF ψ _
  | .k φ ψ, f+1, _ => by
    show decPAux (decP f) (unpair (pair 1 (pair (encF φ) (encF ψ)))) = some (.k φ ψ)
    rw [unpair_pair]
    exact dF2_encF φ ψ _
  | .s φ ψ χ, f+1, _ => by
    show decPAux (decP f) (unpair (pair 2 (pair (encF φ) (pair (encF ψ) (encF χ))))) = some (.s φ ψ χ)
    rw [unpair_pair]
    show obind (decF' (unpair (pair (encF φ) (pair (encF ψ) (encF χ)))).1)
      (fun θ => dF2 (unpair (pair (encF φ) (pair (encF ψ) (encF χ)))).2 (PC.s θ)) = some (.s φ ψ χ)
    rw [unpair_pair]
    show obind (decF' (encF φ)) (fun θ => dF2 (pair (encF ψ) (encF χ)) (PC.s θ)) = some (.s φ ψ χ)
    rw [decF'_encF]
    exact dF2_encF ψ χ _
  | .dne φ, f+1, _ => by
    show decPAux (decP f) (unpair (pair 3 (encF φ))) = some (.dne φ)
    rw [unpair_pair]
    exact dF1_encF φ _
  | .mp p q, f+1, h => by
    have h1 : encP p < encP (.mp p q) := Nat.lt_of_le_of_lt (le_pair_left (encP p) (encP q)) (lt_pair_succ 3 (pair (encP p) (encP q)))
    have h2 : encP q < encP (.mp p q) := Nat.lt_of_le_of_lt (le_pair_right (encP p) (encP q)) (lt_pair_succ 3 (pair (encP p) (encP q)))
    have hp : encP p < f := Nat.lt_of_lt_of_le h1 (Nat.le_of_lt_succ h)
    have hq : encP q < f := Nat.lt_of_lt_of_le h2 (Nat.le_of_lt_succ h)
    show decPAux (decP f) (unpair (pair 4 (pair (encP p) (encP q)))) = some (.mp p q)
    rw [unpair_pair]
    show obind (decP f (unpair (pair (encP p) (encP q))).1) (fun r => omap (PC.mp r) (decP f (unpair (pair (encP p) (encP q))).2)) = some (.mp p q)
    rw [unpair_pair]
    show obind (decP f (encP p)) (fun r => omap (PC.mp r) (decP f (encP q))) = some (.mp p q)
    rw [decP_encP p f hp, decP_encP q f hq]
    rfl
  | .gen p, f+1, h => by
    have h1 : encP p < encP (.gen p) := lt_pair_succ 4 (encP p)
    have hp : encP p < f := Nat.lt_of_lt_of_le h1 (Nat.le_of_lt_succ h)
    show decPAux (decP f) (unpair (pair 5 (encP p))) = some (.gen p)
    rw [unpair_pair]
    show omap PC.gen (decP f (encP p)) = some (.gen p)
    rw [decP_encP p f hp]
    rfl
  | .inst φ j, f+1, _ => by
    show decPAux (decP f) (unpair (pair 6 (pair (encF φ) j))) = some (.inst φ j)
    rw [unpair_pair]
    show dF1 (unpair (pair (encF φ) j)).1 (fun χ => .inst χ (unpair (pair (encF φ) j)).2) = some (.inst φ j)
    rw [unpair_pair]
    exact dF1_encF φ _
  | .dist φ ψ, f+1, _ => by
    show decPAux (decP f) (unpair (pair 7 (pair (encF φ) (encF ψ)))) = some (.dist φ ψ)
    rw [unpair_pair]
    exact dF2_encF φ ψ _
  | .refl i, f+1, _ => by
    show decPAux (decP f) (unpair (pair 8 i)) = some (.refl i)
    rw [unpair_pair]
    rfl
  | .eml i j k, f+1, _ => by
    show decPAux (decP f) (unpair (pair 9 (pair i (pair j k)))) = some (.eml i j k)
    rw [unpair_pair]
    show some (PC.eml (unpair (pair i (pair j k))).1 (unpair (unpair (pair i (pair j k))).2).1 (unpair (unpair (pair i (pair j k))).2).2) = some (.eml i j k)
    rw [unpair_pair]
    show some (PC.eml i (unpair (pair j k)).1 (unpair (pair j k)).2) = some (.eml i j k)
    rw [unpair_pair]
  | .emr i j k, f+1, _ => by
    show decPAux (decP f) (unpair (pair 10 (pair i (pair j k)))) = some (.emr i j k)
    rw [unpair_pair]
    show some (PC.emr (unpair (pair i (pair j k))).1 (unpair (unpair (pair i (pair j k))).2).1 (unpair (unpair (pair i (pair j k))).2).2) = some (.emr i j k)
    rw [unpair_pair]
    show some (PC.emr i (unpair (pair j k)).1 (unpair (pair j k)).2) = some (.emr i j k)
    rw [unpair_pair]
  | .eqq i j k, f+1, _ => by
    show decPAux (decP f) (unpair (pair 11 (pair i (pair j k)))) = some (.eqq i j k)
    rw [unpair_pair]
    show some (PC.eqq (unpair (pair i (pair j k))).1 (unpair (unpair (pair i (pair j k))).2).1 (unpair (unpair (pair i (pair j k))).2).2) = some (.eqq i j k)
    rw [unpair_pair]
    show some (PC.eqq i (unpair (pair j k)).1 (unpair (pair j k)).2) = some (.eqq i j k)
    rw [unpair_pair]

/-! ### The checker and the bridge -/

/-- Is the optional formula `⊥`? -/
def isFls : Option Fml → Bool
  | some .fls => true
  | some (.mem _ _) => false
  | some (.eq _ _) => false
  | some (.imp _ _) => false
  | some (.all _) => false
  | none => false

/-- The check of an optional proof tree. -/
def checkTree : Option PC → Bool
  | some p => isFls (concl p)
  | none => false

/-- **The recursive Boolean checker**: decode the number as a proof tree and test that its
conclusion is `⊥`. -/
def checkZF (n : Nat) : Bool := checkTree (decP (n+1) n)

theorem prf_of_isFls (p : PC) (h : isFls (concl p) = true) : Prf ZF .fls := by
  cases hc : concl p with
  | none => rw [hc] at h; exact nomatch h
  | some c =>
    rw [hc] at h
    cases c with
    | fls => exact prf_of_concl p _ hc
    | mem _ _ => exact nomatch h
    | eq _ _ => exact nomatch h
    | imp _ _ => exact nomatch h
    | all _ => exact nomatch h

theorem checkZF_sound (n : Nat) (h : checkZF n = true) : Prf ZF .fls := by
  have h' : checkTree (decP (n+1) n) = true := h
  cases hd : decP (n+1) n with
  | none => rw [hd] at h'; exact nomatch h'
  | some p => rw [hd] at h'; exact prf_of_isFls p h'

theorem checkZF_complete (h : Prf ZF .fls) : ∃ n : Nat, checkZF n = true := by
  obtain ⟨p, hp⟩ := concl_of_prf h
  refine ⟨encP p, ?_⟩
  show checkTree (decP (encP p + 1) (encP p)) = true
  rw [decP_encP p _ (Nat.lt_succ_self _)]
  show isFls (concl p) = true
  rw [hp]
  rfl

/-- **The proof-code bridge**: provability of `⊥` from `ZF` is the existence of a natural number
accepted by the checker. -/
theorem prf_fls_iff_code : Prf ZF .fls ↔ ∃ n : Nat, checkZF n = true :=
  ⟨checkZF_complete, fun ⟨n, h⟩ => checkZF_sound n h⟩

/-- **Consistency as a `Π⁰₁` sentence.** -/
theorem con_iff_checker : Con ZF ↔ ∀ n : Nat, checkZF n = false :=
  ⟨fun hc n => by
    cases h : checkZF n with
    | false => rfl
    | true => exact (hc (checkZF_sound n h)).elim,
   fun h hp => by
    obtain ⟨n, hn⟩ := checkZF_complete hp
    rw [h n] at hn
    exact nomatch hn⟩

end Code

/-- info: 'PSet.Code.prf_fls_iff_code' does not depend on any axioms -/
#guard_msgs in #print axioms Code.prf_fls_iff_code
/-- info: 'PSet.Code.con_iff_checker' does not depend on any axioms -/
#guard_msgs in #print axioms Code.con_iff_checker
/-- info: 'PSet.Code.decP_encP' does not depend on any axioms -/
#guard_msgs in #print axioms Code.decP_encP

end PSet
