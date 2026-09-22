import ConZF.VLevel
/-!
Stable binary bar induction on the negative Cantor space, and source-wide caps.

The source is `powerset omega`, the negative subsets of `ω`: a point is an actual set, its bit
statements `ofNat n ∈ X` are stable, and Separation makes a point out of any stable predicate
on `Nat`. Finite binary words are lists, most recent bit first, so the children of `s` are
`false :: s` and `true :: s`, and `Prec s X` says the bits of `s` agree with `X`.

For a stable predicate `G` on words closed under joining the two children (`G (false :: s)`
and `G (true :: s)` give `G s`), the *greedy* words (`Greedy`) take `0` when `G` is refutable
at the left child and `1` when it is irrefutable there: a predicate, not a choice of bits. The
greedy real `greedyReal G` is the point whose bit `n` holds when some greedy word of length
`n+1` ends in `1`, by Separation; its prefixes are exactly the greedy words
(`prec_greedyReal`). Every greedy word is bad when the root is, so a hit of `G` on the greedy
real gives `G []` (`root_of_hit`), and so does a bar over all points (`bar_induction`). This
is not the fan theorem for `Nat → Bool`: the bar must cover the proposition-valued point.

Application: for a relation `P` from points to sets, `LocCap P s` says, negatively, that some
ordinal caps the witness ranks throughout the cylinder of `s`. Local caps join by ordinal
union (`locCap_join`), so local caps at every point give a source-wide cap (`cap_of_bar`),
with no function selecting the local caps; and a cap exists iff the greedy real of `LocCap P`
has a locally capped prefix (`hasCap_iff`), the single-critical-real criterion.
-/
universe u

namespace PSet

/-! ### Greedy words -/

section
variable (G : List Bool → Prop)

/-- Take `0` when `G` is refutable at the left child, `1` when it is irrefutable there. -/
def Greedy : List Bool → Prop
  | [] => True
  | false :: s => Greedy s ∧ ¬ G (false :: s)
  | true :: s => Greedy s ∧ ¬¬ G (false :: s)

instance greedy_stable : ∀ {s : List Bool}, Stable (Greedy G s)
  | [] => inferInstanceAs (Stable True)
  | false :: s => by
    have : Stable (Greedy G s) := greedy_stable
    exact inferInstanceAs (Stable (Greedy G s ∧ ¬_))
  | true :: s => by
    have : Stable (Greedy G s) := greedy_stable
    exact inferInstanceAs (Stable (Greedy G s ∧ ¬_))

theorem Greedy.tail : ∀ {b : Bool} {s : List Bool}, Greedy G (b :: s) → Greedy G s
  | false, _, h => h.1
  | true, _, h => h.1

/-- Every greedy word is bad when the root is. -/
theorem greedy_bad [∀ s, Stable (G s)] (join : ∀ s, G (false :: s) → G (true :: s) → G s)
    (bad : ¬ G []) : ∀ s, Greedy G s → ¬ G s
  | [], _ => bad
  | false :: _, h => h.2
  | true :: s, h => fun hg => greedy_bad join bad s h.1 (join s (Stable.dne h.2) hg)

/-- Greedy words of the same length are equal. -/
theorem greedy_unique : ∀ {s s' : List Bool}, Greedy G s → Greedy G s' →
    s.length = s'.length → s = s'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => Nat.noConfusion h
  | _ :: _, [], _, _, h => Nat.noConfusion h
  | b :: s, b' :: s', h, h', e => by
    have e' : s = s' := greedy_unique h.tail h'.tail (Nat.succ.inj e)
    subst e'
    cases b <;> cases b'
    · rfl
    · exact (h'.2 h.2).elim
    · exact (h.2 h'.2).elim
    · rfl

/-- There is, negatively, a greedy word of every length. -/
theorem greedy_exists : ∀ n : Nat, ¬¬∃ s, Greedy G s ∧ s.length = n
  | 0 => nn_intro ⟨[], trivial, rfl⟩
  | n+1 => by
    refine nn_bind (greedy_exists n) fun ⟨s, hs, hn⟩ => ?_
    refine Stable.by_cases (G (false :: s)) (fun h => nn_intro ⟨true :: s, ⟨hs, nn_intro h⟩, ?_⟩)
      fun h => nn_intro ⟨false :: s, ⟨hs, h⟩, ?_⟩
    all_goals exact congrArg Nat.succ hn

end

/-! ### The negative Cantor space -/

instance {b : Bool} : Stable (b = true) :=
  ⟨fun h => by cases b with
    | true => rfl
    | false => exact (h fun h' => Bool.noConfusion h').elim⟩

/-- The bits of `s` agree with `X`: the head of `s` is the bit at `s.length`. -/
def Prec : List Bool → PSet.{u} → Prop
  | [], _ => True
  | b :: s, X => Prec s X ∧ (b = true ↔ ofNat s.length ∈ X)

instance prec_stable : ∀ {s : List Bool} {X : PSet.{u}}, Stable (Prec s X)
  | [], _ => inferInstanceAs (Stable True)
  | _ :: s, X => by
    have : Stable (Prec s X) := prec_stable
    exact inferInstanceAs (Stable (Prec s X ∧ (_ ↔ _)))

/-- The greedy real: bit `n` holds when a greedy word of length `n+1` ends in `1`. -/
def greedyReal (G : List Bool → Prop) : PSet.{u} :=
  sep (fun z => ¬¬∃ s, Greedy G (true :: s) ∧ z ≈ ofNat s.length) omega

section
variable (G : List Bool → Prop)

theorem greedyReal_mem_powerset : greedyReal.{u} G ∈ powerset omega :=
  mem_powerset.2 fun _ hz => ((mem_sep fun _ _ e => nn_map fun ⟨s, hs, e'⟩ =>
    ⟨s, hs, e.symm.trans e'⟩).1 hz).1

theorem ofNat_mem_greedyReal {n : Nat} :
    ofNat.{u} n ∈ greedyReal G ↔ ¬¬∃ s, Greedy G (true :: s) ∧ s.length = n := by
  refine (mem_sep fun _ _ e => nn_map fun ⟨s, hs, e'⟩ => ⟨s, hs, e.symm.trans e'⟩).trans
    ⟨fun h => nn_map (fun ⟨s, hs, e⟩ => ⟨s, hs, ofNat_inj e.symm⟩) h.2,
     fun h => ⟨ofNat_mem_omega n, nn_map (fun ⟨s, hs, e⟩ => ⟨s, hs, e ▸ Equiv.refl _⟩) h⟩⟩

variable [∀ s, Stable (G s)]

/-- The prefixes of the greedy real are the greedy words. -/
theorem prec_greedyReal : ∀ s, Prec s (greedyReal.{u} G) ↔ Greedy G s
  | [] => Iff.rfl
  | b :: s => by
    have ih := prec_greedyReal s
    have key : Greedy G s → (ofNat.{u} s.length ∈ greedyReal G ↔ ¬¬G (false :: s)) := fun hs =>
      (ofNat_mem_greedyReal G).trans
        ⟨fun h => Stable.of_nn h fun ⟨s', hs', e⟩ =>
          (greedy_unique G hs'.1 hs e ▸ hs').2,
         fun h => nn_intro ⟨s, ⟨hs, h⟩, rfl⟩⟩
    cases b
    · constructor
      · rintro ⟨hp, hb⟩
        exact ⟨ih.1 hp, fun hg => Bool.noConfusion (hb.2 ((key (ih.1 hp)).2 (nn_intro hg)))⟩
      · rintro ⟨hs, hn⟩
        exact ⟨ih.2 hs, ⟨fun h => Bool.noConfusion h, fun h => (hn (Stable.dne ((key hs).1 h))).elim⟩⟩
    · constructor
      · rintro ⟨hp, hb⟩
        exact ⟨ih.1 hp, (key (ih.1 hp)).1 (hb.1 rfl)⟩
      · rintro ⟨hs, hn⟩
        exact ⟨ih.2 hs, ⟨fun _ => (key hs).2 hn, fun _ => rfl⟩⟩

variable (join : ∀ s, G (false :: s) → G (true :: s) → G s)
include join

/-- **Stable bar induction at one point.** A hit of `G` on the greedy real gives `G` at the
root. -/
theorem root_of_hit (hit : ¬¬∃ s, Prec s (greedyReal.{u} G) ∧ G s) : G [] :=
  Stable.dne fun bad => hit fun ⟨s, hp, hg⟩ =>
    greedy_bad G join bad s ((prec_greedyReal G s).1 hp) hg

/-- **Stable bar induction.** A bar over all negative points gives `G` at the root. -/
theorem bar_induction (bar : ∀ X, X ∈ powerset omega.{u} → ¬¬∃ s, Prec s X ∧ G s) : G [] :=
  root_of_hit G join (bar _ (greedyReal_mem_powerset G))

end

/-! ### Source-wide caps -/

section
variable (P : PSet.{u} → PSet.{u} → Prop)

/-- `κ` caps the witness ranks throughout the cylinder of `s`. -/
def CapAt (κ : PSet.{u}) (s : List Bool) : Prop :=
  ∀ X, X ∈ powerset omega.{u} → Prec s X → (¬¬∃ y, P X y) → ¬¬∃ y, P X y ∧ rank y ∈ κ

/-- Some ordinal caps the cylinder of `s`, negatively. -/
def LocCap (s : List Bool) : Prop := ¬¬∃ κ, IsOrd κ ∧ CapAt P κ s

instance {s : List Bool} : Stable (LocCap P s) := inferInstanceAs (Stable (¬_))

theorem isOrd_union {a b : PSet.{u}} (ha : IsOrd a) (hb : IsOrd b) : IsOrd (union a b) := by
  refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · exact Stable.of_nn (mem_union.1 hy) fun
      | .inl h => mem_union.2 (nn_intro (.inl (ha.trans y h z hz)))
      | .inr h => mem_union.2 (nn_intro (.inr (hb.trans y h z hz)))
  · exact Stable.of_nn (mem_union.1 hy) fun
      | .inl h => ha.mem_trans y h
      | .inr h => hb.mem_trans y h

/-- Local caps at the two children join by ordinal union: no cap is selected. -/
theorem locCap_join (s : List Bool) (h0 : LocCap P (false :: s)) (h1 : LocCap P (true :: s)) :
    LocCap P s := by
  refine Stable.of_nn h0 fun ⟨κ0, hκ0, hc0⟩ => Stable.of_nn h1 fun ⟨κ1, hκ1, hc1⟩ => ?_
  refine nn_intro ⟨union κ0 κ1, isOrd_union hκ0 hκ1, fun X hX hp hE => ?_⟩
  refine Stable.by_cases (ofNat s.length ∈ X) (fun hb => ?_) fun hb => ?_
  · exact nn_map (fun ⟨y, hy, hr⟩ => ⟨y, hy, mem_union.2 (nn_intro (.inr hr))⟩)
      (hc1 X hX ⟨hp, fun _ => hb, fun _ => rfl⟩ hE)
  · exact nn_map (fun ⟨y, hy, hr⟩ => ⟨y, hy, mem_union.2 (nn_intro (.inl hr))⟩)
      (hc0 X hX ⟨hp, fun h => Bool.noConfusion h, fun h => (hb h).elim⟩ hE)

/-- **Local caps everywhere give a source-wide cap.** -/
theorem cap_of_bar (bar : ∀ X, X ∈ powerset omega.{u} → ¬¬∃ s, Prec s X ∧ LocCap P s) :
    ¬¬∃ κ, IsOrd κ ∧ ∀ X, X ∈ powerset omega.{u} → (¬¬∃ y, P X y) →
      ¬¬∃ y, P X y ∧ rank y ∈ κ :=
  nn_map (fun ⟨κ, hκ, hc⟩ => ⟨κ, hκ, fun X hX => hc X hX trivial⟩)
    (bar_induction (LocCap P) (locCap_join P) bar)

/-- **The critical real.** A source-wide cap exists iff the greedy real of `LocCap P` has a
locally capped prefix. -/
theorem hasCap_iff :
    (¬¬∃ κ, IsOrd κ ∧ CapAt P κ []) ↔
      ¬¬∃ s, Prec s (greedyReal.{u} (LocCap P)) ∧ LocCap P s :=
  ⟨fun h => nn_intro ⟨[], trivial, h⟩, root_of_hit (LocCap P) (locCap_join P)⟩

end

/-- info: 'PSet.bar_induction' does not depend on any axioms -/
#guard_msgs in #print axioms bar_induction
/-- info: 'PSet.cap_of_bar' does not depend on any axioms -/
#guard_msgs in #print axioms cap_of_bar
/-- info: 'PSet.hasCap_iff' does not depend on any axioms -/
#guard_msgs in #print axioms hasCap_iff

end PSet
