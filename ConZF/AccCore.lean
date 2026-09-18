import ConZF.Worldly
/-!
Where excluded middle enters the one non-stable part of the argument.

The only use of `Acc.rec` is `F` (in `Mat.lean`), and the only place where an accessibility proof
is needed is the root of the glued tree in `exists_sup`. Accessibility needs of a target
assignment only that the target of a child is an (honest) element of the target of its parent
(`acc_of_desc`). For the definability rule every case of this is constructive except one: that
the least `ν` from which a limit `η` is reached is an element of `η`. So the accessibility of the
root follows, with no excluded middle, from the single hypothesis

  `hG : ∀ η, IsOrd η → LimCase I η → Gν I η ∈ η`.

Everything else that excluded middle is used for feeds the computation of the *value* of the
recursion and the model theory, not the accessibility.
-/
universe u

namespace PSet

variable {D : PSet.{u} → PSet.{u}} {U : PSet.{u}}

/-- Accessibility only needs the descent condition. -/
theorem acc_of_desc {τ : Path.{u} → PSet.{u} → Prop}
    (desc : ∀ {l p t t'}, τ (l :: p) t → τ p t' → t ∈ t') :
    ∀ (t : PSet.{u}) (p : Path.{u}), τ p t → Acc (Rel τ) p := by
  intro t
  induction t using mem_induction with | _ t ih => ?_
  intro p hp
  exact ⟨_, fun c ⟨_, e, tc, htc⟩ => by subst e; exact ih tc (desc htc hp) _ htc⟩

variable {I : PSet.{u} → PSet.{u} → PSet.{u} → PSet.{u} → Prop}
  (I_resp : ∀ {η η' q q' x x' y y' : PSet.{u}},
    η ≈ η' → q ≈ q' → x ≈ x' → y ≈ y' → I η q x y → I η' q' x' y')
  (hG : ∀ η, IsOrd η → LimCase I η → Gν I η ∈ η)
include I_resp hG

omit I_resp in
/-- The descent of the definability rule, from `hG` alone. -/
theorem rule_mem_of_hG {η : PSet.{u}} {l : Label.{u}} {ξ : PSet.{u}} (hη : IsOrd η)
    (h : rule I η l ξ) : ξ ∈ η := by
  cases l with
  | a =>
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (mem_congr_right h).2 (mem_succ.2 (.inr (Equiv.refl _)))
    · exact (mem_congr_right h1).2 (mem_omega.2 ⟨0, h2⟩)
    · exact (mem_congr_left h2).2 (hG η hη h1)
  | b w =>
    rcases h with ⟨h1, h2, h3⟩ | ⟨_, q, s, x, y, -, h3, h4, h5, h6⟩
    · exact (mem_congr_right h1).2 ((mem_congr_left h3).2 h2)
    · exact (mem_congr_left h6).2 (h3.2.1 x y h4 h5)
  | c => exact h.elim

omit hG in
theorem tr_func' {η p t t'} (h : Tr (rule I) η p t) (h' : Tr (rule I) η p t') : t ≈ t' := by
  induction h generalizing t' with
  | nil e => cases h' with | nil e' => exact e.symm.trans e'
  | cons _ h1 ih =>
    cases h' with
    | cons h0' h1' =>
      exact rule_func I_resp h1
        (rule_resp I_resp (ih h0').symm (Label.Equiv.refl _) (Equiv.refl _) h1')

omit I_resp in
theorem tr_isOrd {η p t} (hη : IsOrd η) (h : Tr (rule I) η p t) : IsOrd t := by
  induction h with
  | nil e => exact hη.resp e
  | cons _ h1 ih => exact ih.mem (rule_mem_of_hG hG ih h1)

/-- **The root of the glued tree is accessible**, given only `hG`. Here `φ` is any relation
with ordinal values that is functional on `s`; no excluded middle is used. -/
theorem acc_root (s : PSet.{u}) (φ : PSet.{u} → PSet.{u} → Prop)
    (φ_func : ∀ {x y y'}, x ∈ s → φ x y → φ x y' → y ≈ y')
    (φ_ord : ∀ {x y}, x ∈ s → φ x y → IsOrd y) :
    Acc (Rel (Glue (Tr (rule I)) s φ)) [] := by
  have desc : ∀ {l p t t'}, Glue (Tr (rule I)) s φ (l :: p) t → Glue (Tr (rule I)) s φ p t' →
      t ∈ t' := by
    rintro l _ t t' h ⟨r, x, η, rfl, hx, hη, h'⟩
    have h := (glue_iff (T := Tr (rule I)) (φ := φ) (r := l :: r)
      (fun e h => Rule.tr_resp_root e h) φ_func hx hη).1 h
    cases h with
    | cons h0 h1 =>
      exact (mem_congr_right (tr_func' I_resp h0 h')).1
        (rule_mem_of_hG hG (tr_isOrd hG (φ_ord hx hη) h0) h1)
  exact ⟨_, fun c ⟨_, _, tc, htc⟩ => acc_of_desc desc tc c htc⟩

/-- info: 'PSet.acc_root' does not depend on any axioms -/
#guard_msgs in #print axioms acc_root
