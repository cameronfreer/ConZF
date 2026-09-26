import ConZF.Proof
/-!
Derived rules for the Hilbert system `Prf`. Composition and congruence of renamings; the
propositional combinators from `K`, `S`, modus ponens; hypothetical derivations `ND T Γ φ`
(a list of hypotheses, closed under modus ponens and theorems) with the deduction theorem
`ND.toPrf : ND T Γ φ → Prf T (imps Γ φ)` and its converse `ND.ofPrf`; introduction of an
implication (`ND.intro`), of a universal quantifier over lifted hypotheses (`ND.gen`, through
the distribution axiom), instantiation, existential introduction and elimination, and
double-negation elimination in context. The classical propositional facts about the derived
connectives are proved once, as hypothetical derivations.
-/
universe u

namespace PSet
open Fml

namespace Fml

theorem up_congr {ρ σ : Nat → Nat} (h : ∀ n, ρ n = σ n) : ∀ n, up ρ n = up σ n
  | 0 => rfl
  | n+1 => congrArg (· + 1) (h n)

theorem rename_congr {ρ σ : Nat → Nat} (h : ∀ n, ρ n = σ n) : ∀ φ, rename ρ φ = rename σ φ
  | .mem i j => show Fml.mem (ρ i) (ρ j) = Fml.mem (σ i) (σ j) from congr (congrArg Fml.mem (h i)) (h j)
  | .eq i j => show Fml.eq (ρ i) (ρ j) = Fml.eq (σ i) (σ j) from congr (congrArg Fml.eq (h i)) (h j)
  | .fls => rfl
  | .imp φ ψ => show Fml.imp (rename ρ φ) (rename ρ ψ) = Fml.imp (rename σ φ) (rename σ ψ) from
      congr (congrArg Fml.imp (rename_congr h φ)) (rename_congr h ψ)
  | .all φ => show Fml.all (rename (up ρ) φ) = Fml.all (rename (up σ) φ) from
      congrArg Fml.all (rename_congr (up_congr h) φ)

theorem up_up (ρ σ : Nat → Nat) : ∀ n, up ρ (up σ n) = up (fun n => ρ (σ n)) n
  | 0 => rfl
  | _+1 => rfl

theorem rename_rename (ρ σ : Nat → Nat) : ∀ φ, rename ρ (rename σ φ) = rename (fun n => ρ (σ n)) φ
  | .mem _ _ => rfl
  | .eq _ _ => rfl
  | .fls => rfl
  | .imp φ ψ => show Fml.imp (rename ρ (rename σ φ)) (rename ρ (rename σ ψ)) =
      Fml.imp (rename (fun n => ρ (σ n)) φ) (rename (fun n => ρ (σ n)) ψ) from
      congr (congrArg Fml.imp (rename_rename ρ σ φ)) (rename_rename ρ σ ψ)
  | .all φ => show Fml.all (rename (up ρ) (rename (up σ) φ)) = Fml.all (rename (up fun n => ρ (σ n)) φ) from
      congrArg Fml.all ((rename_rename (up ρ) (up σ) φ).trans (rename_congr (up_up ρ σ) φ))

theorem up_id : ∀ n, up (fun n => n) n = n
  | 0 => rfl
  | _+1 => rfl

theorem rename_id : ∀ φ, rename (fun n => n) φ = φ
  | .mem _ _ => rfl
  | .eq _ _ => rfl
  | .fls => rfl
  | .imp φ ψ => show Fml.imp (rename (fun n => n) φ) (rename (fun n => n) ψ) = Fml.imp φ ψ from
      congr (congrArg Fml.imp (rename_id φ)) (rename_id ψ)
  | .all φ => show Fml.all (rename (up fun n => n) φ) = Fml.all φ from
      congrArg Fml.all ((rename_congr up_id φ).trans (rename_id φ))

/-- Instantiating a lifted universal at the bound variable gives the formula back. -/
theorem inst0_up_succ (φ : Fml) : rename (inst 0) (rename (up Nat.succ) φ) = φ :=
  (rename_rename _ _ φ).trans ((rename_congr (fun n => by cases n <;> rfl) φ).trans (rename_id φ))

end Fml

namespace Prf
variable {T : Fml → Prop} {φ ψ χ : Fml}

theorem weaken (h : Prf T ψ) : Prf T (imp φ ψ) := mp k h

theorem imp_refl : Prf T (imp φ φ) := mp (mp (s (ψ := imp φ φ)) k) k

theorem imp_trans (h1 : Prf T (imp φ ψ)) (h2 : Prf T (imp ψ χ)) : Prf T (imp φ χ) :=
  mp (mp s (weaken h2)) h1

theorem imp_under (h : Prf T (imp φ ψ)) : Prf T (imp (imp χ φ) (imp χ ψ)) := mp s (weaken h)

/-- `imps [h₁, …, hₙ] φ = h₁ → (… → (hₙ → φ))`. -/
def imps : List Fml → Fml → Fml
  | [], φ => φ
  | h :: Γ, φ => imp h (imps Γ φ)

theorem imps_weaken : ∀ (Γ : List Fml), Prf T φ → Prf T (imps Γ φ)
  | [], h => h
  | _ :: Γ, h => weaken (imps_weaken Γ h)

theorem imps_s : ∀ Γ : List Fml, Prf T (imp (imps Γ (imp φ ψ)) (imp (imps Γ φ) (imps Γ ψ)))
  | [] => imp_refl
  | _ :: Γ => imp_trans (mp s (weaken (imps_s Γ))) s

theorem imp_imps : ∀ Γ : List Fml, Prf T (imp φ (imps Γ φ))
  | [] => imp_refl
  | _ :: Γ => imp_trans (imp_imps Γ) k

theorem imps_hyp : ∀ {Γ : List Fml}, φ ∈ Γ → Prf T (imps Γ φ)
  | _ :: Γ, .head _ => imp_imps Γ
  | _ :: _, .tail _ h => weaken (imps_hyp h)

/-- The lifted universal instantiated at the bound variable. -/
theorem inst_lift : Prf T (imp (lift (all φ)) φ) := by
  have h := Prf.inst (T := T) (φ := rename (up Nat.succ) φ) 0
  rw [Fml.inst0_up_succ] at h
  exact h

end Prf

/-- Hypothetical derivations: hypotheses in a list, theorems, modus ponens. -/
inductive ND (T : Fml → Prop) : List Fml → Fml → Prop
  | hyp {Γ φ} : φ ∈ Γ → ND T Γ φ
  | thm {Γ φ} : Prf T φ → ND T Γ φ
  | mp {Γ φ ψ} : ND T Γ (imp φ ψ) → ND T Γ φ → ND T Γ ψ

namespace ND
open Prf
variable {T : Fml → Prop} {Γ Δ : List Fml} {φ ψ χ : Fml}

/-- The deduction theorem. -/
theorem toPrf : ∀ {φ : Fml}, ND T Γ φ → Prf T (imps Γ φ)
  | _, hyp h => imps_hyp h
  | _, thm h => imps_weaken _ h
  | _, @mp _ _ a b d1 d2 => Prf.mp (Prf.mp (imps_s (φ := a) (ψ := b) _) (toPrf d1)) (toPrf d2)

theorem imps_elim : ∀ {Γ : List Fml}, ND T Δ (imps Γ ψ) → (∀ χ, χ ∈ Γ → χ ∈ Δ) → ND T Δ ψ
  | [], d, _ => d
  | h :: Γ, d, hsub => imps_elim (Γ := Γ) (mp d (hyp (hsub h (.head _)))) fun χ hχ => hsub χ (.tail _ hχ)

theorem ofPrf (h : Prf T (imps Γ φ)) : ND T Γ φ := imps_elim (thm h) fun _ h => h

/-- `(a → b → c) → (b → a → c)`. -/
theorem swapC : Prf T (imp (imp φ (imp ψ χ)) (imp ψ (imp φ χ))) :=
  toPrf (Γ := [imp φ (imp ψ χ), ψ, φ])
    (mp (mp (hyp (.head _)) (hyp (.tail _ (.tail _ (.head _))))) (hyp (.tail _ (.head _))))

theorem imps_swap : ∀ Γ : List Fml, Prf T (imp (imp χ (imps Γ φ)) (imps Γ (imp χ φ)))
  | [] => imp_refl
  | _ :: Γ => imp_trans swapC (imp_under (imps_swap Γ))

/-- Implication introduction. -/
theorem intro (d : ND T (χ :: Γ) φ) : ND T Γ (imp χ φ) := ofPrf (Prf.mp (imps_swap Γ) d.toPrf)

theorem wk (d : ND T Γ φ) : ND T (χ :: Γ) φ := ofPrf (weaken d.toPrf)

theorem imps_lift_dist : ∀ Γ : List Fml,
    Prf T (imp (all (imps (Γ.map lift) φ)) (imps Γ (all φ)))
  | [] => imp_refl
  | _ :: Γ => imp_trans dist (imp_under (imps_lift_dist Γ))

/-- Generalization over lifted hypotheses. -/
theorem gen (d : ND T (Γ.map lift) φ) : ND T Γ (all φ) :=
  ofPrf (Prf.mp (imps_lift_dist Γ) (Prf.gen d.toPrf))

theorem inst (j : Nat) (d : ND T Γ (all φ)) : ND T Γ (rename (Fml.inst j) φ) := mp (thm (Prf.inst j)) d

/-- A lifted universal hypothesis instantiated at the bound variable. -/
theorem inst_lift (d : ND T Γ (lift (all φ))) : ND T Γ φ := mp (thm Prf.inst_lift) d

theorem efq : Prf T (imp fls φ) := imp_trans k dne

theorem dn_intro : Prf T (imp φ (neg (neg φ))) :=
  toPrf (Γ := [φ, neg φ]) (mp (hyp (.tail _ (.head _))) (hyp (.head _)))

/-- Proof by contradiction, in context. -/
theorem by_contra (d : ND T (neg φ :: Γ) fls) : ND T Γ φ := mp (thm dne) (intro d)

theorem ex_intro (j : Nat) (d : ND T Γ (rename (Fml.inst j) φ)) : ND T Γ (ex φ) :=
  intro (mp (mp (thm (Prf.inst j)) (hyp (.head _))) (wk d))

/-- Existential elimination for the goal `⊥`: the witness is a new hypothesis, the others lifted. -/
theorem ex_elim (d : ND T Γ (ex φ)) (e : ND T (φ :: Γ.map lift) fls) : ND T Γ fls :=
  mp d (gen (intro e))

theorem and_intro (d1 : ND T Γ φ) (d2 : ND T Γ ψ) : ND T Γ (and φ ψ) :=
  intro (mp (mp (hyp (.head _)) (wk d1)) (wk d2))

theorem and_left (d : ND T Γ (and φ ψ)) : ND T Γ φ :=
  by_contra (mp (wk d) (intro (intro (mp (hyp (.tail _ (.tail _ (.head _)))) (hyp (.tail _ (.head _)))))))

theorem and_right (d : ND T Γ (and φ ψ)) : ND T Γ ψ :=
  by_contra (mp (wk d) (intro (intro (mp (hyp (.tail _ (.tail _ (.head _)))) (hyp (.head _))))))

theorem or_inl (d : ND T Γ φ) : ND T Γ (or φ ψ) :=
  intro (mp (thm efq) (mp (hyp (.head _)) (wk d)))

theorem or_inr (d : ND T Γ ψ) : ND T Γ (or φ ψ) := intro (wk d)

/-- Case analysis on a disjunction, for a goal proved from either disjunct. -/
theorem or_elim (d : ND T Γ (or φ ψ)) (d1 : ND T (φ :: Γ) χ) (d2 : ND T (ψ :: Γ) χ) : ND T Γ χ := by
  refine by_contra ?_
  have hnφ : ND T (neg χ :: Γ) (neg φ) :=
    intro (mp (hyp (.tail _ (.head _))) (mp (wk (wk (intro d1))) (hyp (.head _))))
  exact mp (hyp (.head _)) (mp (wk (intro d2)) (mp (wk d) hnφ))

theorem neg_or_right (d : ND T Γ (neg (or φ ψ))) : ND T Γ (neg ψ) :=
  intro (mp (wk d) (or_inr (hyp (.head _))))

theorem neg_or_left (d : ND T Γ (neg (or φ ψ))) : ND T Γ (neg φ) :=
  intro (mp (wk d) (or_inl (hyp (.head _))))

theorem eq_symm (i j : Nat) (d : ND T Γ (eq i j)) : ND T Γ (eq j i) :=
  mp (mp (thm (Prf.eq_eq i j i)) d) (thm (Prf.refl i))

end ND

/-- info: 'PSet.ND.toPrf' does not depend on any axioms -/
#guard_msgs in #print axioms ND.toPrf
/-- info: 'PSet.ND.gen' does not depend on any axioms -/
#guard_msgs in #print axioms ND.gen
/-- info: 'PSet.ND.or_elim' does not depend on any axioms -/
#guard_msgs in #print axioms ND.or_elim

end PSet
