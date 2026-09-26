import ConZF.Derived
import ConZF.ZF
import ConZF.ProofCode
/-!
The classical bridge from Replacement to ordinary Collection, in the object calculus. The theory
`ZFCollection` has the axioms of `ZF` with the Replacement schema replaced by ordinary Collection,
`∀x (x ∈ a → ∃y θ) → ∃b ∀x (x ∈ a → ∃y (y ∈ b ∧ θ))`. Every instance of the branch's Replacement
schema (the partial functional form, with values bounded by a set) is derivable in it
(`repl_of_collection`): totalize the matrix with the source set `a` as default output,

`θ(x, y) := ψ(x, y) ∨ (y = a ∧ ¬∃z ψ(x, z))`,

prove it total by the object calculus's double negation elimination, apply Collection, and read off
the bound: an original output is identified with the collected one by functionality, since the
default branch is then impossible. Hence `Prf ZF φ → Prf ZFCollection φ`, `Con ZFCollection → Con ZF`,
and the checker connection `checkZF n = true → Prf ZFCollection ⊥`. Classical syntactic preprocessing
only; no intuitionistic translation and no consistency claim. All renaming identities are proved
by composition and pointwise congruence; there are no axioms.
-/
namespace PSet
open Fml

namespace ZFAx

/-- Under the premise binders `[y, x, a, …]`: the matrix `θ` (variables `x = 0`, `y = 1`, parameters
from `2`, `a` among them at `2`) read at `x ↦ 1`, `y ↦ 0`. -/
def cA : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n+2 => n+2

/-- Under the conclusion binders `[y, x, b, a, …]`, and also under `[z, x, y, …]` for the inner
existential of the totalization. -/
def cB : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n+2 => n+3

/-- Ordinary Collection: `∀x (x ∈ a → ∃y θ) → ∃b ∀x (x ∈ a → ∃y (y ∈ b ∧ θ))`, `θ` with `x`, `y` as
variables `0`, `1` and the free variables of the axiom (`a` at `0`) as its variables `n+2`. -/
def coll (θ : Fml) : Fml :=
  imp (all (imp (mem 0 1) (ex (rename cA θ))))
    (ex (all (imp (mem 0 2) (ex (and (mem 0 2) (rename cB θ))))))

/-- The totalization of `ψ`: `ψ(x, y) ∨ (y = a ∧ ¬∃z ψ(x, z))`. -/
def totalize (ψ : Fml) : Fml := or ψ (and (eq 1 2) (neg (ex (rename cB ψ))))

end ZFAx

/-- The axioms of `ZF` with Replacement replaced by ordinary Collection. -/
inductive ZFCollection : Fml → Prop
  | ext : ZFCollection ZFAx.ext
  | found : ZFCollection ZFAx.found
  | pair : ZFCollection ZFAx.pair
  | union : ZFCollection ZFAx.union
  | power : ZFCollection ZFAx.power
  | inf : ZFCollection ZFAx.inf
  | sep (ψ : Fml) : ZFCollection (ZFAx.sep ψ)
  | coll (θ : Fml) : ZFCollection (ZFAx.coll θ)

namespace ZFAx
open Fml.Bound ND Prf

/-- Insert a slot at position `1`: the instance of a twice-lifted universal at the bound variable. -/
def ins1 : Nat → Nat
  | 0 => 0
  | n+1 => n+2

/-- The instance of a four-times-lifted universal at variable `1`. -/
def ins4 : Nat → Nat
  | 0 => 1
  | n+1 => n+4

/-! ### Renaming identities -/

theorem inst_lift2 (φ : Fml) :
    rename (inst 0) (rename (up Nat.succ) (rename (up Nat.succ) φ)) = rename ins1 φ := by
  rw [rename_rename, rename_rename]
  exact rename_congr (fun n => by cases n <;> rfl) φ

theorem inst_lift4 (φ : Fml) :
    rename (inst 1) (rename (up Nat.succ) (rename (up Nat.succ) (rename (up Nat.succ)
      (rename (up Nat.succ) φ)))) = rename ins4 φ := by
  rw [rename_rename, rename_rename, rename_rename, rename_rename]
  exact rename_congr (fun n => by cases n <;> rfl) φ

/-- The totalization's inner existential, instantiated at `y := a`, is the premise matrix. -/
theorem idE2 (ψ : Fml) : rename (up (inst 1)) (rename (up cA) (rename cB ψ)) = rename cA ψ := by
  rw [rename_rename, rename_rename]
  exact rename_congr (fun n => by rcases n with _ | _ | n <;> rfl) ψ

/-- The first functionality matrix, instantiated at `x, y, y'`, is `ψ(x, y)` lifted. -/
theorem idF1 (ψ : Fml) :
    rename (inst 0) (rename (up (inst 2)) (rename (up (up ins4)) (rename r1 ψ))) =
      rename Nat.succ (rename r3 ψ) := by
  rw [rename_rename, rename_rename, rename_rename, rename_rename]
  exact rename_congr (fun n => by rcases n with _ | _ | n <;> rfl) ψ

/-- The second functionality matrix, instantiated, is the collected `ψ(x, y')`. -/
theorem idF2 (ψ : Fml) :
    rename (inst 0) (rename (up (inst 2)) (rename (up (up ins4)) (rename r2 ψ))) =
      rename (up ins1) (rename cB ψ) := by
  rw [rename_rename, rename_rename, rename_rename, rename_rename]
  exact rename_congr (fun n => by rcases n with _ | _ | n <;> rfl) ψ

/-- The default clause's inner existential, instantiated at `z := y`, is `ψ(x, y)` lifted. -/
theorem idQ (ψ : Fml) :
    rename (inst 2) (rename (up (up ins1)) (rename (up cB) (rename cB ψ))) =
      rename Nat.succ (rename r3 ψ) := by
  rw [rename_rename, rename_rename, rename_rename, rename_rename]
  exact rename_congr (fun n => by rcases n with _ | _ | n <;> rfl) ψ

/-! ### The derivation -/

section
variable (ψ : Fml)

/-- The premise of Collection for the totalization is provable outright, classically. -/
theorem totalize_total : Prf ZFCollection (all (imp (mem 0 1) (ex (rename cA (totalize ψ))))) := by
  refine Prf.gen (weaken ?_)
  -- context `[x, a, …]`; `ex θA = neg (all (neg θA))`
  refine ND.toPrf (Γ := []) (intro ?_)
  -- hypothesis `H = all (neg θA)`
  have hall : ND ZFCollection [all (neg (rename cA (totalize ψ)))] (all (neg (rename cA ψ))) :=
    ND.gen (neg_or_left (inst_lift (hyp (.head _))))
  have hinst := ND.inst 1 (hyp (.head _) : ND ZFCollection [all (neg (rename cA (totalize ψ)))] _)
  -- `¬(or ψA (and (eq 1 1) (neg (ex ψE1))))` with `ψE1 = ψA`
  have hnB : ND ZFCollection [all (neg (rename cA (totalize ψ)))]
      (neg (and (eq 1 1) (neg (ex (rename (up (inst 1)) (rename (up cA) (rename cB ψ))))))) :=
    neg_or_right hinst
  rw [idE2] at hnB
  exact mp hnB (and_intro (thm (Prf.refl 1)) (mp (thm dn_intro) hall))

/-- The instance of the collected relation at the source. -/
theorem collected : Prf ZFCollection
    (ex (all (imp (mem 0 2) (ex (and (mem 0 2) (rename cB (totalize ψ))))))) :=
  Prf.mp (Prf.ax (ZFCollection.coll (totalize ψ))) (totalize_total ψ)

/-- **Replacement from Collection.** -/
theorem repl_of_collection : Prf ZFCollection (repl ψ) := by
  let F := all (imp (mem 0 1) (all (all (imp (rename r1 ψ) (imp (rename r2 ψ) (eq 1 0))))))
  let bodyC := imp (mem 0 2) (ex (and (mem 0 2) (rename cB (totalize ψ))))
  let Concl := all bodyC
  let E := ex (and (mem 0 3) (rename r3 ψ))
  let G := all (imp E (mem 0 1))
  suffices h : Prf ZFCollection (imp F (imp (ex Concl) (ex G))) from
    Prf.mp (Prf.mp swapC h) (collected ψ)
  refine ND.toPrf (Γ := [F, ex Concl]) (intro ?_)
  refine ex_elim (Γ := [all (neg G), F, ex Concl]) (hyp (.tail _ (.tail _ (.head _)))) ?_
  -- context `[b, a, …]`
  let Γ1 : List Fml := [Concl, lift (all (neg G)), lift F, lift (ex Concl)]
  show ND ZFCollection Γ1 fls
  refine mp (inst_lift (hyp (.tail _ (.head _)) : ND ZFCollection Γ1 (lift (all (neg G))))) ?_
  show ND ZFCollection Γ1 G
  refine ND.gen (intro (by_contra ?_))
  -- context `[y, b, a, …]`
  let Γ2 : List Fml := [neg (mem 0 1), E, lift Concl, lift (lift (all (neg G))), lift (lift F),
    lift (lift (ex Concl))]
  show ND ZFCollection Γ2 fls
  refine ex_elim (hyp (.tail _ (.head _)) : ND ZFCollection Γ2 E) ?_
  -- context `[x, y, b, a, …]`
  let Γ3 : List Fml := [and (mem 0 3) (rename r3 ψ), neg (mem 1 2), lift E, lift (lift Concl),
    lift (lift (lift (all (neg G)))), lift (lift (lift F)), lift (lift (lift (ex Concl)))]
  show ND ZFCollection Γ3 fls
  have hxa : ND ZFCollection Γ3 (mem 0 3) := and_left (hyp (.head _))
  have hC : ND ZFCollection Γ3 (rename (inst 0) (rename (up Nat.succ) (rename (up Nat.succ) bodyC))) :=
    ND.inst 0 (hyp (.tail _ (.tail _ (.tail _ (.head _)))))
  rw [inst_lift2] at hC
  refine ex_elim (mp hC hxa) ?_
  -- context `[y', x, y, b, a, …]`
  let Γ4 : List Fml := [and (mem 0 3) (rename (up ins1) (rename cB (totalize ψ))),
    and (mem 1 4) (rename Nat.succ (rename r3 ψ)), neg (mem 2 3), lift (lift E),
    lift (lift (lift Concl)), lift (lift (lift (lift (all (neg G))))), lift (lift (lift (lift F))),
    lift (lift (lift (lift (ex Concl))))]
  show ND ZFCollection Γ4 fls
  have hC2 : ND ZFCollection Γ4 (and (mem 0 3) (rename (up ins1) (rename cB (totalize ψ)))) := hyp (.head _)
  have hyb := and_left hC2
  have hθ := and_right hC2
  have hC1 : ND ZFCollection Γ4 (and (mem 1 4) (rename Nat.succ (rename r3 ψ))) := hyp (.tail _ (.head _))
  have hψ3 := and_right hC1
  have hny : ND ZFCollection Γ4 (neg (mem 2 3)) := hyp (.tail _ (.tail _ (.head _)))
  refine or_elim hθ ?_ ?_
  · -- case `ψ(x, y')`: functionality gives `y = y'`, so `y ∈ b`
    let P := rename (up ins1) (rename cB ψ)
    have hF : ND ZFCollection (P :: Γ4) (rename (inst 1) (rename (up Nat.succ) (rename (up Nat.succ)
        (rename (up Nat.succ) (rename (up Nat.succ)
          (imp (mem 0 1) (all (all (imp (rename r1 ψ) (imp (rename r2 ψ) (eq 1 0))))))))))) :=
      ND.inst 1 (hyp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
    rw [inst_lift4] at hF
    have hF' : ND ZFCollection (P :: Γ4)
        (imp (rename (inst 0) (rename (up (inst 2)) (rename (up (up ins4)) (rename r1 ψ))))
          (imp (rename (inst 0) (rename (up (inst 2)) (rename (up (up ins4)) (rename r2 ψ)))) (eq 2 0))) :=
      ND.inst 0 (ND.inst 2 (mp hF (and_left (wk hC1))))
    rw [idF1, idF2] at hF'
    have heq : ND ZFCollection (P :: Γ4) (eq 2 0) := mp (mp hF' (wk hψ3)) (hyp (.head _))
    exact mp (wk hny) (mp (mp (thm (Prf.eq_mem_l 0 2 3)) (eq_symm 2 0 heq)) (wk hyb))
  · -- case default: `¬∃z ψ(x, z)` contradicts `ψ(x, y)`
    let D := rename (up ins1) (rename cB (and (eq 1 2) (neg (ex (rename cB ψ)))))
    have hne : ND ZFCollection (D :: Γ4)
        (neg (ex (rename (up (up ins1)) (rename (up cB) (rename cB ψ))))) :=
      and_right (hyp (.head _) : ND ZFCollection (D :: Γ4)
        (and (eq 0 4) (neg (ex (rename (up (up ins1)) (rename (up cB) (rename cB ψ)))))))
    have hex : ND ZFCollection (D :: Γ4) (ex (rename (up (up ins1)) (rename (up cB) (rename cB ψ)))) :=
      ND.ex_intro 2 (by rw [idQ]; exact wk hψ3)
    exact mp hne hex

end

end ZFAx

/-- Every theorem of `ZF` is a theorem of `ZFCollection`. -/
theorem prf_collection_of_zf {φ : Fml} (h : Prf ZF φ) : Prf ZFCollection φ := by
  induction h with
  | ax h =>
    cases h with
    | ext => exact .ax .ext
    | found => exact .ax .found
    | pair => exact .ax .pair
    | union => exact .ax .union
    | power => exact .ax .power
    | inf => exact .ax .inf
    | sep ψ => exact .ax (.sep ψ)
    | repl ψ => exact ZFAx.repl_of_collection ψ
  | k => exact .k
  | s => exact .s
  | dne => exact .dne
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2
  | gen _ ih => exact .gen ih
  | inst j => exact .inst j
  | dist => exact .dist
  | refl i => exact .refl i
  | eq_mem_l i j k => exact .eq_mem_l i j k
  | eq_mem_r i j k => exact .eq_mem_r i j k
  | eq_eq i j k => exact .eq_eq i j k

theorem Con.zf_of_collection (h : Con ZFCollection) : Con ZF := fun hp => h (prf_collection_of_zf hp)

/-- The checker connection: an accepted code is a proof of `⊥` from Collection. -/
theorem checkZF_sound_collection (n : Nat) (h : Code.checkZF n = true) : Prf ZFCollection .fls :=
  prf_collection_of_zf (Code.checkZF_sound n h)


/-- info: 'PSet.ZFAx.repl_of_collection' does not depend on any axioms -/
#guard_msgs in #print axioms ZFAx.repl_of_collection
/-- info: 'PSet.prf_collection_of_zf' does not depend on any axioms -/
#guard_msgs in #print axioms prf_collection_of_zf
/-- info: 'PSet.Con.zf_of_collection' does not depend on any axioms -/
#guard_msgs in #print axioms Con.zf_of_collection
/-- info: 'PSet.checkZF_sound_collection' does not depend on any axioms -/
#guard_msgs in #print axioms checkZF_sound_collection

end PSet
