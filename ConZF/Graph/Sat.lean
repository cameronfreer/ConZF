import ConZF.Graph.Rank
import ConZF.Fml
/-!
Satisfaction over graph sets, for the existing formula syntax `Fml`. `GSet.Sat M φ e` reads
equality as bisimulation and membership as graph membership, with quantifiers over a class
`M : GSet → Prop`; over a graph set `G` the class is `Mem · G`. Satisfaction is stable, respects
bisimulation of the environment and equivalence of classes, commutes with renaming, and depends
on finitely many variables. These are the same proofs as `PSet.Sat`, over the graph relations.
-/
universe u

namespace GSet
open PSet.Fml

/-- Extending an environment. -/
def Env.cons (x : GSet.{u}) (e : Nat → GSet.{u}) : Nat → GSet.{u}
  | 0 => x
  | n+1 => e n

/-- Satisfaction in the class `M`. -/
def Sat (M : GSet.{u} → Prop) : PSet.Fml → (Nat → GSet.{u}) → Prop
  | .mem i j, e => Mem (e i) (e j)
  | .eq i j, e => Equiv (e i) (e j)
  | .fls, _ => False
  | .imp φ ψ, e => Sat M φ e → Sat M ψ e
  | .all φ, e => ∀ x, M x → Sat M φ (Env.cons x e)

theorem Env.cons_resp {x x' : GSet.{u}} {e e' : Nat → GSet.{u}} (hx : Equiv x x')
    (he : ∀ i, Equiv (e i) (e' i)) : ∀ i, Equiv (Env.cons x e i) (Env.cons x' e' i)
  | 0 => hx
  | n+1 => he n

theorem Sat.resp_iff {M M' : GSet.{u} → Prop} (hM : ∀ x, M x ↔ M' x) :
    ∀ (φ : PSet.Fml) {e e' : Nat → GSet.{u}}, (∀ i, Equiv (e i) (e' i)) →
      (Sat M φ e ↔ Sat M' φ e')
  | .mem i j, _, _, h => (mem_congr_left (h i)).trans (mem_congr_right (h j))
  | .eq i j, _, _, h =>
    ⟨fun s => (h i).symm.trans (s.trans (h j)), fun s => (h i).trans (s.trans (h j).symm)⟩
  | .fls, _, _, _ => Iff.rfl
  | .imp φ ψ, _, _, h =>
    have h1 := Sat.resp_iff hM φ h; have h2 := Sat.resp_iff hM ψ h
    ⟨fun s a => h2.1 (s (h1.2 a)), fun s a => h2.2 (s (h1.1 a))⟩
  | .all φ, _, _, h =>
    ⟨fun s x hx => (Sat.resp_iff hM φ (Env.cons_resp (Equiv.refl x) h)).1 (s x ((hM x).2 hx)),
     fun s x hx => (Sat.resp_iff hM φ (Env.cons_resp (Equiv.refl x) h)).2 (s x ((hM x).1 hx))⟩

theorem Sat.resp {M : GSet.{u} → Prop} (φ : PSet.Fml) {e e' : Nat → GSet.{u}}
    (h : ∀ i, Equiv (e i) (e' i)) (s : Sat M φ e) : Sat M φ e' :=
  (Sat.resp_iff (fun _ => Iff.rfl) φ h).1 s

/-- Satisfaction over a graph set is invariant under its equivalence. -/
theorem Sat.congr {G G' : GSet.{u}} (e : Equiv G G') (φ : PSet.Fml) (env : Nat → GSet.{u}) :
    Sat (Mem · G) φ env ↔ Sat (Mem · G') φ env :=
  Sat.resp_iff (fun _ => mem_congr_right e) φ fun _ => Equiv.refl _

theorem sat_rename {M : GSet.{u} → Prop} :
    ∀ (φ : PSet.Fml) (ρ : Nat → Nat) (e : Nat → GSet.{u}),
      Sat M (rename ρ φ) e ↔ Sat M φ (fun i => e (ρ i))
  | .mem _ _, _, _ | .eq _ _, _, _ | .fls, _, _ => Iff.rfl
  | .imp φ ψ, ρ, e =>
    have h1 := sat_rename φ ρ e; have h2 := sat_rename ψ ρ e
    ⟨fun s a => h2.1 (s (h1.2 a)), fun s a => h2.2 (s (h1.1 a))⟩
  | .all φ, ρ, e =>
    have H : ∀ x, Sat M (rename (up ρ) φ) (Env.cons x e) ↔
        Sat M φ (Env.cons x fun i => e (ρ i)) := fun x =>
      (sat_rename φ (up ρ) (Env.cons x e)).trans <| Sat.resp_iff (fun _ => Iff.rfl) φ
        fun i => by cases i <;> exact Equiv.refl _
    ⟨fun s x hx => (H x).1 (s x hx), fun s x hx => (H x).2 (s x hx)⟩

/-- Satisfaction depends only on the free variables. -/
theorem sat_bound {M : GSet.{u} → Prop} :
    ∀ {φ : PSet.Fml} {k : Nat} {e e' : Nat → GSet.{u}}, Bound k φ →
      (∀ i, i < k → Equiv (e i) (e' i)) → (Sat M φ e ↔ Sat M φ e')
  | .mem i j, _, _, _, ⟨hi, hj⟩, h => (mem_congr_left (h i hi)).trans (mem_congr_right (h j hj))
  | .eq i j, _, _, _, ⟨hi, hj⟩, h =>
    ⟨fun s => (h i hi).symm.trans (s.trans (h j hj)),
     fun s => (h i hi).trans (s.trans (h j hj).symm)⟩
  | .fls, _, _, _, _, _ => Iff.rfl
  | .imp φ ψ, _, _, _, ⟨b1, b2⟩, h =>
    have h1 := sat_bound b1 h; have h2 := sat_bound b2 h
    ⟨fun s a => h2.1 (s (h1.2 a)), fun s a => h2.2 (s (h1.1 a))⟩
  | .all φ, _, _, _, b, h =>
    have H : ∀ x, Sat M φ (Env.cons x _) ↔ Sat M φ (Env.cons x _) := fun x =>
      sat_bound b fun i hi => by
        cases i with
        | zero => exact Equiv.refl _
        | succ i => exact h i (Nat.lt_of_succ_lt_succ hi)
    ⟨fun s x hx => (H x).1 (s x hx), fun s x hx => (H x).2 (s x hx)⟩

theorem Sat.stable {M : GSet.{u} → Prop} : ∀ (φ : PSet.Fml) (e : Nat → GSet.{u}), Stable (Sat M φ e)
  | .mem _ _, _ => inferInstanceAs (Stable (Mem _ _))
  | .eq _ _, _ => inferInstanceAs (Stable (Equiv _ _))
  | .fls, _ => inferInstanceAs (Stable False)
  | .imp _ ψ, e => have := Sat.stable (M := M) ψ e; inferInstanceAs (Stable (_ → _))
  | .all φ, e => have := fun x => Sat.stable (M := M) φ (Env.cons x e)
    inferInstanceAs (Stable (∀ _, _ → _))

instance {M : GSet.{u} → Prop} {φ e} : Stable (Sat M φ e) := Sat.stable φ e

theorem sat_neg {M : GSet.{u} → Prop} {φ : PSet.Fml} {e} : Sat M (neg φ) e ↔ ¬ Sat M φ e := Iff.rfl

theorem sat_and {M : GSet.{u} → Prop} {φ ψ : PSet.Fml} {e} :
    Sat M (PSet.Fml.and φ ψ) e ↔ Sat M φ e ∧ Sat M ψ e :=
  ⟨fun h => ⟨Stable.dne fun h1 => h fun a => (h1 a).elim, Stable.dne fun h2 => h fun _ b => h2 b⟩,
   fun ⟨a, b⟩ h => h a b⟩

theorem sat_or {M : GSet.{u} → Prop} {φ ψ : PSet.Fml} {e} :
    Sat M (PSet.Fml.or φ ψ) e ↔ ¬¬(Sat M φ e ∨ Sat M ψ e) :=
  ⟨fun h hn => hn (.inr (h fun a => hn (.inl a))),
   fun h n => Stable.of_nn h fun
    | .inl a => (n a).elim
    | .inr b => b⟩

theorem sat_iff {M : GSet.{u} → Prop} {φ ψ : PSet.Fml} {e} :
    Sat M (PSet.Fml.iff φ ψ) e ↔ (Sat M φ e ↔ Sat M ψ e) :=
  sat_and.trans ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

theorem sat_ex {M : GSet.{u} → Prop} {φ : PSet.Fml} {e} :
    Sat M (ex φ) e ↔ ¬¬∃ x, M x ∧ Sat M φ (Env.cons x e) :=
  ⟨fun h hn => h fun x hx s => hn ⟨x, hx, s⟩, fun h k => h fun ⟨x, hx, s⟩ => k x hx s⟩

end GSet
