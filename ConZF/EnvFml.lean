import ConZF.RankFml
import ConZF.Envelope
import ConZF.Model
/-!
The envelope as a formula, and the normal-form reduction. For a formula `ψ(x, y, params)`,
`envFml ψ` says of `x` (variable `0`) and `W` (variable `1`) that `W` is the set of witnesses
`y` of `ψ(x, y)` of least rank, or empty if there are none, with rank expressed by `rankFml`.
Its satisfaction in `HG` is the envelope of `Envelope.lean` (`sat_envFml`). Envelope instances
are total and functional (`envFml_total`, `envFml_func`), and for a functional `ψ` a rank bound
on its envelope instance bounds `ψ` itself, since the envelope of an output is its singleton
(`rankBounded_of_envFml`). Hence `BoundHyp` follows from rank bounds for the envelope
instances alone (`boundHyp_of_envBoundHyp`), with the double negations in place: only one
canonical form of implicit definition needs bounds.
-/
universe u

namespace PSet
open Fml

namespace Fml

/-- Place `x` at `i`, `y` at `j`, and the parameters beyond `k` further binders. -/
def place (i j k : Nat) : Nat → Nat
  | 0 => i
  | 1 => j
  | n+2 => n+2+k

/-- `j = rank i` -/
def rankF (i j : Nat) : Fml := rename (place i j 0) rankFml

/-- `r` is an ordinal: a transitive set of transitive sets. -/
def ordF (r : Nat) : Fml := and (transF r) (all (imp (mem 0 (r+1)) (transF 0)))

/-- The envelope: `(∀y ¬ψ(x,y) ∧ ∀z z ∉ W) ∨ ∃ρ (ρ ordinal ∧ ∃y (ψ(x,y) ∧ ρ = rank y) ∧
∀y (ψ(x,y) → ∀α (α ∈ ρ → ∃r (r = rank y ∧ α ∈ r))) ∧ ∀y (y ∈ W ↔ ψ(x,y) ∧ ρ = rank y))`, with
`x` the variable `0` and `W` the variable `1`. -/
def envFml (ψ : Fml) : Fml :=
  or (and (all (neg (rename (place 1 0 1) ψ))) (all (neg (mem 0 2))))
    (ex (and (ordF 0) (and (ex (and (rename (place 2 0 2) ψ) (rankF 0 1)))
      (and (all (imp (rename (place 2 0 2) ψ)
          (all (imp (mem 0 2) (ex (and (rankF 2 0) (mem 1 0)))))))
        (all (iff (mem 0 3) (and (rename (place 2 0 2) ψ) (rankF 0 1))))))))

end Fml

theorem nn_or_nn {p q : Prop} : ¬¬(p ∨ ¬¬q) ↔ ¬¬(p ∨ q) :=
  ⟨fun h hn => h fun
    | .inl hp => hn (.inl hp)
    | .inr hq => hq fun hq => hn (.inr hq),
   nn_map (Or.imp_right nn_intro)⟩

/-! ### Readback -/

section
variable {E : Nat → PSet.{u}}

theorem sat_rankF {i j : Nat} (hi : HG (E i)) (hj : HG (E j)) :
    Sat HG (rankF i j) E ↔ E j ≈ rank (E i) :=
  (sat_rename rankFml _ E).trans <| (Sat.resp_iff (fun _ => Iff.rfl) rankFml
    (e' := Env.cons (E i) (Env.cons (E j) fun n => E (n+2))) fun n => by
      cases n with
      | zero => exact Equiv.refl _
      | succ n => cases n <;> exact Equiv.refl _).trans (sat_rankFml hi hj)

theorem sat_ordF {r : Nat} (hr : HG (E r)) : Sat HG (ordF r) E ↔ IsOrd (E r) :=
  sat_and.trans ⟨fun ⟨h1, h2⟩ => ⟨(sat_transF hr).1 h1, fun y hy =>
      (sat_transF (e := Env.cons y E) (t := 0) (hr.mem hy)).1 (h2 y (hr.mem hy) hy)⟩,
    fun h => ⟨(sat_transF hr).2 h.1, fun y hy hy' =>
      (sat_transF (e := Env.cons y E) (t := 0) hy).2 (h.2 y hy')⟩⟩

end

section
variable {ψ : Fml} {x W : PSet.{u}} {e : Nat → PSet.{u}}

theorem sat_place1 {y : PSet.{u}} :
    Sat HG (rename (place 1 0 1) ψ) (Env.cons y (Env.cons x (Env.cons W e))) ↔
      Sat HG ψ (Env.cons x (Env.cons y e)) :=
  (sat_rename ψ _ _).trans <| Sat.resp_iff (fun _ => Iff.rfl) ψ fun n => by
    cases n with
    | zero => exact Equiv.refl _
    | succ n => cases n <;> exact Equiv.refl _

theorem sat_place2 {y ρ : PSet.{u}} :
    Sat HG (rename (place 2 0 2) ψ) (Env.cons y (Env.cons ρ (Env.cons x (Env.cons W e)))) ↔
      Sat HG ψ (Env.cons x (Env.cons y e)) :=
  (sat_rename ψ _ _).trans <| Sat.resp_iff (fun _ => Iff.rfl) ψ fun n => by
    cases n with
    | zero => exact Equiv.refl _
    | succ n => cases n <;> exact Equiv.refl _

/-- The witnesses of `ψ` at `x`, in `HG`. -/
def Wit (ψ : Fml) (x : PSet.{u}) (e : Nat → PSet.{u}) (y : PSet.{u}) : Prop :=
  HG y ∧ Sat HG ψ (Env.cons x (Env.cons y e))

instance {y : PSet.{u}} : Stable (Wit ψ x e y) := inferInstanceAs (Stable (_ ∧ _))

theorem Wit.resp {y y' : PSet.{u}} (h : Wit ψ x e y) (e' : y ≈ y') : Wit ψ x e y' :=
  ⟨h.1.resp e', Sat.resp ψ (Env.cons_resp (Equiv.refl x) (Env.cons_resp e' fun _ => Equiv.refl _))
    h.2⟩

/-- **The envelope is first-order over `HG`.** -/
theorem sat_envFml (hW : HG W) :
    Sat HG (envFml ψ) (Env.cons x (Env.cons W e)) ↔ Env (Wit ψ x e) W := by
  have body : ∀ ρ, HG ρ →
      (Sat HG (and (ordF 0) (and (ex (and (rename (place 2 0 2) ψ) (rankF 0 1)))
        (and (all (imp (rename (place 2 0 2) ψ)
            (all (imp (mem 0 2) (ex (and (rankF 2 0) (mem 1 0)))))))
          (all (iff (mem 0 3) (and (rename (place 2 0 2) ψ) (rankF 0 1)))))))
        (Env.cons ρ (Env.cons x (Env.cons W e))) ↔
      IsLeast (Wit ψ x e) ρ ∧ ∀ y, y ∈ W ↔ Wit ψ x e y ∧ rank y ≈ ρ) := by
    intro ρ hρ
    refine sat_and.trans (and_congr (sat_ordF (r := 0) hρ) (sat_and.trans (and_congr ?_
      (sat_and.trans (and_congr ?_ ?_))))) |>.trans ⟨fun ⟨a, b, c, d⟩ => ⟨⟨a, b, c⟩, d⟩,
        fun ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩⟩
    · refine sat_ex.trans (nn_congr ⟨fun ⟨y, hy, hs⟩ => ?_, fun ⟨y, ⟨hy, hs⟩, er⟩ => ?_⟩)
      · have ⟨h1, h2⟩ := sat_and.1 hs
        exact ⟨y, ⟨hy, sat_place2.1 h1⟩, ((sat_rankF (i := 0) (j := 1) hy hρ).1 h2).symm⟩
      · exact ⟨y, hy, sat_and.2 ⟨sat_place2.2 hs, (sat_rankF (i := 0) (j := 1) hy hρ).2 er.symm⟩⟩
    · constructor
      · intro h y ⟨hy, hs⟩ α hα
        refine Stable.of_nn (sat_ex.1 (h y hy (sat_place2.2 hs) α (hρ.mem hα) hα))
          fun ⟨r, hr, hs'⟩ => ?_
        have ⟨h1, h2⟩ := sat_and.1 hs'
        exact (mem_congr_right ((sat_rankF (i := 2) (j := 0) hy hr).1 h1)).1 h2
      · intro h y hy hs α _ hα
        exact sat_ex.2 (nn_intro ⟨rank y, hy.rank, sat_and.2
          ⟨(sat_rankF (i := 2) (j := 0) hy hy.rank).2 (Equiv.refl _), h y ⟨hy, sat_place2.1 hs⟩ α hα⟩⟩)
    · constructor
      · intro h y
        refine ⟨fun hy => ?_, fun ⟨⟨hy, hs⟩, er⟩ => ?_⟩
        · have ⟨h1, h2⟩ := sat_and.1 ((sat_iff.1 (h y (hW.mem hy))).1 hy)
          exact ⟨⟨hW.mem hy, sat_place2.1 h1⟩, ((sat_rankF (i := 0) (j := 1) (hW.mem hy) hρ).1 h2).symm⟩
        · exact (sat_iff.1 (h y hy)).2 (sat_and.2 ⟨sat_place2.2 hs,
            (sat_rankF (i := 0) (j := 1) hy hρ).2 er.symm⟩)
      · intro h y hy
        refine sat_iff.2 ((h y).trans ⟨fun ⟨⟨_, hs⟩, er⟩ => sat_and.2 ⟨sat_place2.2 hs,
          (sat_rankF (i := 0) (j := 1) hy hρ).2 er.symm⟩, fun hs => ?_⟩)
        have ⟨h1, h2⟩ := sat_and.1 hs
        exact ⟨⟨hy, sat_place2.1 h1⟩, ((sat_rankF (i := 0) (j := 1) hy hρ).1 h2).symm⟩
  constructor
  · intro h
    refine nn_or_nn.1 (nn_map (Or.imp ?_ ?_) (sat_or.1 h))
    · intro h
      have ⟨h1, h2⟩ := sat_and.1 h
      exact ⟨fun y ⟨hy, hs⟩ => h1 y hy (sat_place1.2 hs), fun z hz => h2 z (hW.mem hz) hz⟩
    · intro h
      exact nn_map (fun ⟨ρ, hρ, hs⟩ => ⟨ρ, (body ρ hρ).1 hs⟩) (sat_ex.1 h)
  · intro h
    refine sat_or.2 (Stable.of_nn h fun
      | .inl ⟨h1, h2⟩ => nn_intro (.inl (sat_and.2 ⟨fun y hy hs => h1 y ⟨hy, sat_place1.1 hs⟩,
          fun z _ hz => h2 z hz⟩))
      | .inr ⟨ρ, hL, hWρ⟩ => ?_)
    refine Stable.of_nn hL.2.1 fun ⟨y, hy, er⟩ => ?_
    have hρ : HG ρ := hy.1.rank.resp er
    exact nn_intro (.inr (sat_ex.2 (nn_intro ⟨ρ, hρ, (body ρ hρ).2 ⟨hL, hWρ⟩⟩)))

/-- Envelope instances are total. -/
theorem envFml_total :
    ¬¬∃ W, HG W ∧ Sat HG (envFml ψ) (Env.cons x (Env.cons W e)) :=
  nn_map (fun ⟨W, h⟩ =>
    have hW : HG W := env_hg (Wit ψ x e) (fun _ h => h.1) h
    ⟨W, hW, (sat_envFml hW).2 h⟩) (env_exists (Wit ψ x e) Wit.resp)

/-- Envelope instances are functional. -/
theorem envFml_func {W' : PSet.{u}} (hW : HG W) (hW' : HG W')
    (h : Sat HG (envFml ψ) (Env.cons x (Env.cons W e)))
    (h' : Sat HG (envFml ψ) (Env.cons x (Env.cons W' e))) : W ≈ W' :=
  env_func (Wit ψ x e) ((sat_envFml hW).1 h) ((sat_envFml hW').1 h')

end

/-! ### The normal-form reduction -/

/-- A rank bound on the envelope instance of a functional `ψ` bounds `ψ`: the envelope of an
output is its singleton. -/
theorem rankBounded_of_envFml {ψ : Fml} {e : Nat → PSet.{u}} {a : PSet.{u}}
    (hf : ∀ x y y', x ∈ a → HG y → HG y' → Sat HG ψ (Env.cons x (Env.cons y e)) →
      Sat HG ψ (Env.cons x (Env.cons y' e)) → y ≈ y')
    (hb : RankBounded (envFml ψ) e a) : RankBounded ψ e a := by
  refine nn_map (fun ⟨κ, hκ, hbound⟩ => ⟨κ, hκ, fun x y hx hy hs => ?_⟩) hb
  have hW : HG (singleton y) := hy.singleton
  have hs' : Sat HG (envFml ψ) (Env.cons x (Env.cons (singleton y) e)) :=
    (sat_envFml hW).2 (env_singleton (Wit ψ x e) Wit.resp
      (fun _ _ h h' => hf x _ _ hx h.1 h'.1 h.2 h'.2) ⟨hy, hs⟩)
  exact hκ.trans _ (hbound x _ hx hW hs') _ (rank_mem (self_mem_singleton y))

/-- Rank bounds for the envelope instances: total and functional definitions, with no
functionality hypothesis to discharge. -/
def EnvBoundHyp : Prop :=
  ∀ (ψ : Fml) (e : Nat → PSet.{u}), (∀ i, HG (e i)) → ∀ a, HG a → RankBounded (envFml ψ) e a

/-- **Normal form.** Bounds for the envelope instances give `BoundHyp`. -/
theorem boundHyp_of_envBoundHyp (h : EnvBoundHyp.{u}) : BoundHyp.{u} :=
  fun ψ e he a ha hf => rankBounded_of_envFml hf (h ψ e he a ha)

theorem con_ZF_of_envBoundHyp (h : EnvBoundHyp.{0}) : Con ZF :=
  con_ZF_of_bounds (boundHyp_of_envBoundHyp h)

/-- info: 'PSet.sat_envFml' does not depend on any axioms -/
#guard_msgs in #print axioms sat_envFml
/-- info: 'PSet.envFml_total' does not depend on any axioms -/
#guard_msgs in #print axioms envFml_total
/-- info: 'PSet.con_ZF_of_envBoundHyp' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZF_of_envBoundHyp

end PSet
