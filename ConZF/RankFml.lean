import ConZF.RankGraph
/-!
Rank as a first-order formula. `rankFml` says, of `x` (variable `0`) and `ρ` (variable `1`):
there are a transitive set `T` containing `x` and a graph `g` on `T`, total, functional, and
satisfying the rank recursion, with `(x, ρ) ∈ g`. Pairs are Kuratowski pairs, written out by
membership. Its satisfaction in `HG` agrees with native rank (`sat_rankFml`): the witnesses are
`tclDom x` and `rankGraph x`, in `HG` by `RankGraph.lean`, and uniqueness is `rank_unique`.
No Replacement and no model theorem is used, so the bridge is available to the normal-form
reduction of `Envelope.lean` without circularity.
-/
universe u

namespace PSet
open Fml

/-! ### Pairs by membership -/

namespace Fml

/-- `∀v (v ∈ w ↔ v = a)` -/
def isSing (w a : Nat) : Fml := all (iff (mem 0 (w+1)) (eq 0 (a+1)))

/-- `∀v (v ∈ w ↔ v = a ∨ v = b)` -/
def isUpair (w a b : Nat) : Fml := all (iff (mem 0 (w+1)) (or (eq 0 (a+1)) (eq 0 (b+1))))

/-- `∀v (v ∈ p ↔ v = {a} ∨ v = {a, b})` -/
def isPair (p a b : Nat) : Fml :=
  all (iff (mem 0 (p+1)) (or (isSing 0 (a+1)) (isUpair 0 (a+1) (b+1))))

/-- `∃u (u ∈ g ∧ u = (a, b))` -/
def pairMem (g a b : Nat) : Fml := ex (and (mem 0 (g+1)) (isPair 0 (a+1) (b+1)))

/-- `∀z (z ∈ T → ∀w (w ∈ z → w ∈ T))` -/
def transF (t : Nat) : Fml := all (imp (mem 0 (t+1)) (all (imp (mem 0 1) (mem 0 (t+2)))))

/-- `∀z (z ∈ T → ∃α (z, α) ∈ g)` -/
def totF (t g : Nat) : Fml := all (imp (mem 0 (t+1)) (ex (pairMem (g+2) 1 0)))

/-- `∀z (z ∈ T → ∀α ∀β ((z, α) ∈ g → (z, β) ∈ g → α = β))` -/
def funcF (t g : Nat) : Fml :=
  all (imp (mem 0 (t+1)) (all (all (imp (pairMem (g+3) 2 1) (imp (pairMem (g+3) 2 0) (eq 1 0))))))

/-- `∀z (z ∈ T → ∀α ((z, α) ∈ g → ∀γ (γ ∈ α ↔ ∃w (w ∈ z ∧ ∃δ ((w, δ) ∈ g ∧ (γ ∈ δ ∨ γ = δ))))))` -/
def recF (t g : Nat) : Fml :=
  all (imp (mem 0 (t+1)) (all (imp (pairMem (g+2) 1 0) (all (iff (mem 0 1)
    (ex (and (mem 0 3) (ex (and (pairMem (g+5) 1 0) (or (mem 2 0) (eq 2 0)))))))))))

/-- `ρ = rank x`, with `x` the variable `0` and `ρ` the variable `1`. -/
def rankFml : Fml :=
  ex (ex (and (mem 2 1) (and (transF 1) (and (totF 1 0) (and (funcF 1 0)
    (and (recF 1 0) (pairMem 0 2 3)))))))

end Fml

/-! ### Readback over `HG` -/

section
variable {e : Nat → PSet.{u}}

theorem sat_isSing {w a : Nat} (hw : HG (e w)) (ha : HG (e a)) :
    Sat HG (isSing w a) e ↔ e w ≈ singleton (e a) := by
  constructor
  · intro h
    refine ext fun v => ⟨fun hv => mem_singleton.2 (sat_iff.1 (h v (hw.mem hv)) |>.1 hv),
      fun hv => ?_⟩
    have e' := mem_singleton.1 hv
    exact (sat_iff.1 (h v (ha.resp e'.symm))).2 e'
  · intro h v _
    exact sat_iff.2 ((mem_congr_right h).trans mem_singleton)

theorem sat_isUpair {w a b : Nat} (hw : HG (e w)) (ha : HG (e a)) (hb : HG (e b)) :
    Sat HG (isUpair w a b) e ↔ e w ≈ upair (e a) (e b) := by
  constructor
  · intro h
    refine ext fun v => ⟨fun hv => mem_upair.2 (sat_or.1 (sat_iff.1 (h v (hw.mem hv)) |>.1 hv)),
      fun hv => ?_⟩
    have hvH : HG v := (HG.upair ha hb).mem hv
    exact (sat_iff.1 (h v hvH)).2 (sat_or.2 (mem_upair.1 hv))
  · intro h v _
    refine sat_iff.2 ((mem_congr_right h).trans (mem_upair.trans ?_))
    exact (sat_or (M := HG) (φ := eq 0 (a+1)) (ψ := eq 0 (b+1)) (e := Env.cons v e)).symm

theorem sat_isPair {p a b : Nat} (hp : HG (e p)) (ha : HG (e a)) (hb : HG (e b)) :
    Sat HG (isPair p a b) e ↔ e p ≈ pair (e a) (e b) := by
  have inner : ∀ v, HG v → (Sat HG (or (isSing 0 (a+1)) (isUpair 0 (a+1) (b+1))) (Env.cons v e) ↔
      ¬¬(v ≈ singleton (e a) ∨ v ≈ upair (e a) (e b))) := fun v hv =>
    sat_or.trans (nn_congr (or_congr (sat_isSing (e := Env.cons v e) (w := 0) (a := a+1) hv ha)
      (sat_isUpair (e := Env.cons v e) (w := 0) (a := a+1) (b := b+1) hv ha hb)))
  constructor
  · intro h
    refine ext fun v => ⟨fun hv => mem_upair.2 ((inner v (hp.mem hv)).1
      ((sat_iff.1 (h v (hp.mem hv))).1 hv)), fun hv => ?_⟩
    have hvH : HG v := (HG.pair ha hb).mem hv
    exact (sat_iff.1 (h v hvH)).2 ((inner v hvH).2 (mem_upair.1 hv))
  · intro h v hv
    exact sat_iff.2 ((mem_congr_right h).trans (mem_upair.trans (inner v hv).symm))

theorem sat_pairMem {g a b : Nat} (ha : HG (e a)) (hb : HG (e b)) :
    Sat HG (pairMem g a b) e ↔ pair (e a) (e b) ∈ e g := by
  refine sat_ex.trans ?_
  have inner : ∀ u, HG u → (Sat HG (and (mem 0 (g+1)) (isPair 0 (a+1) (b+1))) (Env.cons u e) ↔
      u ∈ e g ∧ u ≈ pair (e a) (e b)) := fun u hu =>
    sat_and.trans (and_congr Iff.rfl
      (sat_isPair (e := Env.cons u e) (p := 0) (a := a+1) (b := b+1) hu ha hb))
  constructor
  · intro h
    exact Stable.of_nn h fun ⟨u, hu, hs⟩ =>
      have ⟨h1, h2⟩ := (inner u hu).1 hs
      (mem_congr_left h2).1 h1
  · intro h
    exact nn_intro ⟨_, HG.pair ha hb, (inner _ (HG.pair ha hb)).2 ⟨h, Equiv.refl _⟩⟩

theorem sat_transF {t : Nat} (ht : HG (e t)) :
    Sat HG (transF t) e ↔ ∀ z, z ∈ e t → ∀ w, w ∈ z → w ∈ e t :=
  ⟨fun h z hz w hw => h z (ht.mem hz) hz w ((ht.mem hz).mem hw) hw,
   fun h z _ hz w _ hw => h z hz w hw⟩

theorem sat_totF {t g : Nat} (ht : HG (e t)) :
    Sat HG (totF t g) e ↔ ∀ z, z ∈ e t → ¬¬∃ α, HG α ∧ pair z α ∈ e g := by
  constructor
  · intro h z hz
    refine nn_map (fun ⟨α, hα, hs⟩ => ⟨α, hα, ?_⟩) (sat_ex.1 (h z (ht.mem hz) hz))
    exact (sat_pairMem (e := Env.cons α (Env.cons z e)) (g := g+2) (a := 1) (b := 0)
      (ht.mem hz) hα).1 hs
  · intro h z hz hz'
    refine sat_ex.2 (nn_map (fun ⟨α, hα, hm⟩ => ⟨α, hα, ?_⟩) (h z hz'))
    exact (sat_pairMem (e := Env.cons α (Env.cons z e)) (g := g+2) (a := 1) (b := 0) hz hα).2 hm

theorem sat_funcF {t g : Nat} (ht : HG (e t)) :
    Sat HG (funcF t g) e ↔ ∀ z, z ∈ e t → ∀ α β, HG α → HG β →
      pair z α ∈ e g → pair z β ∈ e g → α ≈ β := by
  constructor
  · intro h z hz α β hα hβ h1 h2
    exact h z (ht.mem hz) hz α hα β hβ
      ((sat_pairMem (e := Env.cons β (Env.cons α (Env.cons z e))) (g := g+3) (a := 2) (b := 1)
        (ht.mem hz) hα).2 h1)
      ((sat_pairMem (e := Env.cons β (Env.cons α (Env.cons z e))) (g := g+3) (a := 2) (b := 0)
        (ht.mem hz) hβ).2 h2)
  · intro h z hz hz' α hα β hβ h1 h2
    exact h z hz' α β hα hβ
      ((sat_pairMem (e := Env.cons β (Env.cons α (Env.cons z e))) (g := g+3) (a := 2) (b := 1)
        hz hα).1 h1)
      ((sat_pairMem (e := Env.cons β (Env.cons α (Env.cons z e))) (g := g+3) (a := 2) (b := 0)
        hz hβ).1 h2)

theorem sat_recF {t g : Nat} (ht : HG (e t)) :
    Sat HG (recF t g) e ↔ ∀ z, z ∈ e t → ∀ α, HG α → pair z α ∈ e g → ∀ γ, HG γ →
      (γ ∈ α ↔ ¬¬∃ w, HG w ∧ w ∈ z ∧ ¬¬∃ δ, HG δ ∧ pair w δ ∈ e g ∧ γ ∈ succ δ) := by
  have inner : ∀ z α γ, HG z → HG α → HG γ →
      (Sat HG (ex (and (mem 0 3) (ex (and (pairMem (g+5) 1 0) (or (mem 2 0) (eq 2 0))))))
        (Env.cons γ (Env.cons α (Env.cons z e))) ↔
      ¬¬∃ w, HG w ∧ w ∈ z ∧ ¬¬∃ δ, HG δ ∧ pair w δ ∈ e g ∧ γ ∈ succ δ) := by
    intro z α γ _ _ _
    refine sat_ex.trans ⟨nn_map fun ⟨w, hw, hs⟩ => ?_, nn_map fun ⟨w, hw, hwz, h⟩ => ?_⟩
    · have ⟨h1, h2⟩ := sat_and.1 hs
      refine ⟨w, hw, h1, nn_map (fun ⟨δ, hδ, hs'⟩ => ?_) (sat_ex.1 h2)⟩
      have ⟨h3, h4⟩ := sat_and.1 hs'
      exact ⟨δ, hδ, (sat_pairMem (e := Env.cons δ (Env.cons w (Env.cons γ (Env.cons α (Env.cons z e)))))
        (g := g+5) (a := 1) (b := 0) hw hδ).1 h3, mem_succ.2 (sat_or.1 h4)⟩
    · refine ⟨w, hw, sat_and.2 ⟨hwz, sat_ex.2 (nn_map (fun ⟨δ, hδ, hm, hγ⟩ => ?_) h)⟩⟩
      exact ⟨δ, hδ, sat_and.2 ⟨(sat_pairMem
        (e := Env.cons δ (Env.cons w (Env.cons γ (Env.cons α (Env.cons z e)))))
        (g := g+5) (a := 1) (b := 0) hw hδ).2 hm, sat_or.2 (mem_succ.1 hγ)⟩⟩
  constructor
  · intro h z hz α hα hzα γ hγ
    have := h z (ht.mem hz) hz α hα ((sat_pairMem (e := Env.cons α (Env.cons z e))
      (g := g+2) (a := 1) (b := 0) (ht.mem hz) hα).2 hzα) γ hγ
    exact (sat_iff.1 this).trans (inner z α γ (ht.mem hz) hα hγ)
  · intro h z hzH hz α hα hs γ hγ
    exact sat_iff.2 ((h z hz α hα ((sat_pairMem (e := Env.cons α (Env.cons z e))
      (g := g+2) (a := 1) (b := 0) hzH hα).1 hs) γ hγ).trans (inner z α γ hzH hα hγ).symm)

end

/-! ### The bridge -/

/-- **Rank is first-order over `HG`.** -/
theorem sat_rankFml {x ρ : PSet.{u}} {e : Nat → PSet.{u}} (hx : HG x) (hρ : HG ρ) :
    Sat HG rankFml (Env.cons x (Env.cons ρ e)) ↔ ρ ≈ rank x := by
  have body : ∀ T g, HG T → HG g →
      (Sat HG (and (mem 2 1) (and (transF 1) (and (totF 1 0) (and (funcF 1 0)
        (and (recF 1 0) (pairMem 0 2 3)))))) (Env.cons g (Env.cons T (Env.cons x (Env.cons ρ e)))) ↔
      x ∈ T ∧ (∀ z, z ∈ T → ∀ w, w ∈ z → w ∈ T) ∧
      (∀ z, z ∈ T → ¬¬∃ α, HG α ∧ pair z α ∈ g) ∧
      (∀ z, z ∈ T → ∀ α β, HG α → HG β → pair z α ∈ g → pair z β ∈ g → α ≈ β) ∧
      (∀ z, z ∈ T → ∀ α, HG α → pair z α ∈ g → ∀ γ, HG γ →
        (γ ∈ α ↔ ¬¬∃ w, HG w ∧ w ∈ z ∧ ¬¬∃ δ, HG δ ∧ pair w δ ∈ g ∧ γ ∈ succ δ)) ∧
      pair x ρ ∈ g) := by
    intro T g hT _
    let E := Env.cons g (Env.cons T (Env.cons x (Env.cons ρ e)))
    exact sat_and.trans (and_congr Iff.rfl (sat_and.trans (and_congr
      (sat_transF (e := E) (t := 1) hT) (sat_and.trans (and_congr
      (sat_totF (e := E) (t := 1) (g := 0) hT) (sat_and.trans (and_congr
      (sat_funcF (e := E) (t := 1) (g := 0) hT) (sat_and.trans (and_congr
      (sat_recF (e := E) (t := 1) (g := 0) hT)
      (sat_pairMem (e := E) (g := 0) (a := 2) (b := 3) hx hρ))))))))))
  constructor
  · intro h
    refine Stable.of_nn (sat_ex.1 h) fun ⟨T, hT, h⟩ =>
      Stable.of_nn (sat_ex.1 h) fun ⟨g, hg, h⟩ => ?_
    obtain ⟨hxT, htr, tot, _, rec, hxρ⟩ := (body T g hT hg).1 h
    exact rank_unique htr hT tot rec x hxT ρ hρ hxρ
  · intro eq
    have hT := hg_tclDom hx
    refine sat_ex.2 (nn_intro ⟨tclDom x, hT, sat_ex.2 (nn_intro ⟨rankGraph x, hg_rankGraph hx,
      (body _ _ hT (hg_rankGraph hx)).2 ⟨self_mem_tclDom x, fun _ hz _ hw => tclDom_trans hz hw,
        ?_, ?_, ?_, ?_⟩⟩)⟩)
    · exact fun z hz => nn_intro ⟨rank z, (hT.mem hz).rank, pair_rank_mem_rankGraph hz⟩
    · exact fun _ _ _ _ _ _ h1 h2 => (rankGraph_func h1).trans (rankGraph_func h2).symm
    · intro z hz α _ hzα γ _
      refine (mem_congr_right (rankGraph_func hzα)).trans (mem_rank'.trans ⟨?_, ?_⟩)
      · refine nn_map fun ⟨w, hw, hγ⟩ => ?_
        have hwT := tclDom_trans hz hw
        exact ⟨w, hT.mem hwT, hw,
          nn_intro ⟨rank w, (hT.mem hwT).rank, pair_rank_mem_rankGraph hwT, hγ⟩⟩
      · refine fun h => nn_bind h fun ⟨w, _, hw, h'⟩ => nn_map (fun ⟨_, _, hwδ, hγδ⟩ => ?_) h'
        exact ⟨w, hw, (mem_congr_right (succ_congr (rankGraph_func hwδ))).1 hγδ⟩
    · exact (mem_congr_left (pair_congr (Equiv.refl x) eq)).2
        (pair_rank_mem_rankGraph (self_mem_tclDom x))

/-- info: 'PSet.sat_rankFml' does not depend on any axioms -/
#guard_msgs in #print axioms sat_rankFml

end PSet
