import ConZF.NegCore
import ConZF.DecoderCap
/-!
The reviewer's Separation audit after con73 (checked against 7930428 and 1e1b6f6), incorporated
verbatim, with the earlier `sep_ex_bounds` statements kept as corollaries at the end. Nothing here
changes `NegCore`.

* **Conditional bounds.** A realizer of Separation by a **positive** existential `∃⁺y N(x, y)` with
  `N` negative gives, negatively, a native set with a witness for every successful input
  (`native_bound_of_success_sep`), all outputs for functional `N`; and more: **one** existing
  descriptor `q` whose value at `[x, e]` is a valid witness at every successful `x`
  (`uniform_descriptor_of_success_sep`). The forward implication returns the same output code at
  every input, and the Separation set's descriptor is substituted by the existing `letVar` closure.
  No Collection realizer, selection, or large elimination is used.
* **Rank-stage closure.** Every existing object operation preserves `V_η` for successor-closed `η`
  when the environment lies there (`eval_mem_vl`), including `sepNeg` with any matrix. `nextLimit α`
  is `α + ω`, successor-closed and containing `α`; no value in `V_{nextLimit α}` is a
  successor-closed ordinal containing `α` (`no_next_limit_in_stage`).
* **An explicit failed instance.** `request` is an actual negative formula, "`y` is a
  successor-closed ordinal containing slot `0`". At the all-`ω` environment it has the native
  witness `ω + ω` for every input (`request_total`), the separated subset is `ω` itself
  (`success_set_equiv_omega`), `{ω + ω}` is a native collecting set (`request_native_collection`),
  and **no code realizes** `sepAx 0 (.ex request)` (`no_positive_success_separation`).

The failure is reconstruction of the positive witness in the current object language, not the
existence of witnesses, of a collecting set, or of the separated subset. These are properties of
the current `Obj` grammar and the current `Realizes`. A grammar extension that passes this test
should revise the obstruction statements and keep a positive replacement test; the audit is not a
requirement that future implementations preserve the defect.
-/
universe u

namespace PSet.SuccessSepAudit
open NegCore

abbrev ident : Nat → Nat := fun n => n

theorem ex_read {N : IFml} (hN : Neg N) {σ : Nat → Nat} {e : Env.{u}}
    {c : RCode} (hc : Realizes (.ex N) σ e c) :
    ¬¬∃ q : Obj, Truth N (Env.cons (Obj.eval q e) (fun n => e (σ n))) := by
  refine nn_map (fun ⟨r⟩ => ?_) hc.1
  exact ⟨packObj r.1, (truth_congr N (cons_up_env σ e _)).1
    ((neg_reflect hN _ _).1 _ (hc.2 r))⟩

theorem ex_in_extension {N : IFml} (hN : Neg N) {σ : Nat → Nat}
    {e : Env.{u}} {y : PSet.{u}}
    (hy : Truth N (Env.cons y (fun n => e (σ n)))) :
    Realizes (.ex N) (fun n => Nat.succ (σ n)) (Env.cons y e)
      (.pack (.var 0) (canon N).lift) := by
  apply ex_intro_var
  apply (neg_reflect hN _ _).2
  exact (truth_congr N (fun n => by cases n <;> exact Equiv.refl _)).1 hy

abbrev sepBody (k : Nat) (N : IFml) : IFml :=
  .and (.imp (.mem 0 1) (.and (.mem 0 (k+2)) (N.rename sepR)))
    (.imp (.and (.mem 0 (k+2)) (N.rename sepR)) (.mem 0 1))

theorem successful_mem {N : IFml} (hN : Neg N) (k : Nat) (e : Env.{u})
    (S x : PSet.{u}) {c : RCode}
    (hc : Realizes (sepBody k (.ex N)) ident (Env.cons x (Env.cons S e)) c)
    (hx : x ∈ e k) (hy : ¬¬∃ y, Truth N (Env.cons y (Env.cons x e))) : x ∈ S := by
  refine Stable.of_nn hy fun ⟨y, hy⟩ => ?_
  have hb := and_snd hc
  have hN' : Truth (N.rename (Fml.up sepR))
      (Env.cons y (Env.cons x (Env.cons S e))) :=
    (truth_rename N (along_up (Equiv.refl y)
      (show Along sepR (Env.cons x e) (Env.cons x (Env.cons S e)) from
        fun n => by cases n <;> exact Equiv.refl _))).2 hy
  have hex := ex_in_extension (hN.rename (Fml.up sepR)) (σ := ident) hN'
  have hmem : Realizes (.mem 0 (k+2)) (fun n => Nat.succ (ident n))
      (Env.cons y (Env.cons x (Env.cons S e))) .tok := hx
  exact hb Nat.succ (Env.cons y (Env.cons x (Env.cons S e))) (along_succ _ _)
    _ (and_intro hmem hex)

theorem successful_descriptor {N : IFml} (hN : Neg N) (k : Nat) (e : Env.{u})
    (S x : PSet.{u}) {c : RCode}
    (hc : Realizes (sepBody k (.ex N)) ident (Env.cons x (Env.cons S e)) c)
    (hx : x ∈ e k) (hy : ¬¬∃ y, Truth N (Env.cons y (Env.cons x e))) :
    ¬¬∃ q : Obj, Truth N
      (Env.cons (Obj.eval q (Env.cons x (Env.cons S e))) (Env.cons x e)) := by
  have hs := successful_mem hN k e S x hc hx hy
  have hf := imp_elim (and_fst hc) (show Realizes (.mem 0 1) ident _ .tok from hs)
  have he := (realizes_rename (.ex N)).1 (and_snd hf)
  have hr := ex_read hN he
  exact nn_map (fun ⟨q, hq⟩ => ⟨q, (truth_congr N (fun n => by
    cases n with
    | zero => exact Equiv.refl _
    | succ n => cases n <;> exact Equiv.refl _)).1 hq⟩) hr

def candidates (a S : PSet.{u}) (e : Env.{u}) : PSet.{u} :=
  range fun iq : a.Idx × ULift.{u} Obj =>
    Obj.eval iq.2.down (Env.cons (a.Func iq.1) (Env.cons S e))

theorem candidates_cover {N : IFml} (hN : Neg N) (k : Nat) (e : Env.{u})
    (S : PSet.{u})
    (hbody : ∀ x, ¬¬∃ c, Realizes (sepBody k (.ex N)) ident
      (Env.cons x (Env.cons S e)) c) :
    ∀ x, x ∈ e k → (¬¬∃ y, Truth N (Env.cons y (Env.cons x e))) →
      ¬¬∃ y, y ∈ candidates (e k) S e ∧ Truth N (Env.cons y (Env.cons x e)) := by
  intro x hx hy
  refine hx.elim fun i hi => ?_
  have hy' : ¬¬∃ y, Truth N (Env.cons y (Env.cons ((e k).Func i) e)) :=
    nn_map (fun ⟨y, h⟩ => ⟨y, (truth_congr N (fun n => by
      cases n with
      | zero => exact Equiv.refl _
      | succ n => cases n with
        | zero => exact hi
        | succ n => exact Equiv.refl _)).1 h⟩) hy
  refine nn_bind (hbody ((e k).Func i)) fun ⟨c, hc⟩ => ?_
  refine nn_map (fun ⟨q, hq⟩ => ?_)
    (successful_descriptor hN k e S ((e k).Func i) hc (func_mem _ _) hy')
  refine ⟨_, func_mem (candidates (e k) S e) (i, ⟨q⟩), ?_⟩
  exact (truth_congr N (fun n => by
    cases n with
    | zero => exact Equiv.refl _
    | succ n => cases n with
      | zero => exact hi.symm
      | succ n => exact Equiv.refl _)).1 hq

theorem native_bound_of_success_sep {N : IFml} (hN : Neg N) (k : Nat) (e : Env.{u})
    {c : RCode} (hc : Realizes (sepAx k (.ex N)) ident e c) :
    ¬¬∃ b : PSet.{u}, ∀ x, x ∈ e k →
      (¬¬∃ y, Truth N (Env.cons y (Env.cons x e))) →
      ¬¬∃ y, y ∈ b ∧ Truth N (Env.cons y (Env.cons x e)) := by
  refine nn_bind hc.1 fun ⟨r⟩ => ?_
  let S := Obj.eval (packObj r.1) e
  have hb := hc.2 r
  have hbody : ∀ x, ¬¬∃ d, Realizes (sepBody k (.ex N)) ident
      (Env.cons x (Env.cons S e)) d := fun x =>
    nn_map (fun ⟨s⟩ => ⟨genBody s.1,
      realizes_congr_σ _ (fun n => by cases n with
        | zero => rfl
        | succ n => cases n <;> rfl) ((hb x).2 s)⟩) (hb x).1
  exact nn_intro ⟨candidates (e k) S e, candidates_cover hN k e S hbody⟩

theorem native_functional_bound_of_success_sep {N : IFml} (hN : Neg N)
    (k : Nat) (e : Env.{u}) {c : RCode}
    (hc : Realizes (sepAx k (.ex N)) ident e c)
    (hfunc : ∀ x y z, Truth N (Env.cons y (Env.cons x e)) →
      Truth N (Env.cons z (Env.cons x e)) → y ≈ z) :
    ¬¬∃ b : PSet.{u}, ∀ x, x ∈ e k → ∀ y,
      Truth N (Env.cons y (Env.cons x e)) → y ∈ b := by
  refine nn_map (fun ⟨b, hb⟩ => ⟨b, fun x hx y hy => ?_⟩)
    (native_bound_of_success_sep hN k e hc)
  exact Stable.of_nn (hb x hx (nn_intro ⟨y, hy⟩)) fun ⟨z, hz, hzy⟩ =>
    (mem_congr_left (hfunc x y z hy hzy)).2 hz

/-- A fixed Separation body uses a single existential-output code at every input. -/
theorem fixed_output {N : IFml} (hN : Neg N) (k : Nat) (e : Env.{u})
    (S x : PSet.{u}) {c : RCode}
    (hc : Realizes (sepBody k (.ex N)) ident (Env.cons x (Env.cons S e)) c)
    (hx : x ∈ e k) (hy : ¬¬∃ y, Truth N (Env.cons y (Env.cons x e))) :
    Realizes (.ex N) sepR (Env.cons x (Env.cons S e))
      (.snd (.app (.fst c) .tok)) := by
  have hs := successful_mem hN k e S x hc hx hy
  have hf := imp_elim (and_fst hc)
    (show Realizes (.mem 0 1) ident (Env.cons x (Env.cons S e)) .tok from hs)
  exact (realizes_rename (.ex N) (ρ := sepR) (σ := ident)).1 (and_snd hf)

/-- The positive Separation realizer actually gives one descriptor working for all successful
inputs. Only the existence of that descriptor is negative. -/
theorem uniform_descriptor_of_success_sep {N : IFml} (hN : Neg N)
    (k : Nat) (e : Env.{u}) {c : RCode}
    (hc : Realizes (sepAx k (.ex N)) ident e c) :
    ¬¬∃ q : Obj, ∀ x, x ∈ e k →
      (¬¬∃ y, Truth N (Env.cons y (Env.cons x e))) →
      Truth N (Env.cons (Obj.eval q (Env.cons x e)) (Env.cons x e)) := by
  refine nn_bind hc.1 fun ⟨r⟩ => ?_
  let qS := packObj r.1
  let S := Obj.eval qS e
  have hb := hc.2 r
  refine nn_bind (hb empty).1 fun ⟨s⟩ => ?_
  have hbody (x : PSet.{u}) : Realizes (sepBody k (.ex N)) ident
      (Env.cons x (Env.cons S e)) (genBody s.1) :=
    realizes_congr_σ _ (fun n => by cases n with
      | zero => rfl
      | succ n => cases n <;> rfl) ((hb x).2 s)
  let Success : Prop := ∃ x, x ∈ e k ∧ ¬¬∃ y, Truth N (Env.cons y (Env.cons x e))
  refine Stable.by_cases Success (fun hs => ?_) (fun hs => ?_)
  · rcases hs with ⟨x, hx, hy⟩
    have hf := fixed_output hN k e S x (hbody x) hx hy
    refine nn_map (fun ⟨t⟩ => ?_) hf.1
    let q := packObj t.1
    refine ⟨.letVar qS.lift (q.rename swap), fun z hz hzy => ?_⟩
    have hr := (fixed_output hN k e S z (hbody z) hz hzy).2 t
    have hn := (truth_congr N (cons_up_env sepR (Env.cons z (Env.cons S e)) _)).1
      ((neg_reflect hN _ _).1 _ hr)
    have heq : Obj.eval (.letVar qS.lift (q.rename swap)) (Env.cons z e) ≈
        Obj.eval q (Env.cons z (Env.cons S e)) := by
      change Obj.eval (q.rename swap) (Env.cons (Obj.eval qS.lift (Env.cons z e)) (Env.cons z e)) ≈ _
      exact Obj.eval_rename q (along_swap (e := e) (y := z)
        (Obj.eval_rename qS (along_succ z e)).symm)
    exact (truth_congr N (fun n => by
      cases n with
      | zero => exact heq.symm
      | succ n => cases n <;> exact Equiv.refl _)).1 hn
  · exact nn_intro ⟨.emp, fun x hx hy => (hs ⟨x, hx, hy⟩).elim⟩

/-- info: 'PSet.SuccessSepAudit.ex_read' does not depend on any axioms -/
#guard_msgs in #print axioms ex_read
/-- info: 'PSet.SuccessSepAudit.ex_in_extension' does not depend on any axioms -/
#guard_msgs in #print axioms ex_in_extension
/-- info: 'PSet.SuccessSepAudit.successful_mem' does not depend on any axioms -/
#guard_msgs in #print axioms successful_mem
/-- info: 'PSet.SuccessSepAudit.successful_descriptor' does not depend on any axioms -/
#guard_msgs in #print axioms successful_descriptor
/-- info: 'PSet.SuccessSepAudit.candidates_cover' does not depend on any axioms -/
#guard_msgs in #print axioms candidates_cover
/-- info: 'PSet.SuccessSepAudit.native_bound_of_success_sep' does not depend on any axioms -/
#guard_msgs in #print axioms native_bound_of_success_sep
/-- info: 'PSet.SuccessSepAudit.native_functional_bound_of_success_sep' does not depend on any axioms -/
#guard_msgs in #print axioms native_functional_bound_of_success_sep
/-- info: 'PSet.SuccessSepAudit.fixed_output' does not depend on any axioms -/
#guard_msgs in #print axioms fixed_output
/-- info: 'PSet.SuccessSepAudit.uniform_descriptor_of_success_sep' does not depend on any axioms -/
#guard_msgs in #print axioms uniform_descriptor_of_success_sep

end PSet.SuccessSepAudit


/-! ### Rank-stage closure of the current grammar

Scope: the existing `Obj` constructors. The native universe itself has the witness constructed
below. -/
namespace PSet.DescriptorLimitAudit
open NegCore OrdDecode

/-- Every existing object operation preserves a successor-closed rank stage, provided all
environment values lie in that stage. This includes Separation by arbitrary native Truth. -/
theorem eval_mem_vl {η : PSet.{u}} (hη : SuccClosed η) :
    ∀ (q : Obj) (e : Env.{u}), (∀ n, e n ∈ Vl η) → Obj.eval q e ∈ Vl η
  | .var n, e, he => he n
  | .emp, e, he => empty_vl hη.ord (he 0)
  | .upair q r, e, he => upair_vl hη (eval_mem_vl hη q e he) (eval_mem_vl hη r e he)
  | .sUnion q, e, he => sUnion_vl hη.ord (eval_mem_vl hη q e he)
  | .pow q, e, he => powerset_vl hη (eval_mem_vl hη q e he)
  | .sepNeg q N, e, he => subset_vl hη.ord (eval_mem_vl hη q e he)
      fun z hz => ((mem_sep (truth_cons_resp N e)).1 hz).1
  | .letVar q r, e, he => eval_mem_vl hη r (Env.cons (Obj.eval q e) e) (fun n => by
      cases n with
      | zero => exact eval_mem_vl hη q e he
      | succ n => exact he n)

/-- Native construction of alpha + omega. -/
def nextLimit (α : PSet.{u}) : PSet.{u} :=
  iUnion (ι := ULift.{u} Nat) fun n => succN n.down α

theorem nextLimit_ord {α : PSet.{u}} (hα : IsOrd α) : IsOrd (nextLimit α) :=
  isOrd_iUnion fun n => hα.succN n.down

theorem mem_nextLimit (α : PSet.{u}) : α ∈ nextLimit α :=
  mem_iUnion.2 (nn_intro ⟨⟨1⟩, self_mem_succ α⟩)

theorem nextLimit_closed {α : PSet.{u}} (hα : IsOrd α) : SuccClosed (nextLimit α) := by
  refine ⟨nextLimit_ord hα, fun x hx => ?_⟩
  refine Stable.of_nn (mem_iUnion.1 hx) fun ⟨n, hn⟩ => ?_
  refine mem_iUnion.2 (nn_intro ⟨⟨n.down + 1⟩, ?_⟩)
  apply ((hα.succN n.down).mem hn).succ.mem_succ_of_subset (hα.succN n.down)
  intro z hz
  exact Stable.of_nn (mem_succ.1 hz) fun
    | .inl hz => (hα.succN n.down).trans x hn z hz
    | .inr hz => (mem_congr_left hz).2 hn

theorem nextLimit_subset {α y : PSet.{u}} (hy : SuccClosed y) (hα : α ∈ y) :
    ∀ z, z ∈ nextLimit α → z ∈ y := by
  have hs : ∀ n, succN n α ∈ y := fun n => by
    induction n with
    | zero => exact hα
    | succ n ih => exact hy.next _ ih
  intro z hz
  exact Stable.of_nn (mem_iUnion.1 hz) fun ⟨n, hn⟩ => hy.ord.trans _ (hs n.down) z hn

/-- No value in this rank stage is a successor-closed ordinal containing alpha. -/
theorem no_next_limit_in_stage {α y : PSet.{u}} (hα : IsOrd α)
    (hy : y ∈ Vl (nextLimit α)) (hord : SuccClosed y) (ha : α ∈ y) : False := by
  have hylevel : y ∈ nextLimit α := (mem_congr_left hord.ord.rank_equiv).1
    ((mem_Vl_ord (nextLimit_ord hα)).1 hy)
  exact not_mem_self y (nextLimit_subset hord ha y hylevel)

/-- A native witness exists, but none is the evaluation of a current descriptor whose environment
lies below the first successor-closed ordinal above alpha. -/
theorem no_descriptor_next_limit {α : PSet.{u}} (hα : IsOrd α) (e : Env.{u})
    (he : ∀ n, e n ∈ Vl (nextLimit α)) (q : Obj) :
    ¬ (SuccClosed (Obj.eval q e) ∧ α ∈ Obj.eval q e) :=
  fun h => no_next_limit_in_stage hα (eval_mem_vl (nextLimit_closed hα) q e he) h.1 h.2

theorem omega_witness_exists : ∃ y : PSet.{u}, SuccClosed y ∧ omega ∈ y :=
  ⟨nextLimit omega, nextLimit_closed isOrd_omega, mem_nextLimit omega⟩

/-- Even an environment containing omega at every slot cannot express a successor-closed ordinal
strictly above omega using the current Obj constructors. -/
theorem no_descriptor_above_omega (q : Obj) :
    ¬ (SuccClosed (Obj.eval q (fun _ => omega.{u})) ∧
      omega ∈ Obj.eval q (fun _ => omega.{u})) :=
  no_descriptor_next_limit isOrd_omega (fun _ => omega)
    (fun _ => ordinal_vl (nextLimit_ord isOrd_omega) isOrd_omega (mem_nextLimit omega)) q

/-- info: 'PSet.DescriptorLimitAudit.eval_mem_vl' does not depend on any axioms -/
#guard_msgs in #print axioms eval_mem_vl
/-- info: 'PSet.DescriptorLimitAudit.nextLimit_ord' does not depend on any axioms -/
#guard_msgs in #print axioms nextLimit_ord
/-- info: 'PSet.DescriptorLimitAudit.mem_nextLimit' does not depend on any axioms -/
#guard_msgs in #print axioms mem_nextLimit
/-- info: 'PSet.DescriptorLimitAudit.nextLimit_closed' does not depend on any axioms -/
#guard_msgs in #print axioms nextLimit_closed
/-- info: 'PSet.DescriptorLimitAudit.nextLimit_subset' does not depend on any axioms -/
#guard_msgs in #print axioms nextLimit_subset
/-- info: 'PSet.DescriptorLimitAudit.no_next_limit_in_stage' does not depend on any axioms -/
#guard_msgs in #print axioms no_next_limit_in_stage
/-- info: 'PSet.DescriptorLimitAudit.no_descriptor_next_limit' does not depend on any axioms -/
#guard_msgs in #print axioms no_descriptor_next_limit
/-- info: 'PSet.DescriptorLimitAudit.omega_witness_exists' does not depend on any axioms -/
#guard_msgs in #print axioms omega_witness_exists
/-- info: 'PSet.DescriptorLimitAudit.no_descriptor_above_omega' does not depend on any axioms -/
#guard_msgs in #print axioms no_descriptor_above_omega

end PSet.DescriptorLimitAudit

namespace PSet.SuccessSepCounterexample
open NegCore OrdDecode DescriptorLimitAudit SuccessSepAudit

def transF (n : Nat) : IFml :=
  .all (.imp (.mem 0 (n+1)) (.all (.imp (.mem 0 1) (.mem 0 (n+2)))))

def ordF (n : Nat) : IFml :=
  .and (transF n) (.all (.imp (.mem 0 (n+1)) (transF 0)))

/-- Negative expression of: every member has a strictly larger member. -/
def noMaxF (n : Nat) : IFml :=
  .all (.imp (.mem 0 (n+1))
    (.imp (.all (.imp (.and (.mem 0 (n+2)) (.mem 1 0)) .fls)) .fls))

/-- In environment [y,x,ambient...], y is a successor-closed ordinal containing ambient slot 0.
The input x is intentionally unused. -/
def request : IFml := .and (ordF 0) (.and (.mem 2 0) (noMaxF 0))

theorem transF_neg (n : Nat) : Neg (transF n) :=
  .all (.imp (.mem _ _) (.all (.imp (.mem _ _) (.mem _ _))))

theorem ordF_neg (n : Nat) : Neg (ordF n) :=
  .and (transF_neg n) (.all (.imp (.mem _ _) (transF_neg 0)))

theorem noMaxF_neg (n : Nat) : Neg (noMaxF n) :=
  .all (.imp (.mem _ _) (.imp (.all (.imp (.and (.mem _ _) (.mem _ _)) .fls)) .fls))

theorem request_neg : Neg request :=
  .and (ordF_neg 0) (.and (.mem _ _) (noMaxF_neg 0))

theorem transF_read (n : Nat) (e : Env.{u}) : Truth (transF n) e ↔ Trans (e n) := Iff.rfl

theorem ordF_read (n : Nat) (e : Env.{u}) : Truth (ordF n) e ↔ IsOrd (e n) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem noMaxF_read (n : Nat) (e : Env.{u}) : Truth (noMaxF n) e ↔
    ∀ x, x ∈ e n → ¬¬∃ z, z ∈ e n ∧ x ∈ z :=
  ⟨fun h x hx hn => h x hx (fun z hz => hn ⟨z, hz⟩),
    fun h x hx hn => h x hx (fun ⟨z, hz⟩ => hn z hz)⟩

theorem request_read (y x : PSet.{u}) (e : Env.{u}) :
    Truth request (Env.cons y (Env.cons x e)) ↔ SuccClosed y ∧ e 0 ∈ y := by
  constructor
  · intro h
    have ho := (ordF_read 0 _).1 h.1
    have hn := (noMaxF_read 0 _).1 h.2.2
    refine ⟨⟨ho, fun z hz => ?_⟩, h.2.1⟩
    refine Stable.of_nn (hn z hz) fun ⟨w, hw, hzw⟩ => ?_
    refine below_of_le ho (?_ : succ z ∈ succ w) hw
    apply (ho.mem hz).succ.mem_succ_of_subset (ho.mem hw)
    intro t ht
    exact Stable.of_nn (mem_succ.1 ht) fun
      | .inl ht => (ho.mem hw).trans z hzw t ht
      | .inr ht => (mem_congr_left ht).2 hzw
  · rintro ⟨hy, ha⟩
    refine ⟨(ordF_read 0 _).2 hy.ord, ha, (noMaxF_read 0 _).2 ?_⟩
    exact fun z hz => nn_intro ⟨succ z, hy.next z hz, self_mem_succ z⟩

def omegaEnv : Env.{u} := fun _ => omega

/-- This particular negative request has an unconditional native witness for every input. -/
theorem request_total (x : PSet.{u}) :
    ∃ y, Truth request (Env.cons y (Env.cons x omegaEnv)) :=
  ⟨nextLimit omega, (request_read _ _ _).2
    ⟨nextLimit_closed isOrd_omega, mem_nextLimit omega⟩⟩

/-- The desired native separated subset is just omega, so naming the subset is not the failure. -/
theorem success_set_equiv_omega :
    sep (fun x => Truth (.ex request) (Env.cons x omegaEnv.{u})) omega ≈ omega := by
  refine ext fun x => ⟨fun hx => ((mem_sep (truth_cons_resp (.ex request) omegaEnv)).1 hx).1,
    fun hx => (mem_sep (truth_cons_resp (.ex request) omegaEnv)).2 ?_⟩
  exact ⟨hx, nn_intro (request_total x)⟩

/-- The native Collection conclusion has an explicit singleton witness for this request. -/
theorem request_native_collection :
    ∃ b : PSet.{u}, ∀ x, x ∈ omega → ∃ y, y ∈ b ∧
      Truth request (Env.cons y (Env.cons x omegaEnv)) :=
  ⟨singleton (nextLimit omega), fun x _ => ⟨nextLimit omega, self_mem_singleton _,
    (request_read _ x _).2 ⟨nextLimit_closed isOrd_omega, mem_nextLimit omega⟩⟩⟩

/-- The original object grammar cannot realize the positive-success Separation instance for
this request, even though the native relation is everywhere inhabited. This is scoped to the
current grammar and Realizes, not to an extension or another interpretation. -/
theorem no_positive_success_separation (c : RCode) :
    ¬ Realizes (sepAx 0 (.ex request)) ident omegaEnv.{u} c := by
  intro hc
  refine (uniform_descriptor_of_success_sep request_neg 0 omegaEnv hc) fun ⟨q, hq⟩ => ?_
  have hw := hq empty (ofNat_mem_omega 0) (nn_intro (request_total empty))
  have ho := (request_read _ empty omegaEnv).1 hw
  have homega : omega.{u} ∈ Vl (nextLimit omega) :=
    ordinal_vl (nextLimit_ord isOrd_omega) isOrd_omega (mem_nextLimit omega)
  have henv : ∀ n, Env.cons empty omegaEnv n ∈ Vl (nextLimit omega) := fun n => by
    cases n with
    | zero => exact empty_vl (nextLimit_ord isOrd_omega) homega
    | succ n => exact homega
  exact no_descriptor_next_limit isOrd_omega (Env.cons empty omegaEnv) henv q ho

/-- info: 'PSet.SuccessSepCounterexample.transF_neg' does not depend on any axioms -/
#guard_msgs in #print axioms transF_neg
/-- info: 'PSet.SuccessSepCounterexample.ordF_neg' does not depend on any axioms -/
#guard_msgs in #print axioms ordF_neg
/-- info: 'PSet.SuccessSepCounterexample.noMaxF_neg' does not depend on any axioms -/
#guard_msgs in #print axioms noMaxF_neg
/-- info: 'PSet.SuccessSepCounterexample.request_neg' does not depend on any axioms -/
#guard_msgs in #print axioms request_neg
/-- info: 'PSet.SuccessSepCounterexample.transF_read' does not depend on any axioms -/
#guard_msgs in #print axioms transF_read
/-- info: 'PSet.SuccessSepCounterexample.ordF_read' does not depend on any axioms -/
#guard_msgs in #print axioms ordF_read
/-- info: 'PSet.SuccessSepCounterexample.noMaxF_read' does not depend on any axioms -/
#guard_msgs in #print axioms noMaxF_read
/-- info: 'PSet.SuccessSepCounterexample.request_read' does not depend on any axioms -/
#guard_msgs in #print axioms request_read
/-- info: 'PSet.SuccessSepCounterexample.request_total' does not depend on any axioms -/
#guard_msgs in #print axioms request_total
/-- info: 'PSet.SuccessSepCounterexample.success_set_equiv_omega' does not depend on any axioms -/
#guard_msgs in #print axioms success_set_equiv_omega
/-- info: 'PSet.SuccessSepCounterexample.request_native_collection' does not depend on any axioms -/
#guard_msgs in #print axioms request_native_collection
/-- info: 'PSet.SuccessSepCounterexample.no_positive_success_separation' does not depend on any axioms -/
#guard_msgs in #print axioms no_positive_success_separation

end PSet.SuccessSepCounterexample

/-! ### The earlier statements, as corollaries -/

namespace PSet.SepBoundingAudit
open NegCore

/-- The native range of every descriptor value at `[a.Func i, S, e]`, over literal `i` and `q`. -/
abbrev candidates := @SuccessSepAudit.candidates

theorem sep_ex_bounds {N : IFml} (hN : Neg N) (k : Nat) (e : Env.{u}) {c : RCode}
    (hc : Realizes (sepAx k (.ex N)) (fun n => n) e c) :
    ¬¬∃ b : PSet.{u}, ∀ x, x ∈ e k → (¬¬∃ y, Truth N (Env.cons y (Env.cons x e))) →
      ¬¬∃ y, y ∈ b ∧ Truth N (Env.cons y (Env.cons x e)) :=
  SuccessSepAudit.native_bound_of_success_sep hN k e hc

theorem sep_ex_bounds_functional {N : IFml} (hN : Neg N) (k : Nat) (e : Env.{u}) {c : RCode}
    (hc : Realizes (sepAx k (.ex N)) (fun n => n) e c)
    (func : ∀ x y y', Truth N (Env.cons y (Env.cons x e)) → Truth N (Env.cons y' (Env.cons x e)) → y ≈ y') :
    ¬¬∃ b : PSet.{u}, ∀ x, x ∈ e k → ∀ y, Truth N (Env.cons y (Env.cons x e)) → y ∈ b :=
  SuccessSepAudit.native_functional_bound_of_success_sep hN k e hc func

/-- info: 'PSet.SepBoundingAudit.sep_ex_bounds' does not depend on any axioms -/
#guard_msgs in #print axioms sep_ex_bounds
/-- info: 'PSet.SepBoundingAudit.sep_ex_bounds_functional' does not depend on any axioms -/
#guard_msgs in #print axioms sep_ex_bounds_functional

end PSet.SepBoundingAudit
