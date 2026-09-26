import ConZF.Audit.SepBounding
import ConZF.DecoderLocal
import ConZF.Audit.Certificate
/-!
The exact decoder instance of the rank-stage obstruction (nc2 §6), checked. Nothing here changes
`NegCore` or asserts a forcing relation.

`ω + ω` (`nextLimit ω`) injects into `ω` by an explicit pure graph tagging the two copies of `ℕ`
with the checked Cantor pairing (`emb_lam_omega`), so it is decoded from some diagram over `ω`
(`diagram_of_emb`) and is not a barrier. Let `N` be the structural embedding of the source
`rename cA decodeF` into the negative fragment, so `N` at `[y, x, …]` is "`x` decodes `y`"
(`truthN_iff`). At `e₀ = [diagrams ω, ω, ∅, ∅, …]`, every environment entry lies in `V_{ω+ω}`, hence
so does every descriptor value; the uniform-descriptor theorem would then name the decoded ordinal
`ω + ω` inside `V_{ω+ω}`. Therefore **no code realizes** `sepAx 0 (.ex N)` at `e₀`
(`no_decoder_success_separation`), and the generic stage obstruction shows nc2's bottom-certificate
clause cannot be met from the readbacks at `e₀` (`decoder_env_not_refutes`).

Scope: the current `Obj` grammar and the current `Realizes` at this environment. It rules out
neither positive Separation after a justified grammar or environment extension nor an
interpretation changing atoms or domains; full forcing non-refutation additionally needs that
forcing's canonical-assumption theorem, which is not established here.
-/
universe u

namespace PSet.DecoderObstructionAudit
open NegCore OrdDecode DescriptorLimitAudit SuccessSepAudit DecoderLocal

/-! ### `ω + ω` injects into `ω` -/

/-- The two copies of `ℕ`: finite ordinals and the finite successors of `ω`. -/
def tag : Bool × Nat → PSet.{u}
  | (false, n) => ofNat n
  | (true, m) => succN m omega

/-- Their codes, by the checked Cantor pairing. -/
def code : Bool × Nat → Nat
  | (false, n) => Code.pair 0 n
  | (true, m) => Code.pair 1 m

def lam : PSet.{u} := nextLimit omega

theorem lam_ord : IsOrd lam.{u} := nextLimit_ord isOrd_omega
theorem lam_closed : SuccClosed lam.{u} := nextLimit_closed isOrd_omega

theorem omega_mem_succN : ∀ m, omega.{u} ∈ succN (m+1) omega
  | 0 => self_mem_succ _
  | m+1 => mem_succ.2 (nn_intro (.inl (omega_mem_succN m)))

theorem succN_not_mem_omega : ∀ m, ¬ succN m omega.{u} ∈ omega
  | 0 => not_mem_self _
  | m+1 => fun h => mem_asymm _ (omega_mem_succN m) h

theorem succN_inj : ∀ {m m' : Nat}, succN m omega.{u} ≈ succN m' omega → m = m'
  | 0, 0, _ => rfl
  | 0, m'+1, h => (succN_not_mem_omega m' ((mem_congr_right h).2 (self_mem_succ _))).elim
  | m+1, 0, h => (succN_not_mem_omega m ((mem_congr_right h).1 (self_mem_succ _))).elim
  | _+1, _+1, h => congrArg (· + 1) (succN_inj (succ_inj h))

theorem tag_inj : ∀ {t t' : Bool × Nat}, tag.{u} t ≈ tag t' → t = t'
  | (false, _), (false, _), h => congrArg (Prod.mk false) (ofNat_inj h)
  | (false, n), (true, m), h => (succN_not_mem_omega m ((mem_congr_left h).1 (ofNat_mem_omega n))).elim
  | (true, m), (false, n), h => (succN_not_mem_omega m ((mem_congr_left h).2 (ofNat_mem_omega n))).elim
  | (true, _), (true, _), h => congrArg (Prod.mk true) (succN_inj h)

theorem code_inj : ∀ {t t' : Bool × Nat}, code t = code t' → t = t'
  | (false, _), (false, _), h => congrArg (Prod.mk false) (Code.pair_inj h).2
  | (false, _), (true, _), h => absurd (Code.pair_inj h).1 (by decide)
  | (true, _), (false, _), h => absurd (Code.pair_inj h).1 (by decide)
  | (true, _), (true, _), h => congrArg (Prod.mk true) (Code.pair_inj h).2

theorem tag_mem_lam : ∀ t : Bool × Nat, tag.{u} t ∈ lam
  | (false, n) => mem_iUnion.2 (nn_intro ⟨⟨0⟩, ofNat_mem_omega n⟩)
  | (true, m) => mem_iUnion.2 (nn_intro ⟨⟨m+1⟩, self_mem_succ _⟩)

theorem mem_succN_tag : ∀ (m : Nat) {i : PSet.{u}}, i ∈ succN m omega → ¬¬∃ t, i ≈ tag t
  | 0, _, hn => nn_map (fun ⟨k, hk⟩ => ⟨(false, k), hk⟩) (mem_omega.1 hn)
  | m+1, _, hn => nn_bind (mem_succ.1 hn) fun
      | .inl h => mem_succN_tag m h
      | .inr h => nn_intro ⟨(true, m), h⟩

/-- Every element of `ω + ω` is (negatively) a tag. -/
theorem mem_lam_tag {i : PSet.{u}} (hi : i ∈ lam) : ¬¬∃ t, i ≈ tag t :=
  nn_bind (mem_iUnion.1 hi) fun ⟨n, hn⟩ => mem_succN_tag n.down hn

/-- The graph `t ↦ ⟨tag t, ofNat (code t)⟩`. -/
def injGraph : PSet.{u} := range fun t : ULift.{u} (Bool × Nat) => pair (tag t.down) (ofNat (code t.down))

theorem mem_injGraph {q : PSet.{u}} : q ∈ injGraph ↔ ¬¬∃ t : Bool × Nat, q ≈ pair (tag t) (ofNat (code t)) :=
  ⟨nn_map fun ⟨t, h⟩ => ⟨t.down, h⟩, nn_map fun ⟨t, h⟩ => ⟨⟨t⟩, h⟩⟩

theorem injGraph_oinj : OInj injGraph.{u} lam omega := by
  refine ⟨⟨fun q hq => ?_, fun i hi => ?_, fun i v v' hv hv' => ?_⟩, fun i j v w hiv hjw evw => ?_⟩
  · exact nn_map (fun ⟨t, h⟩ => ⟨tag t, ofNat (code t), tag_mem_lam t, ofNat_mem_omega _, h⟩) (mem_injGraph.1 hq)
  · exact nn_map (fun ⟨t, ht⟩ => ⟨ofNat (code t), mem_injGraph.2 (nn_intro ⟨t, pair_congr ht (Equiv.refl _)⟩)⟩)
      (mem_lam_tag hi)
  · refine Stable.of_nn (mem_injGraph.1 hv) fun ⟨t, ht⟩ => Stable.of_nn (mem_injGraph.1 hv') fun ⟨t', ht'⟩ => ?_
    have e := tag_inj ((pair_inj ht).1.symm.trans (pair_inj ht').1)
    subst e
    exact (pair_inj ht).2.trans (pair_inj ht').2.symm
  · refine Stable.of_nn (mem_injGraph.1 hiv) fun ⟨t, ht⟩ => Stable.of_nn (mem_injGraph.1 hjw) fun ⟨t', ht'⟩ => ?_
    have e := code_inj (ofNat_inj ((pair_inj ht).2.symm.trans (evw.trans (pair_inj ht').2)))
    subst e
    exact (pair_inj ht).1.trans (pair_inj ht').1.symm

theorem emb_lam_omega : Emb lam.{u} omega := nn_intro ⟨injGraph, injGraph_oinj⟩

/-- `ω + ω` is decoded from some diagram over `ω`; it is not a barrier. -/
theorem lam_decoded : ¬¬∃ d, d ∈ diagrams omega.{u} ∧ Decoded d lam := diagram_of_emb lam_ord emb_lam_omega

/-! ### The source decoder in the negative fragment -/

def embed : Fml → IFml
  | .mem i j => .mem i j
  | .eq i j => .eq i j
  | .fls => .fls
  | .imp a b => .imp (embed a) (embed b)
  | .all a => .all (embed a)

theorem embed_neg : ∀ φ : Fml, Neg (embed φ)
  | .mem _ _ => .mem _ _
  | .eq _ _ => .eq _ _
  | .fls => .fls
  | .imp a b => .imp (embed_neg a) (embed_neg b)
  | .all a => .all (embed_neg a)

theorem truth_embed : ∀ (φ : Fml) (e : Env.{u}), Truth (embed φ) e ↔ Sat (fun _ => True) φ e
  | .mem _ _, _ => Iff.rfl
  | .eq _ _, _ => Iff.rfl
  | .fls, _ => Iff.rfl
  | .imp a b, e => ⟨fun h ha => (truth_embed b e).1 (h ((truth_embed a e).2 ha)),
      fun h ha => (truth_embed b e).2 (h ((truth_embed a e).1 ha))⟩
  | .all a, _ => ⟨fun h x _ => (truth_embed a _).1 (h x), fun h x => (truth_embed a _).2 (h x trivial)⟩

/-- The decoder with its slots swapped to the Separation convention `[y, x, …]`. -/
def N : IFml := embed (Fml.rename ZFAx.cA decodeF)

theorem truthN_iff (y x : PSet.{u}) (e : Env.{u}) : Truth N (Env.cons y (Env.cons x e)) ↔ Decoded x y :=
  (truth_embed _ _).trans ((sat_rename decodeF ZFAx.cA _).trans
    ((Sat.resp_iff (fun _ => Iff.rfl) decodeF (fun i => by rcases i with _ | _ | i <;> exact Equiv.refl _)).trans
      (sat_decodeF_true x y e)))

/-! ### The environment and the obstruction -/

def e0 : Env.{u} := Env.cons (diagrams omega) (Env.cons omega fun _ => empty)

theorem omega_vl : omega.{u} ∈ Vl lam := ordinal_vl lam_ord isOrd_omega (mem_nextLimit omega)

theorem e0_vl : ∀ n, e0.{u} n ∈ Vl lam
  | 0 => product_vl lam_closed (powerset_vl lam_closed omega_vl)
      (powerset_vl lam_closed (product_vl lam_closed omega_vl omega_vl))
  | 1 => omega_vl
  | _+2 => empty_vl lam_ord omega_vl

/-- **No code realizes the positive-existential Separation instance for the decoder at `e₀`.** -/
theorem no_decoder_success_separation (c : RCode) : ¬ Realizes (sepAx 0 (.ex N)) (fun n => n) e0.{u} c := by
  intro hc
  refine uniform_descriptor_of_success_sep (embed_neg _) 0 e0 hc fun ⟨q, hq⟩ => ?_
  refine lam_decoded fun ⟨d, hd, hdec⟩ => ?_
  have hw := hq d hd (nn_intro ⟨lam, (truthN_iff lam d _).2 hdec⟩)
  have hy : Decoded d (Obj.eval q (Env.cons d e0)) := (truthN_iff _ d _).1 hw
  have hyv : Obj.eval q (Env.cons d e0) ∈ Vl lam := eval_mem_vl lam_closed q _ fun
    | 0 => Vl_trans (e0_vl 0) hd
    | n+1 => e0_vl n
  have hl : lam.{u} ∈ Vl lam := (mem_congr_left (decoded_unique hy hdec)).1 hyv
  exact not_mem_self lam ((mem_congr_left lam_ord.rank_equiv).1 ((mem_Vl_ord lam_ord).1 hl))

/-- nc2's bottom-certificate clause cannot be met from the descriptor readbacks at `e₀`. -/
theorem decoder_env_not_refutes :
    ¬ CertificateAudit.refutes (fun q : ULift.{u} Obj => Obj.eval q.down e0) omega :=
  CertificateAudit.not_refutes_of_stage _ omega lam lam_ord emb_lam_omega fun q =>
    eval_mem_vl lam_closed q.down e0 e0_vl

/-- info: 'PSet.DecoderObstructionAudit.injGraph_oinj' does not depend on any axioms -/
#guard_msgs in #print axioms injGraph_oinj
/-- info: 'PSet.DecoderObstructionAudit.lam_decoded' does not depend on any axioms -/
#guard_msgs in #print axioms lam_decoded
/-- info: 'PSet.DecoderObstructionAudit.truthN_iff' does not depend on any axioms -/
#guard_msgs in #print axioms truthN_iff
/-- info: 'PSet.DecoderObstructionAudit.no_decoder_success_separation' does not depend on any axioms -/
#guard_msgs in #print axioms no_decoder_success_separation
/-- info: 'PSet.DecoderObstructionAudit.decoder_env_not_refutes' does not depend on any axioms -/
#guard_msgs in #print axioms decoder_env_not_refutes

end PSet.DecoderObstructionAudit
