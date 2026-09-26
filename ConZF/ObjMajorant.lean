import ConZF.DecoderLocal
import ConZF.Audit.Certificate
/-!
The structural majorant of nc2 (equation (6)), checked independently of any forcing relation.

For an object `q` and a family `β` of descriptors dominating an auxiliary environment `e'` at `e`
(`e' j ∈ eval (β j) e`), the descriptor `M q β` at `e` **contains** the value of `q` at `e'`
(`eval_mem_M`), for every existing constructor: `sepNeg` with an arbitrary test, since a separation
is a subset of its base, and `letVar` with the extended family. For a bounded extension
`x ∈ eval a e`, the family `β 0 = a`, `β (j+1) = {var j}` gives per-descriptor domination
`eval q (x :: e) ⊆ eval (⋃ M q β) e` (`eval_subset_of_bounded`). This is domination of each
descriptor by an individually constructed descriptor, not a descriptor for all descriptor values at
once (which `Audit/ObjectEnvelope.lean` shows does not exist in this grammar).

With an abstract condition truth `Tr` on sets, stable and antitone under inclusion, this gives the
bounded-environment transport `All Tr (x :: e) ↔ All Tr e` for `x` in a described bound
(`all_transport`), the negative-certificate equivalence `Cert Tr e Q ↔ (All Tr e → Q)` (`cert_iff`),
and the bounded-universal aggregation of certificates (`cert_bounded_all`). These provide negative
existence of a logical-support certificate. They return neither a descriptor containing all previous
certificate values nor a positive witness head, and are not positive Collection.
-/
universe u

namespace PSet.ObjMajorant
open NegCore

def cons' (o : Obj) (β : Nat → Obj) : Nat → Obj
  | 0 => o
  | j+1 => β j

/-- nc2 (6): a descriptor at `e` containing the value of `q` at an environment dominated by `β`. -/
def M : Obj → (Nat → Obj) → Obj
  | .var j, β => β j
  | .emp, _ => .upair .emp .emp
  | .upair q r, β => .pow (.sUnion (.upair (M q β) (M r β)))
  | .sUnion q, β => .pow (.sUnion (.sUnion (M q β)))
  | .pow q, β => .pow (.pow (.sUnion (M q β)))
  | .sepNeg q _, β => .pow (.sUnion (M q β))
  | .letVar q r, β => M r (cons' (M q β) β)

/-- The exact membership bound, nc2 (7). -/
theorem eval_mem_M : ∀ (q : Obj) {β : Nat → Obj} {e e' : Env.{u}},
    (∀ j, e' j ∈ Obj.eval (β j) e) → Obj.eval q e' ∈ Obj.eval (M q β) e
  | .var j, _, _, _, h => h j
  | .emp, _, _, _, _ => mem_upair_left _ _
  | .upair a b, _, _, _, h => mem_powerset.2 fun _ hz => Stable.of_nn (mem_upair.1 hz) fun
      | .inl ez => DecoderLocal.mem_sUnion_upair.2 (nn_intro (.inl ((mem_congr_left ez).2 (eval_mem_M a h))))
      | .inr ez => DecoderLocal.mem_sUnion_upair.2 (nn_intro (.inr ((mem_congr_left ez).2 (eval_mem_M b h))))
  | .sUnion a, _, _, _, h => mem_powerset.2 fun _ hz => Stable.of_nn (mem_sUnion.1 hz) fun ⟨y, hy, hzy⟩ =>
      mem_sUnion.2 (nn_intro ⟨y, mem_sUnion.2 (nn_intro ⟨_, eval_mem_M a h, hy⟩), hzy⟩)
  | .pow a, _, _, _, h => mem_powerset.2 fun _ hz => mem_powerset.2 fun w hw =>
      mem_sUnion.2 (nn_intro ⟨_, eval_mem_M a h, mem_powerset.1 hz w hw⟩)
  | .sepNeg a N, _, _, e', h => mem_powerset.2 fun _ hz =>
      mem_sUnion.2 (nn_intro ⟨_, eval_mem_M a h, ((mem_sep (truth_cons_resp N e')).1 hz).1⟩)
  | .letVar q r, β, _, e', h => eval_mem_M r (β := cons' (M q β) β) (e' := Env.cons (Obj.eval q e') e') fun
      | 0 => eval_mem_M q h
      | j+1 => h j

/-- The family for a bounded extension: slot `0` bounded by `a`, the rest by singletons. -/
def boundedβ (a : Obj) : Nat → Obj
  | 0 => a
  | j+1 => .upair (.var j) (.var j)

/-- Per-descriptor domination, nc2 (8). -/
theorem eval_subset_of_bounded {a q : Obj} {e : Env.{u}} {x : PSet.{u}} (hx : x ∈ Obj.eval a e) :
    ∀ z, z ∈ Obj.eval q (Env.cons x e) → z ∈ Obj.eval (.sUnion (M q (boundedβ a))) e :=
  fun _ hz => mem_sUnion.2 (nn_intro ⟨_, eval_mem_M q (fun
    | 0 => hx
    | _+1 => mem_upair_left _ _), hz⟩)

/-! ### Transport and aggregation for an abstract condition truth -/

section Transport
variable (Tr : PSet.{u} → Prop) [∀ b, Stable (Tr b)]

/-- Every descriptor readback at `e` satisfies the condition. -/
def All (e : Env.{u}) : Prop := ∀ q : Obj, Tr (Obj.eval q e)

/-- Negative existence of a certificate: nc2 (4) at the singleton condition. -/
def Cert (e : Env.{u}) (Q : Prop) : Prop := ¬¬∃ q : Obj, Tr (Obj.eval q e) → Q

omit [∀ b, Stable (Tr b)] in
theorem all_lift (antitone : ∀ U V : PSet.{u}, (∀ x, x ∈ U → x ∈ V) → Tr V → Tr U) (e : Env.{u}) (x : PSet.{u}) : All Tr (Env.cons x e) → All Tr e := fun h q =>
  antitone _ _ (fun _ hz => (mem_congr_right (Obj.eval_rename q (along_succ x e))).2 hz) (h q.lift)

omit [∀ b, Stable (Tr b)] in
theorem all_bounded (antitone : ∀ U V : PSet.{u}, (∀ x, x ∈ U → x ∈ V) → Tr V → Tr U) (e : Env.{u}) {a : Obj} {x : PSet.{u}} (hx : x ∈ Obj.eval a e) :
    All Tr e → All Tr (Env.cons x e) := fun h q =>
  antitone _ _ (eval_subset_of_bounded hx) (h (.sUnion (M q (boundedβ a))))

omit [∀ b, Stable (Tr b)] in
/-- Bounded-environment transport, nc2 (11). -/
theorem all_transport (antitone : ∀ U V : PSet.{u}, (∀ x, x ∈ U → x ∈ V) → Tr V → Tr U) (e : Env.{u}) {a : Obj} {x : PSet.{u}} (hx : x ∈ Obj.eval a e) :
    All Tr (Env.cons x e) ↔ All Tr e :=
  ⟨all_lift Tr antitone e x, all_bounded Tr antitone e hx⟩

/-- nc2 (10): a certificate is logical support under the condition on all readbacks. -/
theorem cert_iff (e : Env.{u}) (Q : Prop) [Stable Q] : Cert Tr e Q ↔ (All Tr e → Q) :=
  CertificateAudit.negative_certificate_iff ⟨Obj.emp⟩ (fun q => Tr (Obj.eval q e)) Q

/-- Bounded-universal aggregation, nc2 (12): no descriptor for the union of the certificate values
is formed. -/
theorem cert_bounded_all (antitone : ∀ U V : PSet.{u}, (∀ x, x ∈ U → x ∈ V) → Tr V → Tr U) (e : Env.{u}) {a : Obj} (P : PSet.{u} → Prop) [∀ x, Stable (P x)]
    (h : ∀ x, x ∈ Obj.eval a e → Cert Tr (Env.cons x e) (P x)) :
    Cert Tr e (∀ x, x ∈ Obj.eval a e → P x) :=
  (cert_iff Tr e _).2 fun hA x hx =>
    (cert_iff Tr (Env.cons x e) (P x)).1 (h x hx) (all_bounded Tr antitone e hx hA)

end Transport

/-- info: 'PSet.ObjMajorant.eval_mem_M' does not depend on any axioms -/
#guard_msgs in #print axioms eval_mem_M
/-- info: 'PSet.ObjMajorant.eval_subset_of_bounded' does not depend on any axioms -/
#guard_msgs in #print axioms eval_subset_of_bounded
/-- info: 'PSet.ObjMajorant.all_transport' does not depend on any axioms -/
#guard_msgs in #print axioms all_transport
/-- info: 'PSet.ObjMajorant.cert_bounded_all' does not depend on any axioms -/
#guard_msgs in #print axioms cert_bounded_all

end PSet.ObjMajorant
