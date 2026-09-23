import ConZF.Graph.Monotone
/-!
Normalization of well-founded justification certificates (con20). Supply a graph set `J` of
judgements and a graph set `Rs` of rules, pairs `⟨U, j⟩` with `U ⊆ J` a premise set (possibly
infinite) and `j ∈ J` a conclusion. The rule operator `ruleOp Rs` admits a judgement once
some rule for it has all premises admitted; it is inflationary and monotone, so the bounded
induction of `Monotone.lean` from the empty seed yields the least closed set `W`
(`normW`) with its first-entry ranks.

A certificate for `q` is a graph set `N` of nodes with an edge set `E`, a functional labelling
`ℓ` into `J`, and a root labelled `q`, such that every node is justified by some rule whose
premises are labels of its predecessors, and every nonempty subset of `N` has an `E`-minimal
member (`IsCert`). Nothing bounds the carrier `N` or the rank of the certificate.

**Completeness** (`endpoint_of_cert`): any certificate for `q` puts `q` in `W`, by the bad-node
argument: an `E`-minimal node whose label is outside `W` has all predecessors labelled in `W`,
so its rule fires. The certificate is used only inside a stable goal; nothing is retained.

**Decoding** (`cert_norm`): for `q ∈ W` the normalized certificate has nodes `W`, edges
`D(u, j) :⟺ ρ(u) < ρ(j)` on first-entry ranks, the identity labelling, and root `q`. A
judgement enters `W` at stage `ρ(j)` by an actual rule with premises of smaller rank
(`enter_rule`), and `D` has minimal members by `∈`-induction on ranks (`normD_wf`).

**Normalization** (`normalization`): a certificate exists, negatively, exactly when `q ∈ W`;
every normalized certificate lies in the envelope `P J × (P(J×J) × (P(J×J) × J))`, which
depends only on `J` (`norm_mem_envelope`), and the menu of normalized certificates over `W`
is complete (`normMenu_complete`). This is a new witness with its full specification proved,
not a collapse of the original one; rules are set-coded, but the certificate carrier, edges,
and labelling are graph sets read through membership, and no rule or predecessor is chosen
per premise.
-/
universe u

namespace GSet

section
variable (J Rs : GSet.{u})

/-- The rule operator: admit `j` once some rule `⟨U, j⟩` has every premise in `U` admitted. -/
def ruleOp (B : Sub J) (j : Pt J) : Prop :=
  ¬¬(B j ∨ ∃ U : GSet.{u}, Mem (opair U (J.at' j.1)) Rs ∧ ∀ u : Pt J, Mem (J.at' u.1) U → B u)

theorem isMono_ruleOp : IsMono J (ruleOp J Rs) where
  stable _ _ := inferInstanceAs (Stable (¬_))
  ext_iff _ _ h j := nn_congr (or_congr (h j) (exists_congr fun _ => and_congr_right fun _ =>
    forall_congr' fun u => imp_congr_right fun _ => h u))
  infl _ _ h := nn_intro (.inl h)
  ext _ hB a b e := nn_map fun
    | .inl hb => .inl (hB a b e hb)
    | .inr ⟨U, hR, hp⟩ => .inr ⟨U, Mem.congr_left (opair_congr _ _ (Equiv.refl U) e) hR, hp⟩
  mono _ _ h j := nn_map fun
    | .inl hb => .inl (h j hb)
    | .inr ⟨U, hR, hp⟩ => .inr ⟨U, hR, fun u hu => h u (hp u hu)⟩

theorem isInfl_ruleOp : IsInfl J (ruleOp J Rs) := (isMono_ruleOp J Rs).toIsInfl

/-- The least closed set of judgements, as a graph set. -/
abbrev normW : GSet.{u} := endpointSet (Φ := ruleOp J Rs) (S := emptySeed (η := J))

/-- Membership in the least closed set, as a predicate on points. -/
abbrev InW (j : Pt J) : Prop := endpoint (Φ := ruleOp J Rs) (S := emptySeed (η := J)) j

/-- The first-entry rank of a judgement. -/
abbrev normRank (j : Pt J) : GSet.{u} := entry (Φ := ruleOp J Rs) (S := emptySeed (η := J)) j

/-- **Certificates.** Nodes `N`, edges `E`, a functional labelling `ℓ` into `J`, a root `r`
labelled `q`; every node is justified by a rule whose premises label predecessors; every
nonempty subset of `N` has an `E`-minimal member. -/
structure IsCert (q N E ℓ r : GSet.{u}) : Prop where
  root : Mem r N
  label_root : Mem (opair r q) ℓ
  label_fun : ∀ n j j', Mem (opair n j) ℓ → Mem (opair n j') ℓ → Equiv j j'
  label_mem : ∀ n j, Mem (opair n j) ℓ → Mem j J
  rule : ∀ n, Mem n N → ¬¬∃ U j, Mem (opair U j) Rs ∧ Mem (opair n j) ℓ ∧
    ∀ u, Mem u U → ¬¬∃ m, Mem m N ∧ Mem (opair m n) E ∧ Mem (opair m u) ℓ
  wf : ∀ Z, Subset Z N → ∀ n₀, Mem n₀ Z → ¬¬∃ n, Mem n Z ∧ ∀ m, Mem m Z → ¬ Mem (opair m n) E

/-! ### Completeness: the bad-node argument -/

/-- **Completeness.** A certificate for `q` puts `q` in the least closed set. -/
theorem endpoint_of_cert {q : Pt J} {N E ℓ r : GSet.{u}} (hc : IsCert J Rs (J.at' q.1) N E ℓ r) :
    InW J Rs q := by
  have hΦ := isInfl_ruleOp J Rs
  have hS : IsSeed J (emptySeed (η := J)) := isSeed_emptySeed
  -- a node is good when all its labels lie in `W`
  let Good : GSet.{u} → Prop := fun n => ∀ j, Mem (opair n j) ℓ → Mem j (normW J Rs)
  have hGood : ∀ n n', Equiv n n' → ¬ Good n → ¬ Good n' := fun _ _ e h g =>
    h fun j hj => g j (Mem.congr_left (opair_congr _ _ e (Equiv.refl _)) hj)
  have memBad : ∀ {n}, Mem n (sep (fun n => ¬ Good n) N) ↔ Mem n N ∧ ¬ Good n :=
    fun {_} => mem_sep _ _ hGood
  have allGood : ∀ n, Mem n N → Good n := by
    intro n hn
    refine Stable.by_cases (Good n) id fun hng => ?_
    refine Stable.of_nn (hc.wf _ (fun _ h => (memBad.1 h).1) n (memBad.2 ⟨hn, hng⟩))
      fun ⟨n₁, hn₁, hmin⟩ => ?_
    have ⟨hn₁N, hbad⟩ := memBad.1 hn₁
    refine (hbad fun j hj => ?_).elim
    refine Stable.of_nn (hc.rule n₁ hn₁N) fun ⟨U, j', hR, hj', hprem⟩ => ?_
    refine Mem.congr_left (hc.label_fun n₁ j j' hj hj').symm ?_
    refine Stable.of_nn (hc.label_mem n₁ j' hj') fun ⟨a, ha, ea⟩ => ?_
    refine Mem.congr_left ea.symm ((pt_mem_endpointSet hΦ hS ⟨a, ha⟩).2 ?_)
    refine endpoint_closed hΦ hS ⟨a, ha⟩ (nn_intro (.inr ⟨U,
      Mem.congr_left (opair_congr _ _ (Equiv.refl U) ea) hR, fun u hu => ?_⟩))
    refine Stable.of_nn (hprem _ hu) fun ⟨m, hmN, hmE, hmℓ⟩ => ?_
    have hmGood : Good m := Stable.dne fun hng => hmin m (memBad.2 ⟨hmN, hng⟩) hmE
    exact (pt_mem_endpointSet hΦ hS u).1 (hmGood _ hmℓ)
  exact (pt_mem_endpointSet hΦ hS q).1 (allGood r hc.root _ hc.label_root)

/-! ### Decoding: the normalized certificate -/

/-- The dependency relation: pairs of judgements of `W` with strictly smaller first rank. -/
def normD : GSet.{u} :=
  range fun p : {p : {u : Pt J // InW J Rs u} × {j : Pt J // InW J Rs j} //
      Mem (normRank J Rs p.1.1) (normRank J Rs p.2.1)} =>
    opair (J.at' p.1.1.1.1) (J.at' p.1.2.1.1)

/-- The identity labelling on `W`. -/
def normL : GSet.{u} :=
  range fun u : {u : Pt J // InW J Rs u} => opair (J.at' u.1.1) (J.at' u.1.1)

theorem mem_normD {K : GSet.{u}} : Mem K (normD J Rs) ↔ ¬¬∃ (u j : Pt J), InW J Rs u ∧ InW J Rs j ∧
    Mem (normRank J Rs u) (normRank J Rs j) ∧ Equiv K (opair (J.at' u.1) (J.at' j.1)) :=
  (mem_range _).trans (nn_congr ⟨fun ⟨⟨⟨u, j⟩, hlt⟩, e⟩ => ⟨u.1, j.1, u.2, j.2, hlt, e⟩,
    fun ⟨u, j, hu, hj, hlt, e⟩ => ⟨⟨(⟨u, hu⟩, ⟨j, hj⟩), hlt⟩, e⟩⟩)

theorem mem_normL {K : GSet.{u}} : Mem K (normL J Rs) ↔
    ¬¬∃ u : Pt J, InW J Rs u ∧ Equiv K (opair (J.at' u.1) (J.at' u.1)) :=
  (mem_range _).trans (nn_congr ⟨fun ⟨u, e⟩ => ⟨u.1, u.2, e⟩, fun ⟨u, hu, e⟩ => ⟨⟨u, hu⟩, e⟩⟩)

theorem normD_sub : Subset (normD J Rs) (prod J J) := fun _ hK =>
  Stable.of_nn ((mem_normD J Rs).1 hK) fun ⟨u, j, _, _, _, e⟩ =>
    Mem.congr_left e.symm (opair_mem_prod _ _ (at'_mem u.2) (at'_mem j.2))

theorem normL_sub : Subset (normL J Rs) (prod J J) := fun _ hK =>
  Stable.of_nn ((mem_normL J Rs).1 hK) fun ⟨u, _, e⟩ =>
    Mem.congr_left e.symm (opair_mem_prod _ _ (at'_mem u.2) (at'_mem u.2))

/-- **Entering by a rule.** A judgement of `W` is admitted by some rule all of whose premises
are in `W` with strictly smaller rank. -/
theorem enter_rule {j : Pt J} (hj : InW J Rs j) :
    ¬¬∃ U : GSet.{u}, Mem (opair U (J.at' j.1)) Rs ∧
      ∀ u : Pt J, Mem (J.at' u.1) U → InW J Rs u ∧ Mem (normRank J Rs u) (normRank J Rs j) := by
  have hΦ := isInfl_ruleOp J Rs
  have hS : IsSeed J (emptySeed (η := J)) := isSeed_emptySeed
  -- the rank of `j` is denoted by a stage vertex
  refine Stable.of_nn (entry_mem_bound hΦ hS hj) fun ⟨β, hβ, eβ⟩ => ?_
  have eβ' : Equiv (normRank J Rs j) ((rank (bound (X := J))).at' β) := eβ.trans (stage_equiv hβ).symm
  have hjβ : hist (Φ := ruleOp J Rs) (S := emptySeed) (bound (X := J)) β j :=
    (hist_iff_entry hΦ (TC.of_rel hβ) j).2 (nn_intro (.inr eβ'))
  -- the stopping cut, as a stage vertex
  refine Stable.of_nn (stopCut_mem hΦ hS) fun ⟨β₀, hβ₀, e₀⟩ => ?_
  have e₀' : Equiv (stopCut (Φ := ruleOp J Rs) (S := emptySeed (η := J)))
      ((rank (bound (X := J))).at' β₀) := e₀.trans (stage_equiv hβ₀).symm
  refine Stable.of_nn ((hist_eq hΦ _ β j).1 hjβ) fun
    | .inl h => h.elim
    | .inr ⟨ξ, hξ, h⟩ => ?_
  have hξβ : Mem ((rank (bound (X := J))).at' ξ) (normRank J Rs j) :=
    Mem.congr_right eβ'.symm (at'_mem (G := (rank (bound (X := J))).at' β) hξ)
  refine Stable.of_nn h fun
    | .inl h => ?_
    | .inr ⟨U, hR, hp⟩ => ?_
  · -- `j` cannot already be present at a stage below its rank
    refine Stable.of_nn ((hist_iff_entry hΦ (hξ.trans (TC.of_rel hβ)) j).1 h) fun
      | .inl h' => (mem_asymm _ hξβ h').elim
      | .inr e => (not_mem_self _ (Mem.congr_left e.symm hξβ)).elim
  refine nn_intro ⟨U, hR, fun u hu => ?_⟩
  have hu' := hp u hu
  have hle := (hist_iff_entry hΦ (hξ.trans (TC.of_rel hβ)) u).1 hu'
  -- the stage `ξ` lies below the stopping cut, so the row at `ξ` is inside the endpoint
  have hξγ : Mem ((rank (bound (X := J))).at' ξ) ((rank (bound (X := J))).at' β₀) :=
    Stable.of_nn (entry_le_stopCut hΦ hS hj) fun
      | .inl h => Mem.congr_right e₀' ((isOrd_stopCut hΦ).1 _ h _ hξβ)
      | .inr e => Mem.congr_right (e.trans e₀') hξβ
  refine ⟨(endpoint_row hΦ (TC.of_rel hβ₀) e₀' u).2 (hist_mono_sem hΦ _ hξγ u hu'), ?_⟩
  exact Stable.of_nn hle fun
    | .inl h => (isOrd_entry hΦ j).1 _ hξβ _ h
    | .inr e => Mem.congr_left e.symm hξβ

/-- **Well-foundedness of the dependency relation**, by `∈`-induction on ranks. -/
theorem normD_wf (Z : GSet.{u}) (hZ : Subset Z (normW J Rs)) :
    ∀ n₀, Mem n₀ Z → ¬¬∃ n, Mem n Z ∧ ∀ m, Mem m Z → ¬ Mem (opair m n) (normD J Rs) := by
  have hΦ := isInfl_ruleOp J Rs
  have hS : IsSeed J (emptySeed (η := J)) := isSeed_emptySeed
  have key : ∀ α : GSet.{u}, ∀ n₀, Mem n₀ Z →
      (∀ u : Pt J, Equiv n₀ (J.at' u.1) → Equiv (normRank J Rs u) α) →
      ¬¬∃ n, Mem n Z ∧ ∀ m, Mem m Z → ¬ Mem (opair m n) (normD J Rs) := by
    refine mem_induction (F := fun α => ∀ n₀, Mem n₀ Z →
      (∀ u : Pt J, Equiv n₀ (J.at' u.1) → Equiv (normRank J Rs u) α) →
      ¬¬∃ n, Mem n Z ∧ ∀ m, Mem m Z → ¬ Mem (opair m n) (normD J Rs)) fun α ih n₀ hn₀ hα => ?_
    refine Stable.by_cases (¬¬∃ m, Mem m Z ∧ Mem (opair m n₀) (normD J Rs)) (fun h => ?_)
      fun h => nn_intro ⟨n₀, hn₀, fun m hm hD => h (nn_intro ⟨m, hm, hD⟩)⟩
    refine Stable.of_nn h fun ⟨m, hm, hD⟩ => ?_
    refine Stable.of_nn ((mem_normD J Rs).1 hD) fun ⟨u, j, _, _, hlt, e⟩ => ?_
    have ⟨em, en⟩ := opair_inj _ _ e
    exact ih _ (Mem.congr_right (hα j en) hlt) m hm fun u' e' =>
      entry_congr hΦ hS (e'.symm.trans em)
  intro n₀ hn₀
  refine Stable.of_nn (mem_endpointSet.1 (hZ n₀ hn₀)) fun ⟨a, _, e⟩ => ?_
  exact key (normRank J Rs a) n₀ hn₀ fun u e' => entry_congr hΦ hS (e'.symm.trans e)

/-- **Decoding.** For `q ∈ W`, the normalized certificate `(W, D, id, q)` is a certificate. -/
theorem cert_norm (hRs : Subset Rs (prod (powerset J) J)) {q : Pt J} (hq : InW J Rs q) :
    IsCert J Rs (J.at' q.1) (normW J Rs) (normD J Rs) (normL J Rs) (J.at' q.1) where
  root := (pt_mem_endpointSet (isInfl_ruleOp J Rs) isSeed_emptySeed q).2 hq
  label_root := (mem_normL J Rs).2 (nn_intro ⟨q, hq, Equiv.refl _⟩)
  label_fun n j j' hj hj' :=
    Stable.of_nn ((mem_normL J Rs).1 hj) fun ⟨u, _, e⟩ => Stable.of_nn ((mem_normL J Rs).1 hj')
      fun ⟨u', _, e'⟩ =>
        have ⟨en, ej⟩ := opair_inj _ _ e
        have ⟨en', ej'⟩ := opair_inj _ _ e'
        ej.trans ((en.symm.trans en').trans ej'.symm)
  label_mem _ j hj := Stable.of_nn ((mem_normL J Rs).1 hj) fun ⟨u, _, e⟩ =>
    Mem.congr_left (opair_inj _ _ e).2.symm (at'_mem u.2)
  rule n hn := by
    refine Stable.of_nn (mem_endpointSet.1 hn) fun ⟨j, hj, en⟩ => ?_
    refine Stable.of_nn (enter_rule J Rs hj) fun ⟨U, hR, hp⟩ => ?_
    -- the premise set is a subset of `J`
    have hU : Subset U J := fun K hK =>
      Stable.of_nn ((mem_prod _ _).1 (hRs _ hR)) fun ⟨_, _, hv, _, e⟩ =>
        (mem_powerset J).1 (at'_mem hv) K (Mem.congr_right (opair_inj _ _ e).1 hK)
    refine nn_intro ⟨U, J.at' j.1, hR, (mem_normL J Rs).2 (nn_intro ⟨j, hj,
      opair_congr _ _ en (Equiv.refl _)⟩), fun u hu => ?_⟩
    refine Stable.of_nn (hU u hu) fun ⟨a, ha, ea⟩ => ?_
    have ⟨hInW, hlt⟩ := hp ⟨a, ha⟩ (Mem.congr_left ea hu)
    refine nn_intro ⟨J.at' a, (pt_mem_endpointSet (isInfl_ruleOp J Rs) isSeed_emptySeed ⟨a, ha⟩).2 hInW,
      (mem_normD J Rs).2 (nn_intro ⟨⟨a, ha⟩, j, hInW, hj, hlt, opair_congr _ _ (Equiv.refl _) en⟩),
      (mem_normL J Rs).2 (nn_intro ⟨⟨a, ha⟩, hInW, opair_congr _ _ (Equiv.refl _) ea⟩)⟩
  wf := normD_wf J Rs

/-! ### The normalization theorem, the envelope, and the menu -/

/-- **Normalization.** A certificate for `q` exists, negatively, exactly when `q ∈ W`. -/
theorem normalization (hRs : Subset Rs (prod (powerset J) J)) (q : Pt J) :
    (¬¬∃ N E ℓ r : GSet.{u}, IsCert J Rs (J.at' q.1) N E ℓ r) ↔ InW J Rs q :=
  ⟨fun h => Stable.of_nn h fun ⟨_, _, _, _, hc⟩ => endpoint_of_cert J Rs hc,
   fun hq => nn_intro ⟨_, _, _, _, cert_norm J Rs hRs hq⟩⟩

/-- The normalized certificate as one graph set `⟨W, ⟨D, ⟨ℓ, q⟩⟩⟩`. -/
def norm (q : Pt J) : GSet.{u} :=
  opair (normW J Rs) (opair (normD J Rs) (opair (normL J Rs) (J.at' q.1)))

/-- The envelope of normalized certificates, depending only on `J`. -/
def normEnvelope : GSet.{u} :=
  prod (powerset J) (prod (powerset (prod J J)) (prod (powerset (prod J J)) J))

theorem norm_mem_envelope (q : Pt J) : Mem (norm J Rs q) (normEnvelope J) :=
  opair_mem_prod _ _ ((mem_powerset _).2 endpointSet_sub)
    (opair_mem_prod _ _ ((mem_powerset _).2 (normD_sub J Rs))
      (opair_mem_prod _ _ ((mem_powerset _).2 (normL_sub J Rs)) (at'_mem q.2)))

/-- The menu: the normalized certificates with root ranging over `W`. -/
def normMenu : GSet.{u} := range fun q : {q : Pt J // InW J Rs q} => norm J Rs q.1

theorem normMenu_sub : Subset (normMenu J Rs) (normEnvelope J) := fun _ hK =>
  Stable.of_nn ((mem_range _).1 hK) fun ⟨q, e⟩ => Mem.congr_left e.symm (norm_mem_envelope J Rs q.1)

/-- **Completeness of the menu.** Whenever `q` has a certificate, the menu holds one. -/
theorem normMenu_complete (hRs : Subset Rs (prod (powerset J) J)) (q : Pt J)
    (h : ¬¬∃ N E ℓ r : GSet.{u}, IsCert J Rs (J.at' q.1) N E ℓ r) :
    ¬¬∃ Z, Mem Z (normMenu J Rs) ∧ Equiv Z (norm J Rs q) ∧
      IsCert J Rs (J.at' q.1) (normW J Rs) (normD J Rs) (normL J Rs) (J.at' q.1) :=
  have hq := (normalization J Rs hRs q).1 h
  nn_intro ⟨norm J Rs q, (mem_range _).2 (nn_intro ⟨⟨q, hq⟩, Equiv.refl _⟩), Equiv.refl _,
    cert_norm J Rs hRs hq⟩

end

/-- info: 'GSet.endpoint_of_cert' does not depend on any axioms -/
#guard_msgs in #print axioms endpoint_of_cert
/-- info: 'GSet.cert_norm' does not depend on any axioms -/
#guard_msgs in #print axioms cert_norm
/-- info: 'GSet.normalization' does not depend on any axioms -/
#guard_msgs in #print axioms normalization
/-- info: 'GSet.normMenu_complete' does not depend on any axioms -/
#guard_msgs in #print axioms normMenu_complete

end GSet
