# Membership accessibility

The remaining hypothesis is exactly

```lean
PSet.AccHyp.{u} ↔ ¬¬∀ x : PSet.{u}, Acc (· ∈ ·) x
```

`ConZF/Acc.lean` proves the converse to upstream's `accHyp_of_mem_wf`.
Its private assignment starts at `[.c x]` for each set `x` and extends a
path targeting `x` by `.c y` whenever `y ∈ x`. It satisfies `Desc`.
Accessibility of its root therefore supplies accessibility of every set.
The construction uses the existing `Path`, `Rel`, and `acc_root_of_desc`.

The relation remains upstream's stable membership:

```lean
x ∈ y := ¬¬∃ i : y.Idx, x ≈ y.Func i
```

`Acc` is ordinary Lean accessibility. Stable membership induction does not
supply unrestricted induction into this proposition. `AccHyp` implies
`∀ x, ¬¬Acc (· ∈ ·) x`; the converse has not been established.

## Constructive cases

`acc_of_subset` transfers accessibility along inclusion. It gives accessibility
of `empty`, closure under `powerset`, closure under `succ` for transitive sets,
and accessibility of each `ofNat n`. Accessibility also transfers from `rank x`
to `x`, including when that rank belongs to a finite ordinal.

For an arbitrary `x ∈ omega`, `mem_omega` supplies only
`¬¬∃ n, x ≈ ofNat n`. The finite proofs give `¬¬Acc (· ∈ ·) x`, but do not
supply accessibility of every member simultaneously. Neither accessibility
nor double-negated accessibility of `omega` has been proved outright.

## Markov's principle

`ConZF/Markov.lean` privately constructs a guarded union of finite ordinals
representing the distance to the first successful search. Under double-negated
existence it belongs to `omega`; after a failed test the next search belongs
to the previous one. Both membership claims are stable, so their proofs use
upstream's `guard`, `iUnion`, and `Stable.of_nn` without selecting a witness.

Recursion on an assumed accessibility proof then gives:

```text
Acc (· ∈ ·) omega → PropMarkov → Markov
¬¬Acc (· ∈ ·) omega → ¬¬PropMarkov → ¬¬Markov
AccHyp → ¬¬PropMarkov → ¬¬Markov
```

Both principles quantify over all `P : Nat → Prop` and conclude
`(¬¬∃ n, P n) → ∃ n, P n`. `Markov` assumes `∀ n, Decidable (P n)`;
`PropMarkov` assumes `∀ n, P n ∨ ¬P n`. Decision procedures supply the
disjunctions, giving `PropMarkov.markov`; no converse is claimed.
With decision procedures, `witness_of_acc_omega` also returns
`{n : Nat // P n}` by eliminating `Acc` into Type. Double-negated `PropMarkov`
yields `search_dns_of_accHyp` for families with propositional decisions.

These are conditional implications, not an independence proof for Lean's
constructive fragment. In particular, nonderivability of Markov's principle
alone would not establish nonderivability of its uniform double negation.
The predicative result in Pédrot–Tabareau's
[Failure is Not an Option](https://link.springer.com/chapter/10.1007/978-3-319-89884-1_9)
cannot simply be applied here: its impredicative extension in §5.2 explicitly
omits singleton elimination, while this development eliminates `Acc : Prop`
into Type. Markov's admissible metatheoretic rule is also distinct from the
uniform internal principle used here.

## Rank bounds

The model theorem no longer consumes accessibility. `CofinalCut.lean` defines,
for an admissible Replacement instance `(ψ, e, a)` over `HG` and an ordinal cap
`κ`, the cut `rankCofinalCut ψ e a κ = {ζ ∈ κ | CoveredRank ψ e a ζ}`, where
`CoveredRank` says that some actual output rank reaches `ζ`. Two facts:

* `cls_rankCofinalCut`: the cut is hereditarily good for every cap. This is the
  endpoint argument formerly inside `hg_model`: if the cut were not good, `HG`
  would be `V` at the cut, and `ψ` itself would reach the cut.
* `hg_replacement_of_rank_bound`: if `κ` strictly bounds the output ranks,
  `Vl (rankCofinalCut ψ e a κ)` is the collecting set for Replacement.

`Model.lean` proves `hg_model_of_bounds : BoundHyp → ZFModel HG`, where
`BoundHyp` asks, for each instance, `RankBounded ψ e a`, a `¬¬∃ κ`. The
double negation is inside the quantifiers over instances; no bound is chosen.

Producers of the bounds, in decreasing strength:

```text
AccHyp → PointwiseHGAcc → BoundHyp → Con ZF
```

`boundHyp_of_accHyp` uses the materializing recursion at the glued root and
takes the rank of the image. `boundHyp_of_pointwise` (`Pointwise.lean`) guards
the recursion at each component `[.c x]` by its own accessibility proof, so
that `∀ η, Cls ISat η → ¬¬Acc (· ∈ ·) η` suffices, with the quantifier outside
the double negation. Neither implication is claimed to reverse.

The pointwise hypothesis does not escape the Markov obstruction: `ω` is
hereditarily good, so `PointwiseHGAcc` gives `¬¬Acc (· ∈ ·) ω` and hence
`¬¬PropMarkov` (`not_not_prop_markov_of_pointwise`). Moving the quantifier
outside the double negation helps assemble bounds; it does not weaken what is
asked at `ω`. This is the reason to seek `BoundHyp` without accessibility of
membership at all, even at `ω`: the finite-predecessor producer, for
instance, bounds a collapse by `ω` through a native presentation of `ω` and
never proves `ω` accessible.

Stopping criteria (`CofinalCut.lean`): `rankCofinalCut ψ e a (succ κ) ≈
rankCofinalCut ψ e a κ` iff `κ` is a strict common bound
(`rankCofinalCut_successor_stationary_iff`). Idempotence of the cut holds for
every cap and detects nothing. If one instance has no bound, every ordinal is
hereditarily good and `HG` is the whole universe
(`hg_universal_of_not_rankBounded`), so the unresolved case is a definable
functional relation on a set whose output ranks are cofinal in all ordinals.

## Scope of the obstructions

`CanonicalAcc.lean`: for a hereditarily good `η`, accessibility of the root of
the *unpruned* rule tree `Tr (rule ISat) η` is equivalent to `Acc (· ∈ ·) η`.
The identity relation on `η` is unbounded at `η`, and `Rel` does not require
`Avail`, so every membership descent is an edge of the tree. This says only
that restricting attention to these trees, as currently defined, does not
weaken pointwise ordinal accessibility. It does not prove impossibility, and
it says nothing about trees with fewer edges.

A classical test model, argued externally in ZFC and not formalized: in
`M = V_{ω₁}`, every ordinal is hereditarily good in the sense of `Reach.lean`
(each countable limit is reached from `0` by a real coding a well-order of that
type), so `HG^M = M`; yet on `a = 𝒫(ℕ × ℕ)` the relation "`z = (β, f)` with
`f : (ℕ, R) ≅ (β, ∈)`" is partial functional, `Δ₀` with parameter `ω`, and its
output ranks are cofinal in `ω₁`. So the set-theoretic consequences extracted
so far (the cut identities, `AllGood`, boundedness of the formula) cannot force
`BoundHyp`. This is a statement about the set-theoretic argument only. `M` is
not a model of Lean's universes or of large elimination of `Acc`, and the
example is not a counterexample to `BoundHyp` in the intended type theory.

## Native bounds

What distinguishes the type theory from the test model is that a native
function `f : I → PSet.{u}` on a small `I : Type u` has its range as a set,
while a functional relation in `Prop` does not. `NativeBound.lean` makes this
into a bound: for a small type `C` of certificates and a decoder
`δ : C → PSet.{u}`, `natBound δ = rank (range δ)` is an ordinal containing
every ordinal that is not not dominated by some `δ c`
(`mem_natBound_of_dominated`). The certificates of interest are well-founded
relations on a small carrier `X` together with their proof of well-foundedness
(`WFCode X : Type u`); the decoder builds trees by `Acc`-recursion on the
certificate, and `wfBound X` bounds their heights. As a test, the usual order
on `Nat` decodes to `ω` (`rank_natCode_tree`), so `ω ∈ wfBound (ULift Nat)`.
This is a native presentation of `ω`, not accessibility of `ω` under
membership, which `Markov.lean` shows would give Markov's principle.

## Simulations

A certificate need not present the target. `Sim.lean` defines, for a source
relation `R` on states (which may be large, such as `Path`) and a code `c`,
`Sim R c p z`: every `R`-child of `p` is not not simulated at some
`c`-predecessor of `z`. It is stable, defined by native recursion on the
certificate, and mentions no target.

* `subset_ht_of_sim`: if targets are ordinals and `R, τ` satisfy coverage
  (every element of a target is not not reached by the successor of a child's
  target), a simulation at `z` bounds the target by the height of `z`. Neither
  functionality nor accessibility of `R` is used.
* `sim_of_subset_ht`: under descent, the converse. For the coherent
  assignments of `Mat.lean`, `Coherent.cover` supplies coverage at ordinal
  targets, by forming the first-child set inside the target and forgetting
  availability. So there a simulation at `z` is exactly inclusion of the
  target in the height of `z`.
* `sim_top`: if every child of `p` has a certificate in some code on a fixed
  carrier `X`, then `p` is simulated at the top of the enclosing tree
  `encCode X`, the code on `Option (Σ c, nodes of c)` with every node of every
  code below a new top. This tree is well-founded without any premise and is
  formed before the pointwise certificates are used, so no double negation
  crosses the quantifier over children. `mem_succ_encBound_of_children` is
  the resulting bound.
* `not_sim_top`: the top of `encCode X` is simulated in no code on `X` (its height
  contains every height on `X`). Composing the parent step therefore requires
  enlarging the carrier; repeating it on one carrier cannot work.

## A producer: the finite-predecessor fragment

`FinPred.lean` derives a bound from semantic hypotheses alone. For a relation
`R` on a small carrier, `FinHt R i n` is the stable predicate of height at
most `n`. If `R` admits induction for stable predicates (`SInd`) and its
predecessor families are negatively finite (`NegFin`: at each point, not not
some finite list covers the predecessors, with no choice of list), then every
point has not not a finite height (`finHt_of_sInd`): at a point, the finitely
many heights of a covering list are combined inside the stable goal. Finite
height `n` is a simulation into `natCode` at `n` (`sim_natCode_of_finHt`), on
the same carrier for every point, so this fragment needs no enlargement.
Soundness then bounds every semantic collapse value by a finite ordinal
(`collapse_value_mem_omega`) and the collapse by `ω` (`collapse_subset_omega`).
The collapse values are a relation in `Prop` with coverage, descent, totality
and ordinal values; stable induction on `R` is itself derived from descent into
them (`sInd_of_desc`). No native function on the carrier, no accessibility of
`R`, and no accessibility of any collapse value under membership is assumed.

The encoded output, the pair of the collapse ordinal and its graph of pairs
`(u, α_i)` with `u ∈ ω`, is bounded by containment: the collapse is in `P(ω)`,
the graph in `P³(ω)`, and the pair in the fixed set
`collapseBox = P²(P(ω) ∪ P³(ω))`, whose rank is the common strict rank bound
(`collapse_encoded_rank_mem`). No level bookkeeping in `D` and no native
function for the isomorphism is used; `rankBounded_of_mem` turns containment
in a fixed set into `RankBounded`.

The scope is the fragment: the order type is at most `ω`. Countable
well-orders with infinite predecessor families are not covered.

## Rank is first-order over `HG`

The envelope of `Envelope.lean` is a predicate in `Prop`; to treat envelopes
as definable instances the least-rank specification must be a formula. The
bridge is `RankFml.lean`: `rankFml` says of `x` (variable `0`) and `ρ`
(variable `1`) that there are a transitive set `T ∋ x` and a graph `g` on `T`,
total, functional and satisfying the rank recursion, with `(x, ρ) ∈ g`, all
written by membership with Kuratowski pairs. `sat_rankFml`: for `x, ρ ∈ HG`,
`Sat HG rankFml ⟨x, ρ⟩ ↔ ρ ≈ rank x`. The witnesses are native
(`RankGraph.lean`): the transitive closure `tcl x` by iterated union, the
domain `tclDom x = tcl x ∪ {x}`, and the graph `rankGraph x` of
`z ↦ (z, rank z)` over the literal indices of the domain, with ranks bounded
by `rank x + 3`, hence in `HG` (`hg_tclDom`, `hg_rankGraph`). Uniqueness
(`rank_unique`) is membership induction on a stable predicate. Neither
Replacement nor `hg_model_of_bounds` is used, so the bridge is available to
the normal-form reduction without circularity.

## Native covers

`Cover.lean` records the interface through which producers reach
`RankBounded`. `F` is covered at `x` by candidates `e : C → PSet` (`C` small)
when every output at `x` is not not the value of a candidate; candidates may
be wrong. Covers at the literal inputs of a domain, with candidate types
depending on the literal index, bound all output ranks by the rank of the
combined range over the dependent sum (`rank_mem_of_covers`,
`rankBounded_of_covers`). Covers compose through an existential intermediate
by a dependent sum of candidate types (`covers_comp`), provided the second
relation respects bisimulation in its input, so that it accepts the
reconstructed intermediate; no intermediate is chosen. Testing candidates by
an arbitrary predicate keeps the cover (`covers_and`): generating candidates
needs native data, testing them may use anything in `Prop`.

## Witness envelopes and caps

`Envelope.lean` gives every first-order existential problem, as a stable
extensional predicate `P` on sets, a canonical functional output: the set of
all witnesses of least rank, or the empty set (`Env P W`, a negative
disjunction). It exists negatively and is functional with no witness selected
(`env_exists`, `env_func`), it is in `HG` when the witnesses are (`env_hg`),
and for a functional `P` it is the singleton of the output
(`env_singleton`), so bounds on envelopes bound the original outputs.

At every ordinal cap `κ` there is an unconditional approximation: `capRank P κ`
is the initial segment of `κ` below every capped witness rank, one
Separation, and `capWit P κ` the capped witnesses of that rank. If no witness
fits the approximation is empty; if some witness fits, negatively, then the cap
rank is attained (`capRank_attained`: otherwise it belongs to itself) and is
the global least witness rank (`capRank_subset`), and `capWit` is the entire
least-rank witness set (`mem_capWit_iff`). The exact criterion
(`env_capWit_iff`): the approximation is the envelope precisely when the cap
meets the witness class whenever that class is nonempty. `rankBounded_of_cap`
turns a source-wide cap meeting each nonempty witness class of a functional
instance into `RankBounded`.

So for a fixed source the question is a single cap, not evaluation,
uniqueness or reconstruction. The classical test model shows this criterion
alone does not supply the cap: its approximations change once per input, at
cofinal thresholds. `Cover.lean` also records that containment in a fixed set
is a cover (`covers_of_mem`), so the collapse benchmark composes with
`covers_comp`.

The remaining task is a producer: for a fixed admissible instance, a small
family of certificates whose decoded heights dominate all its output ranks,
with only pointwise double-negated existence of a certificate. Native
domination is one proposed route to `BoundHyp`, not a requirement; a producer
may assume every ordinal hereditarily good and hypothetical cofinality, and
it suffices to certify one output whose rank reaches the test bound. In
terms of simulations: for each literal input `a_i`, a carrier `X_i` built from
the source data such that the component at `a_i` is not not simulated in
some code on `X_i`; then the union of the `encBound X_i` is a common bound.

The principal results have guarded empty `#print axioms` checks. Verification:
`lake build`, `lake env leanchecker --fresh --verbose ConZF`, and `git diff --check`.
