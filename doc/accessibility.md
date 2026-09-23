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

## Ideal sets: the sheaf route, as far as it goes

The alternative suggested in the Zulip discussion is to interpret the
classical construction in double-negation sheaves rather than to recover
`Acc` from its double negation. `Ideal.lean` takes the part of that available
without higher inductive types: an *ideal set* is a stable, extensional, not
not inhabited predicate on sets whose elements are all bisimilar, compared
pointwise. Unique choice holds into ideals (`Ideal.ofRel`): the envelope,
negatively total and functional, is a function into ideals. What is missing
is a tree. A sheafified tree type whose children are ideals of itself is not
an admissible inductive (the kernel rejects the occurrence, checked); and for
ideals of the existing trees the constructor test fails in a precise way: the
parent of a small family of ideal children is a stable functional
specification (`IsParent`, `isParent_func`), but it is not not inhabited
exactly when some set not not contains a representative of every child
(`isParent_exists_iff`). This is a bounded Collection statement for
ideal families indexed by a small type. It has not been identified with
double-negation shift, nor with the exact strength of `BoundHyp`: arbitrary
ideal families have a different scope from first-order definitions over
`HG`. No impossibility is proved. The checked result is that this
construction of a parent needs a Collection proof which the ideal
definitions do not supply, which is a reasonable stopping point for the
investigation; a setoid presentation of sheafified trees with its own
recursion principle remains an open possibility.

## The graph route (experimental)

The notes of conzf5 propose a different value representation: a *graph
set* is a small type of vertices with an edge relation, a root, and a proof
of well-founded induction for stable predicates (`SWF`), an ordinary record
whose proof field is used only in proofs and never eliminated into `Type`.
`ConZF/Graph/` holds the checked part so far. `Recursion.lean`:
predecessor-local recursion into stable predicates on a fixed carrier, for a
stable transitive relation with `SWF`, with no monotonicity, by the union of
all partial solutions
(`predicate_recursion`, `solution_unique`); a graph can use the resulting
predicate as its edge relation. `GSet.lean`: negative bisimulation and
membership, both stable, the equivalence laws, extensionality
(`GSet.ext`), and stable membership induction (`GSet.mem_induction`).
`Ops.lean`: the range of a small family, Separation, and the powerset, each
with its negative membership law (`mem_range`, `mem_sep`, `mem_powerset`);
the powerset carrier has a vertex for every predicate on the supplied
carrier. `Rank.lean`: rank is the transitive closure of the edges on the same
carrier, so no recursion produces the value; it is idempotent, respects
equivalence and membership, is an ordinal, and satisfies the recurrence in
membership form (`mem_rank_at'`); and for a fixed carrier `T`, every code, a
subset of `T` with a relation and an `SWF` proof, has height below
`univBound T` (`code_height_mem`). This is the semantic Hartogs mechanism:
the proof field is stable well-foundedness, not `WellFounded`.

`Faithful.lean` (the audit-critical lemma of conzf6): for a stable relation
`R` on a small type with `SWF`, a stable equivalence `E` for which `R` is a
congruence, and relational extensionality (equal predecessor profiles give
`E`), pointing the graph at two points gives equivalent graphs exactly when
`E` holds (`faithful_equiv`) and a member exactly when `R` holds
(`faithful_mem`). Stability of `R` is an explicit hypothesis, as the review
required: the bisimulation matches negatively and the transport back to an
edge uses it. Faithfulness preserves the represented structure only; it does
not identify collapsed values with ambient ones. `Sat.lean`: satisfaction of
the existing `Fml` over graph sets, with bisimulation as equality and graph
membership; stable, invariant under bisimulation, renaming, and bounds.
`Def.lean`: the definable powerset, one vertex per formula with a list of
*member* parameters (vertices below the root) and a bound on its free
variables so that the environment's default is unread, with `mem_Def`: its
members are exactly the subsets defined by a bounded formula with member
parameters. Review caught that a first version let parameters range over
every vertex of the carrier, so that re-rooting the powerset graph at its
copy of `G` gave a presentation of `G` whose `Def` was the ambient
powerset; the corrected `Def` respects bisimulation (`Def_congr`), the
parameter list transporting along a bisimulation one parameter at a time.
A transitive graph is included in its `Def`, which is transitive.

The native constructible hierarchy is now checked. `Ord.lean`: graph
ordinals, negative trichotomy, and normalization (`rank_equiv_of_isOrd`), so
the transitive closure of a presentation is a stable, transitive presentation
of the same ordinal; the semantic order on vertices, distinct from the raw
edges, with `SWF`. `Names.lean`: finite names `def' a φ n args` over a
presentation, validity, the earlier-stage graph of any proposed table (with
`SWF` for every table, since name edges decrease the birth), the stable and
predecessor-local step operator (`step_local`: agreement on rows below `d`
gives equivalent earlier-stage graphs at every vertex), the solved table by
predicate recursion (`table_eq`), and the hierarchy graph with `L a`.
`Hier.lean`: the earlier-stage graph agrees with the hierarchy below its
level, the members of a level are the values of valid names born below it,
a valid name denotes the subset of the level at its birth defined by its
formula with the values of its arguments (`nameVal_spec`), and the exact
recurrence in membership form (`mem_L_iff_Def`). `Levels.lean`: levels are
monotone, transitive, and presentation invariant (`L_congr_of_bisim`), all
from the recurrence and `Def_congr` with induction along the transitive
closure, without transporting names.

`Ordinals.lean`: the parameter-free formula `ordF` is correct over any
transitive graph set (`sat_ordF`); the ordinals of `L α a` are exactly the
rank of the presentation at `a` (`ordinals_of_L`, by stage induction: an
ordinal in `Def (L b)` is a subset of `L b` whose ordinals lie below the
ordinal at `b`, and that ordinal is itself named over `L b` by `ordF`), so
for an ordinal presentation `Ord ∩ L_α = α` by normalization
(`ordinals_of_L_root`). Two canonical parameter-free names are exported: the
ordinal at a stage (`ordName`) and the level itself (`levelName`), each born
at its stage and available at strictly later levels (`ord_mem_L`,
`L_mem_L`); nothing at stage `a` is claimed as a member of `L a`.

`Hartogs.lean` (conzf9), from the graph layer alone: an *injection relation*
from the members of `T` to the root predecessors of `X` is stable, respects
equivalence in both arguments, is total on `T`, and is inverse-unique; a
graph-set injection as a set of pairs would supply one, and pairs are not yet
built for graph sets, so this relational form is the current interface. The
pullback code lives on the subtype of vertices of `X` representing some
member of `T`, with membership pulled back; its stable well-founded induction
comes from ambient membership induction with the predicate quantified over
all representatives, selecting no inverse image (`Pullback.swf_rel`); and
the rooted graph at a representative *is* the represented member
(`Pullback.exact`), by membership induction on the member. This is the point
that distinguishes it from an elementary hull: full predecessor coverage
makes the collapse exact. So the code's height is `T` for an ordinal `T`,
every ordinal with an injection relation into `X` lies below the universal
bound of the carrier of `X` (`mem_univBound_of_injRel`), built before the
injection is opened, and the Separation cut `relHartogs X` is an ordinal
with the exact membership law (`mem_relHartogs`), no injection relation
into `X` (`not_injRel_relHartogs`), and extensional in `X`
(`relHartogs_congr`, by transporting a relation along a bisimulation of the
codomain, with no choice). The source-wide menu `menu a` is the range of
these bounds over the literal members of `a`: every member has, negatively,
an ordinal in the menu with no injection relation into it (`mem_menu`).

What the cutoff is, as review pointed out: an injection relation lets one
source member relate to several inequivalent targets, so classically it is a
surjection from a subset of `X` onto the source, and `relHartogs X` is a
Lindenbaum-type number rather than the ordinary Hartogs number; without
choice the two can differ. An ordinary injection gives an injection relation,
so the bound excludes ordinary injections once set-coded injections are
bridged, which is what the uncountability request needs; the exact ordinary
Hartogs cut would add functionality to the predicate and reuse the same
bound theorem. Applied to `ω`, `relHartogs ω` is an ambiently correct
witness, not a hull's internally uncountable collapsed ordinal. Its
constructibility waits on successor presentations.

`Transport.lean`: names over two presentations *correspond* along a
bisimulation when their births are related, their formulas and arities are
equal, and their arguments correspond pointwise (argument functions are
never compared for equality); every valid name transports negatively to a
corresponding valid name born at any match of its birth, matching each
argument beneath the matched parent and combining finitely many negative
choices (`transport`), and corresponding valid names denote equivalent sets
(`nameVal_equiv_of_nameEquiv`).

`Pair.lean`: unordered and Kuratowski ordered pairs (with injectivity), binary
products, binary unions and unions of a set, all as small ranges with negative
membership laws; and the reachable support of a graph set, which negatively
represents every member and is closed under members (`supp_of_mem`,
`supp_closed`).

`Monotone.lean` (conzf10, items 1 to 4 of the review): a subset
of a graph set `X` is a stable, extensional predicate on the points of `X`,
the vertices below the root (`Pt X`), and the operator laws are stated only
on such predicates. (The first version stated the laws on all vertex
predicates together with a containment law, which was contradictory: a
reviewer showed inflation on the constant true predicate placed the root
below itself. The repair moved the state domain to the point subtype and
removed both the containment law and the stable-edge hypothesis.) For a
monotone, inflationary, extensional operator and a seed, the history along
an ordinal presentation is the table solving the uniform recurrence
`A_β = S ∪ ⋃_{ξ<β} Φ(A_ξ)` (`hist_eq`) by `predicate_recursion` on the
transitive closure, as review suggested; the stages increase, are
extensional, respect equivalent stage vertices, stay below every closed
superset of the seed, and after a stationary stage every later stage equals
it (`persist`). Convergence uses `relHartogs (powerset X)` directly: were no
stage below it stationary, the map from stages to their subset states would
be an injection relation into the powerset (`exists_stationary`). The
stopping cut is the Separation cut of the nonstationary members of the
bound: an ordinal, a member of the bound, stationary, with every earlier
member nonstationary (`stopCut_mem`, `statSet_stopCut`), and the endpoint is
closed under the operator and contained in every closed superset of the seed
(`endpoint_closed`, `endpoint_least`). No stationary witness is extracted.
Two instances check applicability. Adjoining a fixed subset `C` has endpoint
`S ∪ C` (`endpoint_addOp`). The transfinite benchmark is the predecessor
rule on an ordinal `η` from the empty seed, a point admitted once all its
predecessors are: stage `β` is `{x ∈ η : x < β}` (`hist_predOp`), a stage is
stationary exactly when it is not below `η` (`stat_predOp`), so the
stopping cut is `η` itself (`stopCut_predOp`) and the endpoint is all of
`η`; as a byproduct every ordinal is a member of the relational Hartogs
bound of its powerset (`mem_relHartogs_powerset`). The operator is the
semantic update, not a set-coded rule table. The interface is split as
con20 suggests: `IsInfl` (stable, extensional, inflationary) suffices for
the history, persistence, convergence, and the stopping cut; monotonicity
(`Mono`) is a separate hypothesis used only for leastness. The certificate
is packaged: the state of a stage is a subset vertex of the powerset, the
history through the stopping cut is the range of the pairs `⟨β, A_β⟩`
(`histSet`, read back through injectivity of ordered pairs by
`histSet_row`), and `⟨γ, ⟨σ, C⟩⟩` lies in the envelope
`κ × (P(κ × P X) × P X)`, which depends only on `X` (`cert_mem_envelope`);
the reachable support of the envelope represents the certificate and all
its members (`cert_supp`, `supp_closed`). First-entry ranks (con19 §5,
con20): the rank of a point is the Separation cut of the stages at which it
is absent (`entry`), an ordinal, at most `β` exactly when the point is in
stage `β` (`hist_iff_entry`), at most the stopping cut on the endpoint;
equivalent points have equal ranks, and the rank graph over the endpoint
extends the certificate inside `envelope X × P(X × κ)` (`rankedCert_mem`).
The rank counts the first stage containing the point, so seeds have rank
zero and the law is `ρ(x) ≤ β`, rather than con19's successor-indexed
`ρ(x) < β`. Not done: the recurrence `ρ(x) = sup (ρ(z)+1)` for the
predecessor rule, which needs successor ordinals; the certificate
conditions as bounded formulas; con20's normalization theorem.

`Normalize.lean` (con20): judgements `J` and set-coded rules
`Rs ⊆ P J × J`; the rule operator admits a judgement once some rule for it
has all premises admitted, and the bounded induction from the empty seed
gives the least closed set `W` with first-entry ranks. A certificate for
`q` (`IsCert`) is an arbitrary graph set of nodes with an edge set, a
functional labelling into `J`, a root labelled `q`, local justification of
every node by a rule whose premises label predecessors, and the minimal-
member form of well-foundedness for every ambient subset; nothing bounds
its carrier or rank. Completeness (`endpoint_of_cert`) is the bad-node
argument, used only inside a stable goal. Decoding (`cert_norm`): a
judgement of `W` enters at its rank by an actual rule with premises of
smaller rank (`enter_rule`), so `(W, D, id, q)` with `D(u, j) :⟺ ρ(u) < ρ(j)`
is a certificate, well-founded by `∈`-induction on ranks (`normD_wf`);
`normalization` is the equivalence, `norm_mem_envelope` places every
normalized certificate in `P J × (P(J×J) × (P(J×J) × J))`, and the menu over
`W` is complete (`normMenu_complete`). This normalizes the unbounded
existential of the certificate fragment; it is not a faithful collapse of
the original certificate, and nothing here applies to arbitrary Π1 truth.
Not done: the certificate conditions as bounded formulas (`Sat`), the
syntax-directed compilation of positive specifications into rule sets, and
the constructible version.

Not yet formalized: shortlex and shortlex minimization across
presentations (needed only for name selection), coherent origin certificates,
the whole-class hull with faithful collapse and the local recurrence, and
from it the support bounds, internal powerset, full first-order Separation,
and the upward-absolute Replacement fragment of conzf7. The
interpretation should be packaged through validity of the syntactic ZF
axioms, not `ZFModel`, whose powerset and Separation fields are stronger
than the internal axioms of graph `L`. Even with those, full Separation and
Replacement in the graph `L` remain mathematical gaps, and nothing here
discharges the `PSet` obligation `BoundHyp`.

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

## Compactness: stable bar induction and a producer on the Cantor space

`Bar.lean` works on the negative Cantor space `powerset omega`: a point is
an actual subset of `ω`, its bit statements are stable, and Separation makes
a point out of any stable predicate on `Nat`. For a stable predicate `G` on
finite words closed under joining the two children, the *greedy* words take
`0` where `G` is refutable at the left child and `1` where it is
irrefutable: a predicate, not a choice of bits. The greedy real is the point
whose bit `n` holds when a greedy word of length `n+1` ends in `1`, by
Separation, and its prefixes are exactly the greedy words. Every greedy word
is bad when the root is, so a hit of `G` on the greedy real gives `G []`
(`root_of_hit`), and a bar over all points gives `G []` (`bar_induction`).
This is not the fan theorem for `Nat → Bool`: the bar must cover the
proposition-valued point.

For a relation from points to sets, local caps (an ordinal capping the
witness ranks throughout a cylinder, negatively) join by ordinal union
(`locCap_join`), so local caps everywhere give a source-wide cap
(`cap_of_bar`) with no function selecting them; and a cap exists iff the
greedy real of the local-cap predicate has a locally capped prefix
(`hasCap_iff`). The criterion identifies the remaining obligation at one
explicit point; it does not discharge it.

`FinObs.lean` discharges it for *finite-observation* specifications: every
witness at a point is, negatively, certified by a finite prefix and works
throughout its cylinder. Negative totality then gives a source-wide cap
(`cap_of_finObs`) and a finite witness menu, one finite list of sets,
singleton lists concatenated along the bar, that meets the witness class of
every point (`menu_of_finObs`); the list is in the conclusion, so finiteness
is certified. With functionality every output is bisimilar to an entry, so
the image is finite (`output_mem_menu`) and `rankBounded_of_finObs` gives
`RankBounded` for a finite-observation, negatively total, functional formula
on the source `powerset omega`; `rankBounded_envFml_of_finObs` bounds the
envelope instance of any finite-observation, negatively total formula, with
no functionality and without assuming that envelope formation preserves
finite observation. Nothing is computed and no generator is assumed; the
witness condition may have arbitrary quantifiers. Two restrictions are
essential: totality must hold at all negative points, including those made
by Separation, and the witness condition must not depend on the unseen
bits of the point. Without functionality the menu meets each witness class;
it does not cover every output in the sense of `Cover.lean`.

### The scope check: a countable source at the zero real

`CountableSource.lean` records exactly why the compactness argument stops
there. Start from any functional relation `Φ` on `ω`, possibly partial;
totalize it (`Tot Φ`: empty if no output, the singleton of the output
otherwise, a negative disjunction, no least rank and no first-order rank),
and lift it to the Cantor space (`Lift Φ`: empty at the zero real, `Tot Φ`
at the first `1` otherwise). The lift is negatively total and functional.
Every nonzero point has a local cap (`locCap_of_firstOne`): its cylinder
fixes the first `1`, where the lift is a single-input specification. And
`Φ` has a cap iff the lift has a local cap at the zero real iff the lift has
a source-wide cap (`countable_reduction`); the tail is bounded by the local
cap and the finitely many earlier inputs by combining finitely many negative
witnesses (`head_bound`). So totality, functionality, and local caps at every
other point do not discharge the local cap at the last point: proving it
would already solve the countable-source cap problem. This is a reduction,
not an impossibility result. The lift need not satisfy finite observation,
its zero branch being a condition on all bits, though for particular `Φ` it
may. Without functionality the local cap at a nonzero point supplies a
bounded witness throughout the cylinder, as `CapAt` asks; it does not bound
every output. The checked reduction concentrates an arbitrary
countable-source instance at zero; it does not reduce every `HG` source to
that case.

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

## The normal-form reduction

`EnvFml.lean` writes the envelope as a formula: `envFml ψ` says of `x`
(variable `0`) and `W` (variable `1`) that `W` is the set of witnesses of
`ψ(x, y, params)` of least rank, or empty, with rank by `rankFml`;
`sat_envFml` identifies its satisfaction in `HG` with `Env` of the witness
predicate. Envelope instances are total and functional (`envFml_total`,
`envFml_func`), so they are admissible with nothing to discharge. For a
functional `ψ` the envelope of an output is its singleton, whose rank exceeds
the output's, so a rank bound on the envelope instance bounds `ψ`
(`rankBounded_of_envFml`). Hence `EnvBoundHyp`, rank bounds for the envelope
instances alone, gives `BoundHyp` (`boundHyp_of_envBoundHyp`), and conversely `BoundHyp` applied to the
envelope formulas gives `EnvBoundHyp` (`envBoundHyp_iff_boundHyp`): the
normalization preserves the strength of the obligation. The double
negations stay in place; no uniform operator over formulas is involved. A
cap meeting each nonempty witness class of `ψ` at every input, supplied
negatively, bounds the envelope instance of `ψ` with no functionality
assumption on `ψ` (`rankBounded_envFml_of_cap`): every envelope output is
the capped witness set, a subset of `Vl κ`.

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
