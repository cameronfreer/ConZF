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
`ρ(x) < β`. The rank can equal the stopping cut (a single predecessor-free
node first enters at stage 1, which is also the stopping stage), so the
codomain of the rank is the bound `κ` (`entry_mem_bound`), not the stopping
cut. Not done: the recurrence for the predecessor rule, which with this
indexing reads `ρ(u) = (sup_{vRu} ρ(v)) + 1` (a leaf has rank 1; a node
above predecessors of unbounded finite rank enters at ω+1) and needs
successor ordinals; the certificate conditions as bounded formulas.

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

## The seeded model (con22 §2)

The label set `D` is used by the definability rule and the model only
through a few properties: extensionality, monotonicity in the source,
transitivity, containment of the source and of `ω`, closure under unordered
pairs, and containment of every set whose rank is included in an ordinal
source. These are the fields of the class `Budget` (`VLevel.lean`), the
standard label set is its instance, and `Reach.lean`, `ModelBase.lean`,
`CofinalCut.lean`, and `Model.lean` are generic in the budget; downstream
modules use the standard instance unchanged. `Seeded.lean` builds the
budget `seeded b` from a supplied set `b` (the standard label set around the
pair of the source and `b`), proves it contains the standard budget and
`succ (rank b)` at source `∅`, and proves identity-source reachability: every
nonzero ordinal `μ ≤ rank b` is reached from any of its elements by the
identity formula on the fixed domain `succ (rank b)`. Hence every ordinal up
to `rank b` is hereditarily good and `b` lies in the class of the seeded
budget. The generic model theorem gives, under `AccHyp` and so under
irrefutable excluded middle, an explicitly defined transitive class model of
`ZF` containing `b` (`hg_model_seeded`), with empty axiom reports.

The rest of the con22 route, as far as it goes. `AllGood.lean`: for an
interpreter for which every ordinal is hereditarily good, excluded middle
makes the glued root accessible, and the value of the materializing
recursion there is an actual ordinal term above every value of a supplied
functional ordinal-valued relation (`ordBound`, `mem_ordBound_of`); nothing
is extracted from a propositional existential. `Lift.lean`: the structural
lift to the next universe preserves and reflects bisimulation, membership,
and ordinals, commutes with successor, powerset, rank, and levels; an upper
subset of a lifted lower set has the lower representative `shrink`, its
lift being the subset (`lift_shrink`), the upper parameter occurring only in
the separating proposition; `U` is the set of lifts, `K` its rank, the
members of `K` are exactly the lifted lower ordinals (`mem_K`), `U` is the
level `V_K` (`mem_U_iff_rank`), and `K` has no lower representative.
`MixedHartogs.lean`: under excluded middle, an upper ordinal with a
set-coded injection into `lift a` lies below `lift (wfBound a.Idx)`, the
lower bound decoded from all well-founded certificates on the carrier of `a`
(`mem_lift_wfBound`); the injection is pulled back to a relation on the
lower carrier whose fields mention upper objects only in `Prop`, excluded
middle turns upper membership induction into accessibility, and full
predecessor coverage identifies the lift of the lower collapse of a point
with the original upper ordinal (`lift_tree`); hence `K` has no set-coded
injection into any of its members (`K_initial`). `Cofinality.lean`: the
interface `UpperModel` states exactly what is assumed of the upper class
`N`: extensional, containing lifted lower ordinals; a least-cofinal-map
relation that is extensional, unique, cofinal (inclusively), and exists
whenever some cofinal map of `N` does; abstract predicates `Inacc` and
`Reg`; and the classification of nonzero lifted lower ordinals not
inaccessible in `N` into the three cases (at most `ω`; smaller cofinality
with a map from a smaller lower ordinal; regular but not a strong limit,
with a map from an internal powerset `P ⊆ P(lift l)` of a smaller `l` with
`succ l` still below). The interpreter `cofI` reads the least cofinal map
`lift q → lift η` of `N` at `lift x`, with the target an argument and the
code only the domain; it respects bisimulation and is unbounded on `q`
whenever `N` has a cofinal map from `lift q` (`unb_cofI`); every nonzero
lower ordinal not inaccessible in `N` is reachable (`reachable_cofI`), the
third case with source `shrink (powerset l) P` in the budget at `succ l`;
so with no smaller inaccessible every lower ordinal is hereditarily good
(`cls_cofI`) and under excluded middle every functional ordinal-valued
relation on a lower source has a native bound (`ordBound_of_noInacc`). All
with empty axiom reports. Universes: everything is polymorphic in `u`; at
`u := 0` the lower sets are in `Type 1`, the upper sets and the interface in
`Type 2`, and nothing higher is used.

Two interface corrections after review: `Cof` is a partial cofinal relation
(a functional set of pairs, not necessarily total; `Cof empty Q empty`
holds), which is what `Unb` needs, and the least-candidate relation of the
interface is understood as minimizing partial cofinal graphs, with the
adapter `Cof.of_isFun` for total cofinal functions; the injection condition
of the mixed Hartogs bound is relational (`IsInjRel`: total with inverse
uniqueness, no functionality), with the adapter `IsInjFun.toRel` for
ordinary set-coded injections. Inaccessibility, regularity, strong limit,
and initiality in `N` are now explicit notions quantifying over the
functions and injections of `N` (`InaccIn` and friends), and the
classification fields of the interface are stated with them.

`Interval.lean` (con23): with the seeded budget around a lower set `b` and
the same interpreter, every nonzero ordinal at most `rank b` is reached by
the identity graph on its lift, a partial cofinal relation from
`lift (succ (rank b))` (`reachable_below`), and above `rank b` the three
cofinality cases apply; so under the interval hypothesis `NoGap` (no lifted
lower ordinal above `rank b` is inaccessible in `N`) every lower ordinal is
hereditarily good for the seeded budget (`cls_interval`) and every
functional ordinal relation has a native bound (`ordBound_interval`). The
explicit consequences: `K` is initial and a strong limit against relational
injections into subsets of powersets of its members, unconditionally under
excluded middle (`K_strongLimit`), with `ω ∈ K`; and regular against all
upper set-coded functions under the interval hypothesis
(`K_regular_of_interval`), by pulling a function `δ → K` back to a lower
ordinal relation on the lower representative of `δ` and bounding it
natively. The interval theorem (`inacc_interval`): under excluded middle,
for every lower set `b`, `N` has an inaccessible `ρ` with
`lift (rank b) ∈ ρ` and `ρ ≤ K`, since either some lifted lower ordinal
above `rank b` is inaccessible in `N`, or the interval hypothesis holds and
`K` is inaccessible in `N` (ambient inaccessibility against all upper
functions implies the `N`-relative notion). Its only premise beyond excluded
middle is the interface `M`. At one fixed height `K` every application may
return the same inaccessible, namely `K` itself; distinct witnesses need the
increasing universe heights and disjoint intervals in one common class of
con23, which are not formalized. Changing the seed alone does not give
distinctness.

`Cardinal.lean`: the first-order cardinal interface. Formulas with de
Bruijn variables for singletons, pairs, `⟨x, y⟩ ∈ f`, transitivity and
ordinals, functions and injections (every member a pair, so these imply the
ambient `IsFun` and `IsInjRel`, which allow non-pair junk), internal
powersets, `ω < κ` (a nonempty successor-closed member), regularity,
initiality, strong limit, strong inaccessibility (`inaccF`), and the axiom
of choice (`ac`, a choice function on any set of nonempty sets); the theory
`ZFCI = ZF + ac + ∃ inaccessible`. The bridges are proved for a transitive
class respecting bisimulation and closed under unordered pairs
(`TransClass`) with environments in the class: pair and ordinal formulas are
exact, the function, injection, and powerset predicates imply the ambient
ones, and the main bridge is `InaccIn N κ → Sat N (inaccF) (κ, e)`; the
converse is not proved. Conditional consistency (`con_ZFCI`): under
excluded middle, for an interface `M` whose class is a `TransClass` and
validates the syntactic ZF axioms and `ac`, `ZFCI` is consistent, by the
interval theorem at seed `∅` and `Con.of_model`. All premises are explicit.
Height coherence for two universes (`rank_lift_U`, `lift_K_mem_K`): the lift
of `U` is by definition the set of doubly lifted sets, so `rank (lift U) ≈
lift K` and `lift K ∈ K` one level up; a two-witness theorem in one common
class is not formalized, because transporting inaccessibility from the
induced lower class to the common class needs functions in the class to
have lower representatives, which the junk-tolerant `IsFun` does not give
without Separation in the class.

The internal `L` route (conzf15), gate 1. `Relativize.lean` (ported from
the supplied draft): `restrictClass d φ` restricts every quantifier of a
native formula to a unary formula `d`, and satisfaction of the relativized
formula in `M` is satisfaction of the original in the class of members of
`M` satisfying `d` (`sat_restrictClass`), uniformly over native syntax, so
validity transfers; no truth predicate for a proper class is encoded.
`InternalZF.lean`: the interface `SynZF` is a class that is stable,
respects bisimulation, is transitive, contains `ω`, and validates the
syntactic `ZF` axioms. Stability is explicit, as review asked: internal
existence gives double-negated existence, and identifying a witness with a
native set gives `¬¬M t`. From syntactic validity alone (no ambient closure)
the class is closed under separation by any native formula with parameters
in the class (`sepM`), the empty set, unordered pairs, pairs, and unions,
has internal powersets (`powM`: a member whose members in the class are
exactly the subsets in the class, not the ambient powerset) and internal
products (`prodM`), and has a collecting member for every functional native
relation (`replM`). Graph normalization: the restriction of a member to an
internal product is a member (`cleanM`), which cleans any junk-bearing
function or cofinal relation to a pure one in the class with the same
pair-edges (`normalizeFun`, `normalizeCof`); and in a class validating the
choice sentence every member of nonempty members has a pure choice
function in the class (`choiceFun_of_ac`), which records that the functional
choice relation of `ac` is an acceptable formulation of choice. All with
empty axiom reports.

`OmegaRec.lean` (the reusable internal ω-history theorem, item 3 of the
conzf16 review): for a native step formula that is functional and total on
the class and a start `a`, the partial sequences (`partSeqF`: pure set-coded
functions on a numeral with `p(∅) = a` and consecutive values related by the
step, so junk cannot break uniqueness) exist for every numeral
(`partSeq_exists`, by external induction on the numeral, the extension step
using totality of the step) and agree at every numeral where both are
defined (`partSeq_agree`, using functionality); collection over `ω` of the
partial sequences on successors, by the internal Replacement of the class
applied to the fixed formula `collectF`, gives the sequence specified by the
single formula `seqF step` (variables: the sequence, the start, `ω`, then
the step's parameters). The sequence exists in the class (`seq_exists`), is
unique up to bisimulation (`seq_unique`), and satisfies the recursion
equations (`seq_spec`: pure pairs on `ω`, functional, total on `ω`, starting
at `a`, consecutive values related by the step). Every bridge is proved for
a transitive pair-closed class with the step renamed into position
(`sat_stepRen`, `sat_partSeqF`, `sat_seqF`). Empty axiom reports; one core
congruence lemma (`iff_congr`) had to be avoided because it uses `propext`.

`Reflection.lean` (item 1 of the conzf16 review, ported from the supplied
syntax draft with the relativizer reused): the computed free-variable bound
`fv` with `Bound (fv p) p`; the counterexample requests of the raw universal
nodes, every request having its witness at variable `0` and parameters at
`1, …, arity` (`requests_valid`); the capture formula of a request, with
free variables the source level `A` and the target level `B`; the closure
conjunction over the requests of a native finite list; the good-stage and
least-next-stage formulas over supplied unary and binary templates; set
relativization and the reflection sentence. Scope: renaming with a bounded
renaming, relativization preserves every bound including `0`, and
`Bound 2 (capture ell m)`, `Bound 2 (nextF ell level Δ)`,
`Bound 1 (reflectionAt ell Δ)`. Semantics: conjunctions, iterated universals
as a recursive predicate, guards, the two-slot instantiation, and the exact
capture law (`sat_capture_body`): inside the parameter binders, with the
parameters in `A`, if some member of the defined class satisfies the
request's matrix in the defined class, some such member lies in `B`. The
internal existence of the next stage and the reflection theorem itself are
not proved.

`Assign.lean` (gate 2, step A): an assignment into a domain set `A` is a
pure set-coded function from a numeral `n ∈ ω` into `A` (`IsAssign`, formula
`assignF`, bridge `sat_assignF`), so the value at a numeral is read by pair
membership and no arithmetic on indices is needed. The set of all
assignments into a member of the class exists (`assignSet_exists`: the
separation of the internal powerset of the internal product `ω × A` by the
assignment formula, whose members are exactly the assignments in the class).
Consing a value shifts the domain by one (`IsCons`, formula `consF`, bridge
`sat_consF`), the cons of an assignment in the class exists in the class on
the successor domain (`cons_exists`, by separating the shifted copy from the
product and adjoining the head), and reading values through a cons behaves
as `Env.cons` (`IsCons.reads_zero`, `IsCons.reads_succ`). Native environments
are packaged by `pack n e`, which is an assignment when its entries lie in
the domain (`isAssign_pack`), commutes with cons (`isCons_pack`), and lies in
the class when its entries do (`pack_mem`); conversely every assignment on
the numeral `n` is, negatively, such a package (`exists_pack`), so legal
assignments relate to native environments by negative reconstruction inside
stable goals, with no decoder. Empty axiom reports. The remaining steps of gate 2: the code sets and truth tables as
one joint ω-recursion using `seqF`, the `SetSat` formula quantifying over
that sequence, and its uniform correctness over native formulas.

`Codes.lean` and `Step.lean` (gate 2, checkpoint 2): numeral formulas
read `x ≈ ofNat k`, and the five code-shape formulas read the exact shapes
of `Fml.enc` (a numeral tag paired with the payload; the `⊥` code requires
an empty payload), so tag distinctness and pair injectivity give constructor
disjointness and, with `enc_inj`, unique decoding of represented codes. The
guarded step follows conzf17: a state is a pair of a scope table (code,
length) and a truth table (code, assignment); the new scope table admits
atoms with indices below the length, `⊥`, implications whose children are
already scoped at the same length, and universals whose body is scoped at
the successor length (`validBodyF`); the new truth table uses the **new**
scope table as a guard and the **old** truth table for the children
(`truthBodyF`), so an implication is only evaluated once both children have
values and a universal with a malformed body is rejected even over an empty
domain. The step formula `stepF` (input state, output state, then the
domain, the assignment set, and `ω`) says both new tables are pure and
satisfy these membership laws; its ambient reading `IsStep` is proved exact
(`sat_stepFormula`, through clause-by-clause bridges), the step is
functional up to bisimulation (`IsStep.unique`), and it is total in the
class (`step_exists`: the new scope table is separated from the product of
a code carrier built from the domain of the old table with `ω`, and the new
truth table from the product of that carrier with the assignment set). Empty
axiom reports.

`History.lean` (gate 2, checkpoint 3): the step is totalized outside the
pairs (`totStepF`: on a pair state the step, elsewhere the output `∅`), so
it is functional and total on the class and the ω-recursion of
`OmegaRec.lean` from `⟨∅, ∅⟩` gives the history `H` in the class
(`history_exists`), with the row at each stage a pair of tables in the class
(`row_exists`), rows unique (`row_unique`), and consecutive rows related by
the step (`row_step`). The invariants, by induction on the stage
(`invariants`): a row `⟨enc φ, ofNat n⟩` is in the scope table exactly when
`ht φ ≤ d` and `Bound n φ` (`vbody_enc`, by cases on the constructor with tag
distinctness), every scoped row negatively decodes to a native formula and
a numeral (`vbody_decode`, the converse the review asked for), and a row
`⟨enc φ, pack n e⟩` with entries in `A` is in the truth table exactly when
`ht φ ≤ d`, `Bound n φ`, and `φ` holds in the set structure `A` at `e`
(`tbody_enc`: implications use the guard to apply the induction hypothesis
to both children, universals use uniqueness of the cons and the package of
the extended environment, which lies in the assignment set). Empty axiom
reports.

`SetSat.lean` (gate 2, checkpoint 4): `ω` as the least inductive set
(`omegaF`, bridge `sat_omegaF` using the supplied `ω` of the class), the
assignment set (`assignSetF`), and the start state (`emptyStateF`) as
formulas; the set-satisfaction formula `setSatF` (free variables the
domain, the code, the assignment) says there are `ω`, the assignment set,
the start state, and a history satisfying the sequence formula for the
totalized step, renamed into position with every unused parameter slot
pointing at the bound `ω` so that no bound lemma for the sequence formula
is needed, with a stage whose truth table contains the row. **Uniform
correctness** (`setSat_correct`): in a `SynZF` class, for every native
formula `φ`, length `n`, and environment with entries in a member `A`, the
class satisfies `setSatF` at `(A, enc φ, pack n e)` exactly when `Bound n φ`
and `φ` holds in the set structure `A` at `e`; hence any two such classes
agree (`setSat_absolute`). The empty domain and the empty assignment are
ordinary cases, and malformed codes never enter the tables. This closes
gate 2 of conzf15 with empty axiom reports.

Gate 3 (con28, the guarded internal `Def`). `ScopedCode.lean`: the formula
`scopedCodeF` (code and length, `Bound 2` by decision) reads the scope
component of the history over the empty structure; exact readback
(`scopedCode_correct`): for members `q, r`, it holds exactly when,
negatively, `r ≈ ofNat n`, `q ≈ enc φ`, and `Bound n φ`; both directions
cover arbitrary codes through the decoding of scoped rows.
`DefAdapter.lean`: the generic adapter of con28 for any evaluator `S`
(`Bound 3`) and guard `C` (`Bound 2`): the evaluation is "some cons of `x`
onto the package satisfies `S`", a definable member is the value of a pure
function package `p : n → A` with a code scoped at `succ n` (the pure
`CardF.funF`, not the junk-tolerant `IsFun`, with the `ω` guard dropped as
con28 shows it redundant), and the family formula says `B` is the family.
Generic internal existence (`defF_exists`) is the outer Separation of an
internal powerset, generic uniqueness (`defF_unique`) is extensionality, and
the model-relative membership law (`mem_of_defF`) describes the family
through the first-Separation values; none of this uses correctness of
`S` or `C`, and with `C` always false the family is empty. `Def.lean`: the
instantiation `defPowF := defF setSatF scopedCodeF` (`Bound 2` by decision);
the ambient `Definable A z` (negatively `z ≈ {x ∈ A : φ(x, e)}` for a native
`φ` bounded by `n + 1` and entries in `A`) and the native
`defPow A := sep (Definable A) (powerset A)` with exact membership; the
value of a native package is the definable subset (`valueOf_pack`, using
uniqueness of the cons, the package of the extended environment, and
`setSat_correct`), packages correspond to definable subsets
(`package_iff_definable`, using the scoped-code readback and negative
reconstruction of the package), hence the exact correspondence
(`sat_defPowF`), internal closure (`defPow_mem`), congruence in the domain,
absoluteness between classes containing the data (`defPowF_absolute`),
`defPow ∅ ≈ {∅}`, `A ∈ defPow A`, `∅ ∈ defPow A`, and for transitive `A` both
`A ⊆ defPow A` and transitivity of `defPow A`. Monotonicity of `defPow` in
the domain is not claimed. Empty axiom reports throughout.

Gate 4 (relational level histories). `LHier.lean`: a level history on `α` is
a pure, total, functional graph `h` on `succ α` (`mapF`) whose rows satisfy
the uniform recurrence (`recF`): `x ∈ h(β)` exactly when, negatively, some
`γ ∈ β` and some row `h(γ)` have `x ∈ defPow (h γ)`. The history formula
`lhistF` has its exact ambient reading (`sat_lhistF`) over a `SynZF` class;
the level relation `Level M α A` says some history in the class has the row
`(α, A)`. Overlap compatibility (`lhist_agree`): two histories on internal
ordinals agree on every common index, by `∈`-induction using congruence of
`defPow`. Existence (`lhist_exists`) is `∈`-induction: collect the histories
of the members of `α` by Collection, take their union `U`, form the new row
by Collection of `defPow` over the rows of `U`, and adjoin it; uniqueness
(`lhist_unique`, `level_unique`) is agreement at the top row. Restriction
(`level_of_row`): the rows of a history at indices up to `γ ∈ succ α` form
a history on `γ`, so every row is a level. Hence the recurrence at levels
(`level_rec`) and the exact laws: `L_0 = ∅` (`level_zero`),
`L_{succ β} ≈ defPow L_β` (`level_succ`), and for a nonzero
successor-closed ordinal `L_λ = ⋃_{β ∈ λ} L_β` (`level_limit`).
Transitivity and monotonicity of the levels are proved jointly by
`∈`-induction (`level_trans_mono`) from transitivity of `defPow A` and
`A ⊆ defPow A` for transitive `A`; no monotonicity of `defPow` in the
domain is used. Empty axiom reports throughout.

Guarded interface and constructibility. `Constr.lean`: the unguarded
`lhistF` and `levelF` do not force an ordinal index (with `1 = {∅}` and
the non-ordinal `a = {1}`, the rows `1 ↦ ∅, a ↦ {∅}` satisfy the recurrence
on `succ a`), so the exported `ordLhistF` and `ordLevelF` (`Bound 2` by
decision) conjoin the ordinal formula, and their readings carry `IsOrd`.
Both components of a level are in the class (`level_mem_class`, by
stability of the class). The ordinal formula is exact over any transitive
set structure without pair closure (`sat_ordF_set`), so an ordinal `ξ`
lies in `L_α` exactly when `ξ ∈ α` (`ord_mem_level`, by `∈`-induction on
`α`: forward through the recurrence and `ξ ⊆ γ ⇒ ξ ∈ succ γ`; backward
since `ξ = {x ∈ L_ξ : Ord(x)}` is definable in `L_ξ`); hence
`α ∈ L_{succ α}` and `L_α ∈ L_{succ α}`. Levels are absolute between
`SynZF` classes containing the index (`level_absolute`): `IsLHist` is
class-independent, so a history supplied by the second class agrees with
the given one. Constructibility (`constrF`, `Bound 1` by decision): `x`
lies in some ordinal level; the class `Constr M` has exact membership
(`sat_constrF`), is stable, respects `≈`, is transitive (`Constr.trans`),
lies inside `M`, and contains every ordinal of `M` (`constr_of_ord`, via
`ξ ∈ L_{succ ξ}`) and every level. Empty axiom reports throughout.

The constructible class as a model of the axioms other than Separation.
`ConstrAx.lean`: `Constr M` is the class defined over `M` by `constrF`
(`constr_iff_definedClass`), so the uniform relativization applies
(`sat_constr_iff`). The least-stage formula `leastF` (`x` lies in the
level at `γ` and in no level below) is functional by trichotomy of ordinals
and total for constructible `x` by `∈`-minimality below a supplied stage.
The level bound (`level_bound`): a member `B` of `M` whose elements are
constructible is included in one level; the proof collects the least stages
by Collection in `M`, keeps the ordinals among the collected values by
Separation in `M`, and takes the successor of their union. The bound says
nothing about constructibility of `B` itself. Pairing and union in `N` are
definable subsets of a bounding level (`constr_of_definable`); Power Set
forms `{y ∈ P_M(a) : N(y)}` in `M`, bounds it in a level `L_γ` (which
contains `a`), and takes `{y ∈ L_γ : y ⊆ a}` (`powN`, the exact internal
powerset law). Collection in `N` (`replN`) relativizes the native formula
to `N`, collects in `M` the relation "`y` constructible and `ψ^N(x, y)`",
separates the constructible outputs, and uses the bounding level as the
witness. `valid_nonsep`: every axiom of `ZF` other than the Separation
schema is valid in `N`. All constructions use Separation and Collection in
`M`; the axioms of `N` are conclusions. Empty axiom reports throughout.

Reflection and the constructible model. `ReflectN.lean`: iterated
quantifiers read as quantification over a finite prefix of the environment
(`sat_allN_pre`, `sat_exN_pre`), and a formula with its parameters read off
an assignment package (`withPackF`, exact for packages of native
environments). The least-witness-stage formula `leastWitF` says the stage is
the least one whose level contains a constructible witness of the request
at the packaged parameters; it is functional by ordinal comparison and total
for active tuples by `∈`-minimality below a supplied stage. Bounded capture
(`capture_bound`): Collection in `M` over the internal set of assignments
into `A` collects the least stages, Separation keeps the ordinals, and the
successor of their union bounds the witnesses of every parameter tuple from
`A`; the zero-arity case is the empty assignment. The compiled formulas read
exactly (`sat_capture`, `sat_closes`, `sat_goodF`, `sat_nextF`), and the
next good stage exists (`next_exists`, by the finite union of the bounds
and `∈`-minimality among the good stages up to it) and is unique. The step
`stepN` totalizes `nextF` with the identity on non-ordinals; the history is
the internal ω-sequence of that step (`hist_exists`, `hist_unique`,
`hist_spec` from `seq_spec`), a pure graph on `ω` whose orbit from an ordinal
stays ordinal (`hist_ord`), with consecutive rows related by `NextStage`
(`hist_next`), hence strictly increasing, and rows included along the index
order (`hist_le`). The supremum of the rows (`sup_spec`) is a member of `M`,
a nonzero limit above the start, with the rows cofinal in it; every member
of its level lies in the level of some row (`sup_fit`), and finitely many
lie in one row level (`sup_fit_finite`). Reflection at the supremum
(`reflect_at_sup`) is by induction on the formula: for a universal, a
failed instance at a constructible value is an active counterexample
request whose parameters fit into a row level, capture at the next row
supplies a constructible counterexample already correct in `N`, and that
counterexample lies in the level at the supremum, contradicting the
universal there. The reflection theorem (`reflection`) is uniform in the
native list. Separation in `N` (`sepN`): the finitely many parameters lie in
one level, reflection above it gives a level `B` reflecting the formula,
and the separated subset is the definable subset `{z ∈ B : z ∈ a ∧ ψ}` of
`B`. With `valid_of_sep`, **`synZF_constr : SynZF (Constr M)`**: the
constructible class of a syntactic model is a syntactic model. Only `SynZF M`
is assumed; no excluded middle or choice enters. Empty axiom reports
throughout.

The concrete constructible upper class and the assembly. `UpperN.lean`: a
stable, bisimulation-respecting model of `ZF` is a syntactic `ZF` class
(`SynZF.of_zfModel`). At the upper universe, the seeded hereditarily-good
class with seed `K` is such a model under the accessibility hypothesis of
that universe (`MU`, `synZF_MU`), and its constructible class `NL` is a
syntactic `ZF` class (`synZF_NL`) containing `K` (`NL_K`), every lifted
lower ordinal (`NL_lift_ord`), and the identity graph on each of its
members (`idGraph_mem`, by Collection and Separation in the class). The
classification fields hold for any syntactic class, with no choice and no
canonical order (conzf16 §A5, §A7): regularity implies initiality
(`initialIn_of_regularIn`: the zero-totalized reverse of a relational
injection of `κ` into a member is a function of the class covering `κ`,
which regularity would bound) and limitness (`succ_mem_of_regularIn`: the
constant function at a predecessor would be bounded); the identity graph on
a nonzero ordinal at most `ω` is a partial cofinal graph from `ω`
(`cof_idGraph_le`); failure of regularity supplies negatively an unbounded
function from a member, cofinal by ordinal comparison
(`cof_lt_or_reg_of_synZF`); a regular non-inaccessible above `ω` fails
strong limit, and the reverse of the supplied injection restricted to
`P × κ` is a partial cofinal graph from `P`, with `succ lam` still below by
limitness (`cof_powerset_of_synZF`). Specialized to lifted lower ordinals
through `mem_lift`, these discharge every field of `UpperModel` except the
least-cofinal-relation interface: `upperModel_of_leastCof` takes only
`LeastCof` and its four laws, and `con_ZFCI_of_leastCof` states the
conditional consistency with every outstanding assumption visible: excluded
middle (which yields the accessibility hypothesis), the least partial
cofinal relation of `NL` with its laws, and validity of choice in `NL`.
Empty axiom reports throughout.

Choice and the cofinality selector from finite definition programs (conzf20,
con31–32). `Words.lean`: ordinal words and shortlex, linear up to
bisimulation (`oword_trichotomy`); the minimum principle (`minWord`): an
inhabited stable class of words of the class has a least member, obtained by
minimizing the successful length below a supplied witness and then
extending a prefix coordinate by coordinate with the least ordinal still
permitting success, each minimization by `∈`-minimality below a supplied
candidate, so no class of all words is collected; the minimum is unique.
`Programs.lean`: a program is an ordinal word evaluated by a stack machine
(a token below `9` is an opcode, any other ordinal pushes itself); the
opcodes build the codes of formulas, `∅`, successors, and packages by cons,
and the definition instruction pops a stage, a code, and a package and
pushes the value of the package at the level of the stage (the first
Separation of the guarded `Def` adapter). Stacks, steps, runs, and
denotations are pure finite functions with fixed native formulas and exact
readings (`sat_stepF`, `sat_runF`, `sat_denF`); the denotation is functional
up to bisimulation (`Den.unique`, by induction along the history with
determinism of the step); there are no pointers, so programs concatenate
without shifting (`Ext.append`), and every constructible set of the class
is the denotation of a program of the class (`coverage`, by hierarchy
induction: the parameters' programs, the package by cons instructions, the
code, the stage, and the definition instruction). `ChoiceN.lean`: the
constructible class is its own constructible universe (`constr_constr`, by
level absoluteness), so the program minimum is a first-order definable
selector: the least cofinal graph is the denotation of the shortlex-least
program denoting a cofinal graph (`LeastCofN`, with existence by coverage
and `minWord`, uniqueness by uniqueness of the minimum and functionality of
the denotation, congruence, and the `Cof` property), and the choice graph is
one Separation of `a × ⋃a` by the selector formula `pickF` (`valid_ac`).
Hence `upperModel_NL` needs no further input, and **`con_ZFCI_of_em`: the
consistency of `ZFC + ∃ inaccessible` from excluded middle alone**, with
empty axiom reports. The seeded ambient model is not claimed to satisfy
choice; choice is proved in its constructible class, and no extra universe
enters.

The pointwise endpoint (con33). `MixedHartogs.lean`: the pullback order is
accessible below any accessible upper ordinal mapped to a point, with the
existential of the carrier's guard eliminated into the propositional `Acc`
goal (`pull_acc_of_acc`), so the mixed Hartogs bound holds from actual
accessibility of the source (`mem_lift_wfBound_of_acc`) and, its conclusion
being stable, from negative accessibility. With `NNAccK`, negative
accessibility of `K` in the upper universe, `K` has no relational injection
into the lift of a lower set, any injecting upper ordinal is below `K` by
comparison and restriction of the injection (`mem_K_of_injRel`), and `K` is
initial. `Interval.lean`: `K` is a strong limit from `NNAccK`
(`K_strongLimit_of_nnacc`); actual accessibility of `K` gives lower
membership accessibility through the rank map (`lower_acc_of_acc_K`), hence
lower `AccHyp`; under the interval hypothesis the exact image of the
definability rule's Replacement bounds every functional ordinal-valued
relation on a supplied source by its rank (`ordBound_interval_nn`), so `K`
is regular (`K_regular_of_interval_acc`); and the interval theorem holds
with a negatively existential conclusion, the split on a lifted inaccessible
above the seed being by stability (`inacc_interval_nnacc`). `Cardinal.lean`:
`con_ZFCI_of_nnacc`. `Endpoint.lean`: pointwise accessibility of the
hereditarily good ordinals of the seeded upper budget gives `NNAccK` (the
seeded class contains its seed, whose rank is itself) and the syntactic
class `MU`, hence **`con_ZFCI_of_pointwise`: the consistency of
`ZFC + ∃ inaccessible` from that single premise**. Alternatively it suffices
to supply the two ingredients separately: the syntactic class from the upper
accessibility hypothesis (`con_ZFCI_of_upper_accHyp`, which already yields
negative accessibility of `K`) or from a bound producer for the seeded upper
budget together with `NNAccK` (`con_ZFCI_of_bounds_nnacc`); the reverse
implication to pointwise accessibility is not established. Corollaries from
double-negated well-foundedness of upper membership, from irrefutable
excluded middle (`con_ZFCI_of_not_not_em`), and from excluded middle. Universe levels are
explicit: the lower universe is `0`, the upper is `1`. Empty axiom reports
throughout. The remaining question is the pointwise accessibility premise
itself; this refactor does not establish unconditional consistency.

The arithmetic endpoint. `ProofCode.lean`: a Cantor pairing without
division (`pair`, with the inverse `unpair` computed by a bounded search
and injectivity by monotonicity of the triangular numbers), codes of
formulas (`encF`) and of proof trees (`encP`) with fuelled decoders and
exact round trips, the conclusion of a proof tree by structural recursion
with explicit schema-instance tags for Separation and Replacement
(`concl`), and the recursive Boolean checker `checkZF`, which decodes a
number and tests whether the coded conclusion is `⊥`. Soundness is
structural recursion on the code, completeness is induction on the
derivation using only propositional existence of a code, and the bridge is
`prf_fls_iff_code : Prf ZF ⊥ ↔ ∃ n, checkZF n = true`, so consistency is the
`Π⁰₁` sentence `∀ n, checkZF n = false` (`con_iff_checker`). A narrow
lesson from this file: the particular definitions first written with
overlapping wildcard patterns (`| _, _ => none`) compiled, on this
toolchain, to matchers carrying propositional extensionality, so those
definitions use exhaustive non-overlapping patterns instead; overlapping
patterns are not forbidden in general, they are checked case by case by
the axiom report. The reports are empty.

The decoder-capacity tranche (con46–47). The remaining unconditional
obligation is one rank bound, and these files locate it exactly for one
formula. `OrdDecode.lean`: the Σ₁ ordinal decoder `decodeF`, saying that
a diagram `⟨A, r⟩` is order-isomorphic to the ordinal `α` by an onto pure
map `f`, with one unbounded existential (over `f`) and every other
quantifier membership-bounded, certified by the bounded-formula syntax
`BForm` (absolute between any transitive class and the universe by
transitivity alone), `Bound 2` by `decide`; its exact reading in any
transitive class with the class guards on the three witnesses explicit
(`decode_read`), uniqueness of the decoded ordinal and even of the
isomorphism graph (stable membership induction; injectivity from order
reflection), and Σ₁ upward absoluteness. `DecodeSpectrum.lean`: the exact
ambient spectrum, the ordinals with a pure injection into the base
(`decoded_spectrum`; the diagram of an injection is its active range and
the transported order, both by Separation, and the same injection is the
isomorphism); ambient barriers (`Barrier`: an ordinal admitting no pure
injection into `U`) as exact strict caps and as exact collecting sets;
over `HG`, closure of `HG` under subsets, unions, powersets and products
before its model theorem, the `HG` domain of an `HG` injection, the reading
of `decodeF` in `HG`, the exact `HG` spectrum, and
**`barrier_iff_rankBounded`: at an `HG` base, the instancewise rank-bound
obligation `RankBounded decodeF e (diagrams U)` of the model's Replacement
clause is exactly negative existence of an `HG`-relative barrier**. This is
a reduction of the obligation to one ordinal, not a producer of that
ordinal; a supplied barrier improves to an `HG` barrier through the
unchanged Replacement consumer. `DecoderCap.lean`: at a successor-closed
rank stage, `V_η` is closed under the constructions used, so the decoder is
read exactly there (`sat_decode_at_limit`, downward absoluteness of this one
formula, not a general principle); every successor is reached from `0` by
the parameter-free `maxOrdF` on the source `{∅}`, and every successor-closed
ordinal above `λ U = rank (diagrams U)` embeddable in `U` is reached from
`λ U` by `decodeF` on `diagrams U`, keeping the original outputs
(`decoder_reach`); hence **`controller_le`: the least controller of every
ordinal embeddable in `U` is at most `λ U`**, with no bound on the decoder's
outputs assumed or negated; one native library `D (succ (λ U))` and a fixed
small label type cover every available child, and the covered children stay
cofinal (`cofinal_small_children`); and `HG` saturation, `injectable_hg`:
every ordinal embeddable in an `HG` base is `HG`, so at `HG` bases the `HG`
and ambient spectra and barriers of the decoder coincide
(`rankBounded_iff_ambient_barrier`). `DecodeGraph.lean`: the graph
checkpoint. Pre-sets embed fully faithfully into graph sets by structural
recursion on the tree; the rule assignments of the successful outputs glue
into a coherent assignment whose targets all embed in `U` and whose
controllers are all below `λ U`; the graph on the fixed small carrier of
label lists has `SWF` from `Desc` by stable membership induction, not `Acc`,
and no `Acc` is constructed. The raw pruned graph need not denote the
original ordinal, since only cofinally many children are kept; its rank does
(`graphNode_exact`), so every original decoded ordinal, and its rank, is a
member of the graph ordinal `decoderGraphHeight U`
(`original_rank_mem_graphHeight`), a graph-valued majorant that is not a
pre-set. `collecting_of_acc` records exactly what native accessibility of
the glued relation would add, namely Replacement's collecting set; that
hypothesis is not discharged. Empty axiom reports throughout.

Explicitly open after this tranche: any common bound on the decoded
ordinals, including at the base `U = ω`, where a barrier alone would not
close the route; completeness for arbitrary formulas, since only this one
formula is read; and the extension of the construction from the specific
supplied base to arbitrary bases.

The native majorant compiler (con42). `Majorant.lean`: a certificate
language `Plan` whose interpretation is an actual formula in the branch's
convention (input `0`, output `1`, parameters from `2`): copying the input
or a parameter, an element or subset of the input, the internal powerset
formula, the union, relational composition and image, both capturing the
original input as a parameter, conjunction with an arbitrary native test,
and disjunction. `Plan.bound` computes by recursion a native envelope of
all successful outputs from an envelope of the source and envelopes of the
parameters (`𝒫² (⋃ A)` for the internal powerset, `𝒫 (B_p (A :: P, ⋃ A))`
for an image, and so on), and `Plan.sound` proves in any transitive class
that every output lies in it, with no stability, closure, functionality,
accessibility or model premise; a guard's test is never evaluated. A
`Certificate ψ` carries the equation `plan.formula = ψ` checked by Lean, so
the bound is on the original matrix. For the actual interpreter this gives
a native ordinal bounding all output ranks on a source, uniform in the
stage (`isat_original_rank_bound`), and over `HG` the instancewise rank
bound and the collecting set through the unchanged consumers
(`certifiedRankBounded`, `certifiedReplacement`). The checked nested
example is `Image (Image (Guard (Compose Power Power) T))` for an arbitrary
test `T`, which may be unbounded and negative: its envelope is
`𝒫⁵ (⋃³ s)` up to the identity `⋃ 𝒫 Y ≈ Y` (`stress_envelope`), an image
formula is functional in any transitive class, and `stress_replacement` is
its `HG` Replacement instance from `HG` of the source and parameters alone.
This is an unconditional producer for the certified fragment; the
ordinal-decoder outputs are not built by these constructors, so it says
nothing about the barrier.

Two additions from conzf23. `Covered.lean`: a supplied native set `Y`
whose members are `HG` outputs of one partial functional relation on an
`HG` source, with negative source names, is `HG`
(`hg_of_definably_covered`): its own rank is the cap, the cofinal cut is
hereditarily good at every cap, and each member's rank lies in the cut. `Y`
is data; the lemma does not turn `∀ x, ¬¬∃ y, R x y` into a family. The
range of an actual family of outputs is the special case. For the certified
fragment the envelope itself is `HG` on `HG` data, so the exact relational
image `outputSet` of a certified matrix is an `HG` set with the exact
membership law, with no functionality or totality premise. `Witness.lean`:
witness menus, small index types with payloads of any size and negative
inhabitation `Ready`. From an actual family of ready menus of witnesses
with evidence, one per literal index of the source, the native `range` over
the sum of the indices is a collecting set satisfying both clauses of Strong
Collection with the evidence retained (`collection_spec`); this interprets
Collection from a realizer of its premise and does not produce that
realizer. For a stable functional specification, a ready menu of correct
witnesses contracts to a correct witness (`contract_spec`): for the
decoder, menus are no weaker than witnesses. Typed fusion of large semantic
realizers on an auxiliary positive syntax (`merge_valid`) is included as
labelled: it is not a translation of proofs and establishes nothing about
small codes. The notes' own audits stand: nested bounded histories cannot
reach the decoder, universe descent is equivalent to the barrier schema over
`HG` bases, and the proposed small-code machine still lacks its operations
and correctness proofs.

The relational small-code machine (con64), a focused prototype.
`RelMachine.lean`: formulas with positive existentials, conjunction and
biconditional; codes as a small syntax; a syntactic step relation and its
reflexive transitive closure; and a fuelled structural semantics whose
first component is the actual witness readback of an existential head and
whose second is realizability. The witness of a variable head is the
environment value pruned to the free variables of the existential, the
witness of the empty head is `∅`, and the witness of the Separation head is
the native `sep` at the realizability predicate of the matrix, read from
the formula. Head menus are subtypes of the code type, small; validity
asserts only their negative inhabitation. One joint induction on the fuel
gives fuel irrelevance and agreement up to bisimulation on the mentioned
variables. From it: readiness with actual payloads, existential elimination
into stable goals with no head selected, both introductions, and Separation:
the axiom code realizes every instance whose matrix does not mention the set
being separated, the forward clause returning every realizing code and the
backward clause consuming readiness only. Collection is composed from a
realizer of the premise: the collector is a native range over the literal
elements of the source, the generalization heads of the realizer, and the
existential heads of its instances, with the readback as payload, and it
satisfies both clauses and is a base for further Separation. No menu
function is supplied anywhere.

Two findings shape the file. First, the pruning of variable witnesses to
the free variables of the existential is what makes Separation sound: a code
realizing the matrix could otherwise read the slot of the set being
separated, and the backward clause would fail on `∃w (w ∈ z)` read at that
slot. Second, on this toolchain the equation lemmas of well-founded
recursion carry `Quot.sound` and overlapping constructor patterns carry
`propext`, so the semantics is fuelled and every shape test is an
exhaustive Boolean function. Not done: a code realizing the Collection
axiom formula, which needs a closure over the premise code and a renaming
lemma for inserting the collector's slot; validity of the logical
combinators; and adequacy for any translated proof. `Derived.lean` holds the
Hilbert-system toolkit (deduction theorem, generalization over lifted
hypotheses, existential rules) prepared for the Replacement-to-Collection
bridge, which is not yet derived.

Status of the machine after review (2026-09-26). Two counterexamples,
checked against the prototype with empty axiom reports and kept in
`RelMachineTests.lean`, show that its logical rules fail: with `x = {∅}`
and `a = {{∅}}` no code realizes `x ∈ a → ∃y (y ∈ a)`, because pruning
forbids the witness variable `x`, which is absent from the conclusion; and
the code realizing a conjunction through Separation's semantic pair entries
has a right projection that does not realize the right conjunct, because
projection follows only syntactic reduction. They describe the current
defects; a repair should invalidate them. Determinism of one-step
reduction, normality of heads, reduction expansion and the validity of the
two combinators were added as infrastructure; they do not bear on either
failure. The one repair the prover attempted ran into the following, all
scoped to this interpretation: without pruning a matrix realizer may read
the slot of the set being separated, so the backward clause of Separation
would need the separating predicate at an environment already containing
the set, and no fixed-point construction for that has been supplied; a
restriction on codes not to read that slot is not preserved by compilation,
since a derivation may use the eigenvariable of a Separation instance as a
witness inside its own matrix; and repairing the eliminators by a code
whose heads are those of every realizer of the same formula is a same-size
query whose fuel slack grows with nesting depth, so it breaks fuel
irrelevance. This does not establish a general limitation of the type
theory or an impossibility of interpreting IZF, and it does not rule out
explicit menu composition with scoped closures and traces; the comparison
with the CZF-strength Σ-interpretation is motivation only. The reviewer's
audit probes, incorporated in `ConZF/Audit`, add a checked context
interface with unrestricted introduction and joint renaming, and two
constraints on any certified design: an unrestricted raw collector meets a
one-step self-application whose total readback would contain itself, with
no fuel threshold stabilizing it, and arbitrary captured native witnesses
cannot be erased into one fixed small menu family preserving their values.
The productive question is which precisely stated restriction makes witness
reconstruction sound while still allowing the required Separation instances.
The Collection axiom closure is not attempted before that is answered.

The classical bridge from Replacement to ordinary Collection.
`Collection.lean`, entirely in the object calculus: the Collection schema
and the theory `ZFCollection`, the `ZF` axioms with Replacement replaced by
Collection. Every instance of the branch's Replacement schema, in its
partial functional form with values bounded by a set, is derivable in it.
The matrix is totalized with the source set as default output,
`ψ(x, y) ∨ (y = a ∧ ¬∃z ψ(x, z))`; the totalized relation is total by the
object calculus's double negation elimination, so no excluded middle of the
type theory is used; Collection supplies a set with a collected output for
each element of the source; and whenever an original output exists the
default branch is impossible, so functionality identifies the collected
output with the original one, which is the bounding form of Replacement.
The derivation runs in the hypothetical-derivation toolkit of
`Derived.lean`, with six renaming identities proved by composition and
pointwise congruence. Hence every theorem of `ZF` is a theorem of
`ZFCollection`, consistency of `ZFCollection` gives consistency of `ZF`,
and an accepted checker code is a proof of falsity from Collection. This is
classical syntactic preprocessing; it is not an intuitionistic translation
and proves no consistency. One toolchain fact from this file: the renaming
lemmas had been closed by `simp only`, which discharges an equality through
`propext`; they are now explicit congruence terms. The reviewer's
cumulative-fuel audit, `Audit/CumulativeFuel.lean`, is incorporated with its
stated assumptions: it checks a natural specialization of conzf26's
proposal, not every step-indexed semantics.

`NegCore.lean` is the restricted core the reviewer asked for after conzf27,
kept apart from the prototype. Witnesses are syntactic objects read back
structurally, with negative-matrix separation read as the native `sep` at
truth, so no code ever becomes an object. Codes carry a closure `letObj q c`
produced by both β-rules; reduction never pushes it, the head readers see
through it, and an application to a closure pulls its argument inside. The
realizability judgment `Realizes φ σ e c` is structural on the formula and
reads implication in the Kripke way over environment renamings, which is
what makes weakening, object substitution by closures, and the two
quantifier eliminators go through by induction on the formula. Checked:
determinism and renaming compatibility of reduction, invariance under
reduction, monotonicity, substitution, application preserving certification,
`I`/`K`/`S`, double negation introduction, projections through actual pair
heads, existential introduction at any object or variable, universal
elimination at a variable and at an object, code-producing existential
elimination, negative soundness with canonical completeness, and negative
Separation with a reconstructible witness, plus positive tests including an
existential conclusion whose witness variable is absent. On the negative
fragment, negative existence of a realizer is native truth, the same scoped
fact as the reviewer's audit of the prototype. No Collection constructor
and no source-adequacy claim.

After conzf29 two reviewer results are integrated, unchanged in substance.
`Witness.Certified` corrects con71's claim that negative existence over a
small witness carrier does not give menu families: under con71's own
Prop-subtype convention the certified witnesses at each request already form
an actual menu, ready from pointwise negative existence without selecting
anything, and with total readback, stable conclusions and an inclusion-antitone
condition predicate their decoded values consolidate into one native common
bound. `Audit/ObjectEnvelope.lean` then separates native bound construction
from descriptor reconstruction: at a fixed environment the union of all
`NegCore` descriptor values contains every descriptor value, so no descriptor
of the same grammar denotes it or even bounds all values by inclusion.
Returning a native bound as a descriptor therefore needs a larger grammar or
an environment parameter, with preservation theorems still to be proved. This
is a fixed-grammar, fixed-environment fact, not a general impossibility of
candidate forcing, and con72's example is likewise read narrowly: it defeats
one logger that returns observed universal-query arguments and checks no full
operational countermodel.

`DecoderLocal.lean` carries out newcon1's localization natively, without
touching `NegCore`. The isomorphism graph of the ordinal decoder lies in an
explicit powerset box over the ordinal and the double union of the diagram,
and the box has an existing object descriptor with an exact readback law, so
the decoder is a genuine bounded matrix once the box is supplied in an
environment slot by an explicit adapter. Bounds in that syntax are variable
slots, so the box is never written as a term, and the free-variable bound on
the literal decoder is kept distinct from a bounded-quantifier certificate.
Pure injections have the same kind of box, giving a bounded injection matrix
with the exact reading and a bounded no-barrier condition. The literal
totalized decoder normalizes to a conjunction whose only unbounded universal
is positive with a bounded antecedent, its Collection premise is negatively
provable, and the Collection instance used by the classical bridge reads
exactly as "some set contains the source and every decoded output". The
audit lemma equates absence of outputs within a candidate set implying
global absence with coverage of every output, which is the obligation a
bounded-search replacement must meet. Any source reduces to a barrier for
its triple union, and for diagram sources the collecting bound is exactly a
barrier. These are native equivalences, not forcing equivalences, and they
prove no source adequacy. `Audit/SepBounding.lean` checks the reviewer's
conjecture that a realizer of Separation by a positive existential with a
negative matrix already bounds the native witnesses in the current
semantics: the argument uses only the Kripke clause of the backward
implication, canonical completeness, and the descriptor readback of the
forward head; it produces no Separation realizer and refutes nothing.

Not formalized: the converse cardinal bridge, the internal reflection
sentence, the two-height assembly, and the finite scheme of distinct
inaccessibles.

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
