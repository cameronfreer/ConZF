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

The principal results have guarded empty `#print axioms` checks. Verification:
`lake build`, `lake env leanchecker --fresh --verbose ConZF`, and `git diff --check`.
