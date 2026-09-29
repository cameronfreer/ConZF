import ConZF.GraphConsumer

/-!
Source formulas for the Axiom H tranche (conzf30). Definitions and scope checks only. Every source
existential is `PSet.Fml.ex`, negative under `GSet.Sat`; `cA`, `cB`, `totalize` and the ordinal
decoder are unchanged.

* `hRelF`, `hOrdinaryF`: the relational and the ordinary form of Axiom H, free parameter `U`:
  `∃H (Trans H ∧ ∀T ∀r (Trans T ∧ r : T ↪ U → T ⊆ H))`. The ordinary form adds forward
  functionality of `r`. The conclusion is inclusion `T ⊆ H`, not membership.
* `tCoF`: a transitive set containing the supplied set as an element.
* `supportF` at `[U, y, …]`: the **weak, root-free** support convention, `y ⊆ T` for some transitive
  `T` with a relational injection into `U`. It is not the usual hereditary-cardinality class: at
  `U = ∅` it admits `y = ∅`.
* `guarded θ := supportF ∧ θ` at `[x, y, params…]`: the guard reads "the output `y` has weak
  transitive support bounded by the input `x`". `guardedCollection θ` is the literal
  `coll (totalize (guarded θ))`. The matrix `θ` is arbitrary, but this is **not** unrestricted
  Collection: the guard supplies the bound.
* `transBody`, `transDecodeF`: the decoder body with ordinalhood replaced by transitivity and every
  other clause kept.
-/
namespace GSet.HRel.Syntax
open PSet.OrdDecode

/-- Membership-bounded subset: all x in i, x in j. -/
def sub (i j : Nat) : BForm := .allIn i (.mem 0 (j + 1))

/-- Inverse uniqueness. Under the three binders: [v, t', t, ...]. -/
def inverseUnique (r T U : Nat) : BForm :=
  .allIn T (.allIn (T + 1) (.allIn (U + 2)
    (.imp (B.edge (r + 3) 2 0)
      (.imp (B.edge (r + 3) 1 0) (.eq 2 1)))))

/-- Pure, negatively total, inverse-unique relation; no forward-functionality. -/
def rInj (r T U : Nat) : BForm :=
  .conj (B.typed r T U)
    (.conj (B.total r T U) (inverseUnique r T U))

/-- Ordinary pure injection, for the comparison with standard Axiom H. -/
def ordinaryInj (r T U : Nat) : BForm :=
  .conj (rInj r T U) (B.functional r T U)

/-- Free parameter [U,...]. After all binders: [r,T,H,U,...]. -/
def hRelF : PSet.Fml :=
  PSet.Fml.ex (PSet.Fml.and (B.trans 0).compile
    (.all (.all (.imp
      (PSet.Fml.and (B.trans 1).compile (rInj 0 1 3).compile)
      (sub 1 2).compile))))

/-- Standard injection version of Axiom H, free parameter [U,...]. -/
def hOrdinaryF : PSet.Fml :=
  PSet.Fml.ex (PSet.Fml.and (B.trans 0).compile
    (.all (.all (.imp
      (PSet.Fml.and (B.trans 1).compile (ordinaryInj 0 1 3).compile)
      (sub 1 2).compile))))

/-- A transitive set containing the supplied set as an element.
Equivalent over Pairing to the usual transitive-containment statement. -/
def tCoF : PSet.Fml :=
  PSet.Fml.ex (PSet.Fml.and (B.trans 0).compile (.mem 1 0))

/-- Free variables [U,y,...]; after ex T, ex r: [r,T,U,y,...]. -/
def supportMatrix : BForm :=
  .conj (B.trans 1) (.conj (sub 3 1) (rInj 0 1 2))

def supportF : PSet.Fml :=
  PSet.Fml.ex (PSet.Fml.ex supportMatrix.compile)

/-- Bound slots [U,y,A,B,...], with A = powerset C and B = powerset (C x U).
The second bound is slot 4 AFTER introducing T; BForm bounds are pre-binder slots. -/
def boxedSupport : BForm :=
  .exIn 2 (.exIn 4 supportMatrix)

/-- The matrix has the original conventions [x,y,params...]. -/
def guarded (theta : PSet.Fml) : PSet.Fml := PSet.Fml.and supportF theta

/-- The literal source instances, without changing cA/cB or the default a. -/
def guardedCollection (theta : PSet.Fml) : PSet.Fml :=
  PSet.ZFAx.coll (PSet.ZFAx.totalize (guarded theta))

def guardedReplacement (theta : PSet.Fml) : PSet.Fml :=
  PSet.ZFAx.repl (guarded theta)

/-- Same environment convention as the original decoder body: [f,d,T,...].
Only the ordinal conjunct is replaced by transitivity. -/
def transBody : BForm :=
  .exIn 1 (.exIn 0 (.exIn 3 (.exIn 0
    (.conj (B.pair 5 2 0)
      (.conj (B.trans 6)
        (.conj (B.map 4 6 2)
          (.conj (B.onto 4 6 2)
            (.conj (B.relationPure 0 2) (B.order 4 0 6 2)))))))))

def transDecodeF : PSet.Fml := PSet.Fml.ex transBody.compile


/-- Universal closures for documentation; GValid of the open forms is used first. -/
def hRelClosed : PSet.Fml := .all hRelF
def hOrdinaryClosed : PSet.Fml := .all hOrdinaryF
def tCoClosed : PSet.Fml := .all tCoF

set_option maxRecDepth 200000 in
theorem supportMatrix_scoped : BForm.Scoped 4 supportMatrix := by decide
set_option maxRecDepth 200000 in
theorem boxedSupport_scoped : BForm.Scoped 4 boxedSupport := by decide
set_option maxRecDepth 200000 in
theorem transBody_scoped : BForm.Scoped 3 transBody := by decide

theorem supportF_bound : PSet.Fml.Bound 2 supportF :=
  ((BForm.compile_bound supportMatrix_scoped).ex).ex

theorem transDecodeF_bound : PSet.Fml.Bound 2 transDecodeF :=
  (BForm.compile_bound transBody_scoped).ex

/-- info: 'GSet.HRel.Syntax.supportF_bound' does not depend on any axioms -/
#guard_msgs in #print axioms supportF_bound
/-- info: 'GSet.HRel.Syntax.transDecodeF_bound' does not depend on any axioms -/
#guard_msgs in #print axioms transDecodeF_bound

end GSet.HRel.Syntax
