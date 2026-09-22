import ConZF.Acc
/-!
An obstruction, with its scope. The rule trees `Tr (rule ISat) η` are unpruned: `Rel` requires a
child to have a target but not that its label be available, and the identity relation on `η` is
unbounded at `η` (`.b` labels need no lower `D`-stage). So every membership descent below a
hereditarily good ordinal is an edge of its tree, and accessibility of the root of the tree is
equivalent to `Acc (· ∈ ·) η` (`canonical_acc_iff_mem_acc`). Restricting attention to these
trees, as defined, therefore does not weaken pointwise ordinal accessibility. Nothing is said
about trees with fewer edges, and no impossibility is claimed.
-/
universe u
namespace PSet

private def identityCode : PSet.{u} :=
  code (.eq 0 1) 0 (fun _ => empty)

private theorem identityBound : Fml.Bound (0+2) (.eq 0 1) :=
  ⟨by decide, by decide⟩

private theorem ordinal_mem_Vl {η x : PSet.{u}} (hη : IsOrd η) (hx : x ∈ η) :
    x ∈ Vl η :=
  (mem_Vl_ord hη).2 ((mem_congr_left (hη.mem hx).rank_equiv).2 hx)

/-- The identity on eta is cofinal in eta. It need not be available from a lower D-stage. -/
private theorem identity_unb {η : PSet.{u}} (hη : IsOrd η) :
    Unb ISat η identityCode η := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y y' _ h h'
    have h1 := (isat_code identityBound).1 h
    have h2 := (isat_code identityBound).1 h'
    exact h1.2.2.symm.trans h2.2.2
  · intro x y _ h
    exact (mem_Vl_ord hη).1 ((isat_code identityBound).1 h).2.1
  · intro ζ hζ
    refine nn_intro ⟨ζ, ζ, hζ, ?_, ?_⟩
    · exact (isat_code identityBound).2
        ⟨ordinal_mem_Vl hη hζ, ordinal_mem_Vl hη hζ, Equiv.refl _⟩
    · exact mem_succ_of_equiv (hη.mem hζ).rank_equiv.symm

private theorem rule_contains_mem {η ξ : PSet.{u}} (hη : IsOrd η) (hξ : ξ ∈ η) :
    rule ISat η (.b (triple identityCode η ξ)) ξ := by
  refine nn_intro ⟨identityCode, η, ξ, ξ, Equiv.refl _, identity_unb hη, hξ, ?_, ?_⟩
  · exact (isat_code identityBound).2
      ⟨ordinal_mem_Vl hη hξ, ordinal_mem_Vl hη hξ, Equiv.refl _⟩
  · exact (hη.mem hξ).rank_equiv.symm

private theorem mem_acc_of_canonical_acc {η : PSet.{u}} {p : Path.{u}}
    (ha : Acc (Rel (Tr (rule ISat) η)) p) :
    ∀ t, IsOrd t → Tr (rule ISat) η p t → Acc (· ∈ ·) t := by
  induction ha with
  | intro p _ ih =>
    intro t ht hpath
    refine Acc.intro t fun ξ hξ => ?_
    let l : Label.{u} := .b (triple identityCode t ξ)
    have hchild : Tr (rule ISat) η (l :: p) ξ :=
      .cons hpath (rule_contains_mem ht hξ)
    exact ih (l :: p) ⟨l, rfl, ξ, hchild⟩ ξ (ht.mem hξ) hchild

/-- Restricting to these canonical trees does not weaken pointwise ordinal accessibility. -/
theorem canonical_acc_iff_mem_acc {η : PSet.{u}} (hη : Cls ISat η) :
    Acc (Rel (Tr (rule ISat) η)) [] ↔ Acc (· ∈ ·) η := by
  constructor
  · intro ha
    exact mem_acc_of_canonical_acc ha η hη.1 (.nil (Equiv.refl _))
  · intro ha
    have hc := (reach_rule ISat_resp empty).coherent (η := η) hη
    exact acc_of_desc hc.1.desc ha [] hc.2

/-- info: 'PSet.canonical_acc_iff_mem_acc' does not depend on any axioms -/
#guard_msgs in #print axioms canonical_acc_iff_mem_acc
end PSet
