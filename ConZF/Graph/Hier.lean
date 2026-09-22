import ConZF.Graph.Names
/-!
Semantics of the hierarchy. The earlier-stage graph of the solved table at `b` and the hierarchy
graph agree on the part below the level `b`: the name vertices are equivalent, and the root of
the earlier-stage graph is equivalent to `L α b` (`stageGraph_equiv_hier`). Hence the members of
`L α b` are, negatively, the values of the valid names born below `b` (`mem_L`), and the value of
a valid name `def' b φ n args` is the subset of `L α b` defined by `φ` with the values of its
arguments (`nameVal_spec`). Together with `mem_Def` these give the exact recurrence
`L α a ≈ ⋃_{b below a} Def (L α b)` in membership form (`mem_L_iff_Def`).
-/
universe u

namespace GSet
open PSet.Fml

section
variable (α : GSet.{u})

/-- The earlier-stage graph of the solved table at `b`, and the hierarchy graph, agree below the
level `b`: the bisimulation relates a name born below `b` to its copy, and the root to `inr b`. -/
theorem stageGraph_equiv_hier (b : α.A) :
    (∀ c : Name α.A, Stage α c.birth b →
      Equiv ((stageGraph α (table α) b).at' (some c)) (nameVal α c)) ∧
    Equiv (stageGraph α (table α) b) (L α b) := by
  let Z : Option (Name α.A) → Name α.A ⊕ α.A → Prop := fun x y =>
    ¬¬((∃ c, Stage α c.birth b ∧ x = some c ∧ y = .inl c) ∨ (x = none ∧ y = .inr b))
  have hZ : IsBisim (stageGraph α (table α) b) (hier α) Z := by
    refine ⟨fun _ _ => inferInstance, ?_, ?_⟩
    · intro x y hxy x' hx'
      refine Stable.of_nn hxy fun h => ?_
      rcases h with ⟨c, hcb, rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨c', hc', hc, hcd, _, ht, rfl⟩ := stageRel_some α (table α) b hx'
        exact nn_intro ⟨Sum.inl c', .name hc' hc hcd ht, nn_intro (.inl ⟨c', hcd.trans hcb, rfl, rfl⟩)⟩
      · obtain ⟨c, hc, hcb, rfl⟩ := stageRel_none α (table α) b hx'
        exact nn_intro ⟨Sum.inl c, .lev hc hcb, nn_intro (.inl ⟨c, hcb, rfl, rfl⟩)⟩
    · intro x y hxy y' hy'
      refine Stable.of_nn hxy fun h => ?_
      rcases h with ⟨c, hcb, rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨c', hc', hc, hcd, ht, rfl⟩ := hierRel_inl α hy'
        exact nn_intro ⟨some c', .name hc' hc hcd hcb ht, nn_intro (.inl ⟨c', hcd.trans hcb, rfl, rfl⟩)⟩
      · obtain ⟨c, hc, hcb, rfl⟩ := hierRel_inr α hy'
        exact nn_intro ⟨some c, .root hc hcb, nn_intro (.inl ⟨c, hcb, rfl, rfl⟩)⟩
  exact ⟨fun c hcb => hZ.at' (nn_intro (.inl ⟨c, hcb, rfl, rfl⟩)), hZ.at' (nn_intro (.inr ⟨rfl, rfl⟩))⟩

/-- The members of a level: the values of the valid names born below it, negatively. -/
theorem mem_L {b : α.A} {K : GSet.{u}} :
    Mem K (L α b) ↔ ¬¬∃ c : Name α.A, Valid α c ∧ Stage α c.birth b ∧ Equiv K (nameVal α c) := by
  constructor
  · refine nn_map fun ⟨x, hx, e⟩ => ?_
    obtain ⟨c, hc, hcb, rfl⟩ := hierRel_inr α hx
    exact ⟨c, hc, hcb, e⟩
  · refine nn_map fun ⟨c, hc, hcb, e⟩ => ⟨Sum.inl c, .lev hc hcb, e⟩

/-- The members of the value of a name: the names it contains by the solved table. -/
theorem mem_nameVal {d : Name α.A} {K : GSet.{u}} :
    Mem K (nameVal α d) ↔
      ¬¬∃ c : Name α.A, Valid α c ∧ Valid α d ∧ Stage α c.birth d.birth ∧ ¬¬table α d c ∧
        Equiv K (nameVal α c) := by
  constructor
  · refine nn_map fun ⟨x, hx, e⟩ => ?_
    obtain ⟨c, hc, hd, hcd, ht, rfl⟩ := hierRel_inl α hx
    exact ⟨c, hc, hd, hcd, ht, e⟩
  · refine nn_map fun ⟨c, hc, hd, hcd, ht, e⟩ => ⟨Sum.inl c, .name hc hd hcd ht, e⟩

/-- The environment of a name's arguments, read as values in the hierarchy, with the level at
its birth as the default. -/
def valEnv (t : Name α.A) : Nat → GSet.{u} := fun i =>
  if h : i < t.arity then nameVal α (t.args ⟨i, h⟩) else L α t.birth

theorem valEnv_equiv_argEnv {t : Name α.A} (hv : Valid α t) :
    ∀ i, Equiv (argEnv α (stageGraph α (table α) t.birth) some t i) (valEnv α t i) := by
  intro i
  unfold argEnv valEnv
  split
  · rename_i h
    refine (stageGraph_equiv_hier α t.birth).1 _ ?_
    cases t with
    | def' a φ n args => exact (hv.2 ⟨i, h⟩).2
  · exact (stageGraph_equiv_hier α t.birth).2

/-- **The value of a name.** A valid name `def' b φ n args` denotes the subset of `L α b` defined
by `φ` with the values of its arguments. -/
theorem nameVal_spec {d : Name α.A} (hd : Valid α d) (K : GSet.{u}) :
    Mem K (nameVal α d) ↔
      Mem K (L α d.birth) ∧ Sat (Mem · (L α d.birth)) d.fml (Env.cons K (valEnv α d)) := by
  have hM := stageGraph_equiv_hier α d.birth
  constructor
  · intro h
    refine ⟨(mem_L α).2 (nn_map (fun ⟨c, hc, _, hcd, _, e⟩ => ⟨c, hc, hcd, e⟩) ((mem_nameVal α).1 h)),
      ?_⟩
    refine Stable.of_nn ((mem_nameVal α).1 h) fun ⟨c, hc, _, hcd, ht, e⟩ => ?_
    refine Stable.of_nn ht fun ht => ?_
    have hs := ((table_eq α d c).1 ht).2.2.2
    refine (Sat.resp_iff (fun _ => mem_congr_right hM.2) d.fml ?_).1 hs
    intro i
    cases i with
    | zero => exact (hM.1 c hcd).trans e.symm
    | succ i => exact valEnv_equiv_argEnv α hd i
  · rintro ⟨h, hs⟩
    refine Stable.of_nn ((mem_L α).1 h) fun ⟨c, hc, hcd, e⟩ => ?_
    refine (mem_nameVal α).2 (nn_intro ⟨c, hc, hd, hcd, nn_intro ((table_eq α d c).2 ⟨hd, hc, hcd, ?_⟩), e⟩)
    refine (Sat.resp_iff (fun _ => mem_congr_right hM.2) d.fml ?_).2 hs
    intro i
    cases i with
    | zero => exact (hM.1 c hcd).trans e.symm
    | succ i => exact valEnv_equiv_argEnv α hd i

/-! ### The recurrence -/

theorem envOf_get {G : GSet.{u}} : ∀ (ps : List (Param G)) (i : Nat) (h : i < ps.length),
    envOf G ps i = G.at' (ps.get ⟨i, h⟩).1
  | _ :: _, 0, _ => rfl
  | _ :: ps, i+1, h => envOf_get ps i (Nat.lt_of_succ_lt_succ h)

theorem envOf_default {G : GSet.{u}} : ∀ (ps : List (Param G)) (i : Nat), ps.length ≤ i →
    envOf G ps i = G
  | [], _, _ => rfl
  | _ :: _, 0, h => (Nat.not_succ_le_zero _ h).elim
  | _ :: ps, i+1, h => envOf_default ps i (Nat.le_of_succ_le_succ h)

/-- A list of parameters from a finite family. -/
def paramList {G : GSet.{u}} : (n : Nat) → (Fin n → Param G) → List (Param G)
  | 0, _ => []
  | n+1, f => f ⟨0, Nat.zero_lt_succ n⟩ :: paramList n fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

theorem paramList_length {G : GSet.{u}} : ∀ (n : Nat) (f : Fin n → Param G), (paramList n f).length = n
  | 0, _ => rfl
  | n+1, f => congrArg Nat.succ (paramList_length n fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

theorem envOf_paramList {G : GSet.{u}} : ∀ (n : Nat) (f : Fin n → Param G) (i : Nat) (h : i < n),
    envOf G (paramList n f) i = G.at' (f ⟨i, h⟩).1
  | _+1, _, 0, _ => rfl
  | n+1, f, i+1, h =>
    envOf_paramList n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) i (Nat.lt_of_succ_lt_succ h)

/-- A parameter of a level is a name born below it. -/
theorem param_L {b : α.A} (p : Param (L α b)) :
    ∃ c : Name α.A, Valid α c ∧ Stage α c.birth b ∧ p.1 = .inl c := by
  obtain ⟨c, hc, hcb, e⟩ := hierRel_inr α p.2
  exact ⟨c, hc, hcb, e⟩

/-- The name of a parameter of a level. -/
def paramName {b : α.A} (p : Param (L α b)) : Name α.A :=
  match p with
  | ⟨.inl c, _⟩ => c
  | ⟨.inr _, h⟩ => nomatch h

theorem paramName_spec {b : α.A} (p : Param (L α b)) : p.1 = .inl (paramName α p) :=
  match p with
  | ⟨.inl _, _⟩ => rfl
  | ⟨.inr _, h⟩ => nomatch h

theorem Valid.bound {t : Name α.A} (h : Valid α t) : Bound (t.arity + 1) t.fml := by
  cases t with | def' a φ n args => exact h.1

theorem Valid.arg_valid {t : Name α.A} (h : Valid α t) (i : Fin t.arity) : Valid α (t.args i) := by
  cases t with | def' a φ n args => exact (h.2 i).1

theorem Valid.arg_stage {t : Name α.A} (h : Valid α t) (i : Fin t.arity) :
    Stage α (t.args i).birth t.birth := by
  cases t with | def' a φ n args => exact (h.2 i).2

/-- **The recurrence, membership form.** The members of `L α a` are, negatively, the members of
`Def (L α b)` for stages `b` below `a`. -/
theorem mem_L_iff_Def {a : α.A} {K : GSet.{u}} :
    Mem K (L α a) ↔ ¬¬∃ b, Stage α b a ∧ Mem K (Def (L α b)) := by
  constructor
  · intro h
    refine nn_map (fun ⟨c, hc, hca, e⟩ => ⟨c.birth, hca, ?_⟩) ((mem_L α).1 h)
    let f : Fin c.arity → Param (L α c.birth) := fun i =>
      ⟨Sum.inl (c.args i), .lev (Valid.arg_valid α hc i) (Valid.arg_stage α hc i)⟩
    have hl := paramList_length c.arity f
    refine (mem_Def (L α c.birth)).2 (nn_intro ⟨⟨c.fml, paramList c.arity f, by rw [hl]; exact Valid.bound α hc⟩,
      fun K' => ?_⟩)
    refine (mem_congr_right e).trans ((nameVal_spec α hc K').trans (and_congr Iff.rfl ?_))
    refine Sat.resp_iff (fun _ => Iff.rfl) c.fml fun i => ?_
    cases i with
    | zero => exact Equiv.refl _
    | succ i =>
      show Equiv (valEnv α c i) (envOf (L α c.birth) (paramList c.arity f) i)
      unfold valEnv
      split
      · rename_i h
        rw [envOf_paramList c.arity f i h]
        exact Equiv.refl _
      · rename_i h
        have hl' : (paramList c.arity f).length ≤ i := by rw [hl]; exact Nat.le_of_not_lt h
        rw [envOf_default _ i hl']
        exact Equiv.refl _
  · intro h
    refine (mem_L α).2 ?_
    refine nn_bind h fun ⟨b, hba, hK⟩ => ?_
    refine nn_map ?_ ((mem_Def (L α b)).1 hK)
    rintro ⟨d, hd⟩
    let c : Name α.A := .def' b d.φ d.ps.length fun i => paramName α (d.ps.get i)
    have hc : Valid α c := ⟨d.bound, fun i => by
      obtain ⟨c', hc', hcb, e⟩ := param_L α (d.ps.get i)
      have : paramName α (d.ps.get i) = c' := Sum.inl.inj ((paramName_spec α _).symm.trans e)
      show Valid α (paramName α (d.ps.get i)) ∧ Stage α (paramName α (d.ps.get i)).birth b
      rw [this]
      exact ⟨hc', hcb⟩⟩
    refine ⟨c, hc, hba, ext fun K' => (hd K').trans (Iff.trans ?_ (nameVal_spec α hc K').symm)⟩
    refine and_congr Iff.rfl (Sat.resp_iff (fun _ => Iff.rfl) d.φ fun i => ?_)
    cases i with
    | zero => exact Equiv.refl _
    | succ i =>
      show Equiv (envOf (L α b) d.ps i) (valEnv α c i)
      unfold valEnv
      split
      · rename_i h
        rw [envOf_get d.ps i h, paramName_spec α (d.ps.get ⟨i, h⟩)]
        exact Equiv.refl _
      · rename_i h
        rw [envOf_default d.ps i (Nat.le_of_not_lt h)]
        exact Equiv.refl _

end

/-- info: 'GSet.nameVal_spec' does not depend on any axioms -/
#guard_msgs in #print axioms nameVal_spec
/-- info: 'GSet.mem_L_iff_Def' does not depend on any axioms -/
#guard_msgs in #print axioms mem_L_iff_Def

end GSet
