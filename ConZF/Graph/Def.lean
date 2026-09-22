import ConZF.Graph.Sat
/-!
The definable powerset of a graph set. `GSet.Def G` has the old vertices, one vertex for every
formula with a finite list of parameters and a bound on its free variables, and an outer root.
Parameters are vertices that are predecessors of the root, so they represent members of `G`; the
bound `Fml.Bound (ps.length + 1) φ` makes the environment's default irrelevant. The predecessors
of a definition vertex are the predecessors of the old root satisfying the formula over `G`. Its
members are exactly the subsets of `G` defined by a formula with bounded free-variable indices
and member parameters (`mem_Def`), and `Def` respects bisimulation (`Def_congr`): a parameter list transports along a
bisimulation finitely, one parameter at a time. A transitive `G` is included in `Def G`
(`subset_Def`), and `Def G` is transitive (`trans_Def`).
-/
universe u

namespace GSet
open PSet.Fml

section
variable (G : GSet.{u})

/-- Parameters: vertices representing members of `G`. -/
abbrev Param : Type u := {a : G.A // G.R a G.r}

/-- The environment of a parameter list, with `G` itself as the default. -/
def envOf : List (Param G) → Nat → GSet.{u}
  | [], _ => G
  | a :: _, 0 => G.at' a.1
  | _ :: ps, n+1 => envOf ps n

/-- A definition: a formula, member parameters, and a bound making the default unread. -/
structure Defn : Type u where
  φ : PSet.Fml
  ps : List (Param G)
  bound : Bound (ps.length + 1) φ

/-- Vertices: old vertices, definitions, and the outer root. -/
inductive DefV : Type u
  | old (a : G.A)
  | def' (d : Defn G)
  | top

/-- Edges: old edges; the satisfying predecessors of the old root below a definition; every
definition below the top. -/
inductive DefRel : DefV G → DefV G → Prop
  | old {a b : G.A} : G.R a b → DefRel (.old a) (.old b)
  | sel {a : G.A} {d : Defn G} : G.R a G.r →
      Sat (Mem · G) d.φ (Env.cons (G.at' a) (envOf G d.ps)) → DefRel (.old a) (.def' d)
  | top (d : Defn G) : DefRel (.def' d) .top

theorem defRel_old {b : G.A} {x} (h : DefRel G x (.old b)) : ∃ a, G.R a b ∧ x = .old a := by
  cases h with
  | old h => exact ⟨_, h, rfl⟩

theorem defRel_def' {d : Defn G} {x} (h : DefRel G x (.def' d)) :
    ∃ a, G.R a G.r ∧ Sat (Mem · G) d.φ (Env.cons (G.at' a) (envOf G d.ps)) ∧ x = .old a := by
  cases h with
  | sel h hs => exact ⟨_, h, hs, rfl⟩

theorem defRel_top {x} (h : DefRel G x .top) : ∃ d, x = .def' d := by
  cases h with
  | top d => exact ⟨d, rfl⟩

theorem swf_defRel : Graph.SWF (DefRel G) := by
  intro Q hs H
  have old : ∀ a : G.A, Q (.old a) := by
    refine G.swf (fun a => Q (.old a)) (fun _ => hs _) fun a ih => H _ fun x hx => ?_
    obtain ⟨a', ha', rfl⟩ := defRel_old G hx
    exact ih a' ha'
  have def' : ∀ d, Q (.def' d) := fun d => H _ fun x hx => by
    obtain ⟨a, _, _, rfl⟩ := defRel_def' G hx; exact old a
  intro x
  cases x with
  | old a => exact old a
  | def' d => exact def' d
  | top => exact H _ fun x hx => by obtain ⟨d, rfl⟩ := defRel_top G hx; exact def' d

/-- The definable powerset. -/
def Def : GSet.{u} := ⟨DefV G, DefRel G, .top, swf_defRel G⟩

theorem Def_old_equiv (a : G.A) : Equiv ((Def G).at' (.old a)) (G.at' a) := by
  refine nn_intro ⟨fun x b => ¬¬(x = .old b), ⟨fun _ _ => inferInstance, ?_, ?_⟩, nn_intro rfl⟩
  · intro x b hx x' hx'
    refine Stable.of_nn hx fun e => ?_
    subst e
    obtain ⟨a', ha', rfl⟩ := defRel_old G hx'
    exact nn_intro ⟨a', ha', nn_intro rfl⟩
  · intro x b hx b' hb'
    refine Stable.of_nn hx fun e => ?_
    subst e
    exact nn_intro ⟨.old b', DefRel.old hb', nn_intro rfl⟩

/-- The members of a definition vertex. -/
theorem mem_Def_def' {d : Defn G} {K : GSet.{u}} :
    Mem K ((Def G).at' (.def' d)) ↔ Mem K G ∧ Sat (Mem · G) d.φ (Env.cons K (envOf G d.ps)) := by
  constructor
  · intro h
    refine ⟨nn_map (fun ⟨x, hx, e⟩ => ?_) h, Stable.of_nn h fun ⟨x, hx, e⟩ => ?_⟩
    · obtain ⟨a, _, hs, rfl⟩ := defRel_def' G hx
      exact Sat.resp d.φ (Env.cons_resp (e.trans (Def_old_equiv G a)).symm fun _ => Equiv.refl _) hs
    · obtain ⟨a, ha, _, rfl⟩ := defRel_def' G hx
      exact ⟨a, ha, e.trans (Def_old_equiv G a)⟩
  · rintro ⟨h, hs⟩
    refine nn_map (fun ⟨a, ha, e⟩ => ?_) h
    exact ⟨.old a, DefRel.sel ha (Sat.resp d.φ (Env.cons_resp e fun _ => Equiv.refl _) hs),
      e.trans (Def_old_equiv G a).symm⟩

/-- **The definable powerset law.** The members of `Def G` are exactly the subsets of `G` defined
by a formula with bounded free-variable indices and finitely many member parameters. -/
theorem mem_Def {Y : GSet.{u}} :
    Mem Y (Def G) ↔ ¬¬∃ d : Defn G,
      ∀ K, Mem K Y ↔ Mem K G ∧ Sat (Mem · G) d.φ (Env.cons K (envOf G d.ps)) := by
  constructor
  · refine nn_map fun ⟨x, hx, e⟩ => ?_
    obtain ⟨d, rfl⟩ := defRel_top G hx
    exact ⟨d, fun K => (mem_congr_right e).trans (mem_Def_def' G)⟩
  · refine nn_map fun ⟨d, h⟩ => ?_
    exact ⟨.def' d, DefRel.top d, ext fun K => (h K).trans (mem_Def_def' G).symm⟩

/-- Every member of `Def G` is a subset of `G`. -/
theorem subset_of_mem_Def {Y : GSet.{u}} (h : Mem Y (Def G)) : Subset Y G := fun K hK =>
  Stable.of_nn (mem_Def G |>.1 h) fun ⟨_, hY⟩ => ((hY K).1 hK).1

/-- A transitive graph set is included in its definable powerset: `x = {z ∈ G | z ∈ x}`. -/
theorem subset_Def (hG : Trans G) : Subset G (Def G) := by
  intro K hK
  refine Stable.of_nn hK fun ⟨a, ha, e⟩ => ?_
  refine (mem_Def G).2 (nn_intro ⟨⟨.mem 0 1, [⟨a, ha⟩], ⟨Nat.zero_lt_succ _, Nat.lt_succ_self _⟩⟩, fun K' => ?_⟩)
  show Mem K' K ↔ Mem K' G ∧ Mem K' (G.at' a)
  exact ⟨fun h => ⟨hG K hK K' h, Mem.congr_right e h⟩, fun h => Mem.congr_right e.symm h.2⟩

theorem trans_Def (hG : Trans G) : Trans (Def G) :=
  fun _ hY K hK => subset_Def G hG K (subset_of_mem_Def G hY K hK)

end

/-! ### Presentation invariance -/

/-- A parameter list transports along a bisimulation, one parameter at a time. -/
theorem envOf_transport {G G' : GSet.{u}} {Z} (hZ : IsBisim G G' Z) (hr : Z G.r G'.r) :
    ∀ ps : List (Param G), ¬¬∃ ps' : List (Param G'),
      ps.length = ps'.length ∧ ∀ i, Equiv (envOf G ps i) (envOf G' ps' i)
  | [] => nn_intro ⟨[], rfl, fun _ => nn_intro ⟨Z, hZ, hr⟩⟩
  | a :: ps => by
    refine nn_bind (envOf_transport hZ hr ps) fun ⟨ps', hl, he⟩ => ?_
    refine nn_map (fun ⟨b, hb, hab⟩ => ⟨⟨b, hb⟩ :: ps', congrArg Nat.succ hl, fun i => ?_⟩)
      (hZ.forth G.r G'.r hr a.1 a.2)
    cases i with
    | zero => exact hZ.at' hab
    | succ i => exact he i

/-- `Def` respects bisimulation. -/
theorem mem_Def_of_equiv {G G' Y : GSet.{u}} (e : Equiv G G') (h : Mem Y (Def G)) :
    Mem Y (Def G') := by
  refine Stable.of_nn e fun ⟨Z, hZ, hr⟩ => ?_
  refine Stable.of_nn ((mem_Def G).1 h) fun ⟨d, hd⟩ => ?_
  refine Stable.of_nn (envOf_transport hZ hr d.ps) fun ⟨ps', hl, he⟩ => ?_
  refine (mem_Def G').2 (nn_intro ⟨⟨d.φ, ps', hl ▸ d.bound⟩, fun K => (hd K).trans ?_⟩)
  refine and_congr (mem_congr_right (nn_intro ⟨Z, hZ, hr⟩)) ?_
  exact Sat.resp_iff (fun _ => mem_congr_right (nn_intro ⟨Z, hZ, hr⟩)) d.φ
    (Env.cons_resp (Equiv.refl K) he)

theorem Def_congr {G G' : GSet.{u}} (e : Equiv G G') : Equiv (Def G) (Def G') :=
  ext fun _ => ⟨mem_Def_of_equiv e, mem_Def_of_equiv e.symm⟩

/-- info: 'GSet.mem_Def' does not depend on any axioms -/
#guard_msgs in #print axioms mem_Def
/-- info: 'GSet.Def_congr' does not depend on any axioms -/
#guard_msgs in #print axioms Def_congr
/-- info: 'GSet.subset_Def' does not depend on any axioms -/
#guard_msgs in #print axioms subset_Def

end GSet
