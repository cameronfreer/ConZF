import ConZF.Graph.Sat
/-!
The definable powerset of a graph set. `GSet.Def G` has the old vertices, one vertex for every
formula with a finite list of parameter vertices, and an outer root; the predecessors of a
definition vertex are the predecessors of the old root satisfying the formula over `G`, with the
parameters read as pointed graphs. Its members are exactly the definable subsets of `G`
(`mem_Def`): a finite name suffices for each new object, while its predicate may inspect all of
`G`. A transitive `G` is included in `Def G` (`subset_Def`), and `Def G` is transitive
(`trans_Def`).
-/
universe u

namespace GSet
open PSet.Fml

section
variable (G : GSet.{u})

/-- The environment of a parameter list, with `G` itself as the default. -/
def envOf : List G.A → Nat → GSet.{u}
  | [], _ => G
  | a :: _, 0 => G.at' a
  | _ :: ps, n+1 => envOf ps n

/-- Vertices: old vertices, definitions, and the outer root. -/
inductive DefV : Type u
  | old (a : G.A)
  | def' (φ : PSet.Fml) (ps : List G.A)
  | top

/-- Edges: old edges; the satisfying predecessors of the old root below a definition; every
definition below the top. -/
inductive DefRel : DefV G → DefV G → Prop
  | old {a b : G.A} : G.R a b → DefRel (.old a) (.old b)
  | sel {a : G.A} {φ : PSet.Fml} {ps : List G.A} : G.R a G.r →
      Sat (Mem · G) φ (Env.cons (G.at' a) (envOf G ps)) → DefRel (.old a) (.def' φ ps)
  | top (φ : PSet.Fml) (ps : List G.A) : DefRel (.def' φ ps) .top

theorem defRel_old {b : G.A} {x} (h : DefRel G x (.old b)) : ∃ a, G.R a b ∧ x = .old a := by
  cases h with
  | old h => exact ⟨_, h, rfl⟩

theorem defRel_def' {φ : PSet.Fml} {ps : List G.A} {x} (h : DefRel G x (.def' φ ps)) :
    ∃ a, G.R a G.r ∧ Sat (Mem · G) φ (Env.cons (G.at' a) (envOf G ps)) ∧ x = .old a := by
  cases h with
  | sel h hs => exact ⟨_, h, hs, rfl⟩

theorem defRel_top {x} (h : DefRel G x .top) : ∃ φ ps, x = .def' φ ps := by
  cases h with
  | top φ ps => exact ⟨φ, ps, rfl⟩

theorem swf_defRel : Graph.SWF (DefRel G) := by
  intro Q hs H
  have old : ∀ a : G.A, Q (.old a) := by
    refine G.swf (fun a => Q (.old a)) (fun _ => hs _) fun a ih => H _ fun x hx => ?_
    obtain ⟨a', ha', rfl⟩ := defRel_old G hx
    exact ih a' ha'
  have def' : ∀ φ ps, Q (.def' φ ps) := fun φ ps => H _ fun x hx => by
    obtain ⟨a, _, _, rfl⟩ := defRel_def' G hx; exact old a
  intro x
  cases x with
  | old a => exact old a
  | def' φ ps => exact def' φ ps
  | top => exact H _ fun x hx => by obtain ⟨φ, ps, rfl⟩ := defRel_top G hx; exact def' φ ps

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
theorem mem_Def_def' {φ : PSet.Fml} {ps : List G.A} {K : GSet.{u}} :
    Mem K ((Def G).at' (.def' φ ps)) ↔ Mem K G ∧ Sat (Mem · G) φ (Env.cons K (envOf G ps)) := by
  constructor
  · intro h
    refine ⟨nn_map (fun ⟨x, hx, e⟩ => ?_) h, Stable.of_nn h fun ⟨x, hx, e⟩ => ?_⟩
    · obtain ⟨a, _, hs, rfl⟩ := defRel_def' G hx
      exact Sat.resp φ (Env.cons_resp (e.trans (Def_old_equiv G a)).symm fun _ => Equiv.refl _) hs
    · obtain ⟨a, ha, _, rfl⟩ := defRel_def' G hx
      exact ⟨a, ha, e.trans (Def_old_equiv G a)⟩
  · rintro ⟨h, hs⟩
    refine nn_map (fun ⟨a, ha, e⟩ => ?_) h
    refine ⟨.old a, DefRel.sel ha (Sat.resp φ (Env.cons_resp e fun _ => Equiv.refl _) hs),
      e.trans (Def_old_equiv G a).symm⟩

/-- **The definable powerset law.** The members of `Def G` are exactly the subsets of `G` defined
by a formula with finitely many parameters from `G`. -/
theorem mem_Def {Y : GSet.{u}} :
    Mem Y (Def G) ↔ ¬¬∃ (φ : PSet.Fml) (ps : List G.A),
      ∀ K, Mem K Y ↔ Mem K G ∧ Sat (Mem · G) φ (Env.cons K (envOf G ps)) := by
  constructor
  · refine nn_map fun ⟨x, hx, e⟩ => ?_
    obtain ⟨φ, ps, rfl⟩ := defRel_top G hx
    exact ⟨φ, ps, fun K => (mem_congr_right e).trans (mem_Def_def' G)⟩
  · refine nn_map fun ⟨φ, ps, h⟩ => ?_
    exact ⟨.def' φ ps, DefRel.top φ ps, ext fun K => (h K).trans (mem_Def_def' G).symm⟩

/-- Every member of `Def G` is a subset of `G`. -/
theorem subset_of_mem_Def {Y : GSet.{u}} (h : Mem Y (Def G)) : Subset Y G := fun K hK =>
  Stable.of_nn (mem_Def G |>.1 h) fun ⟨_, _, hY⟩ => ((hY K).1 hK).1

/-- A transitive graph set is included in its definable powerset: `x = {z ∈ G | z ∈ x}`. -/
theorem subset_Def (hG : Trans G) : Subset G (Def G) := by
  intro K hK
  refine Stable.of_nn hK fun ⟨a, ha, e⟩ => ?_
  refine (mem_Def G).2 (nn_intro ⟨.mem 0 1, [a], fun K' => ?_⟩)
  show Mem K' K ↔ Mem K' G ∧ Mem K' (G.at' a)
  exact ⟨fun h => ⟨hG K hK K' h, Mem.congr_right e h⟩, fun h => Mem.congr_right e.symm h.2⟩

theorem trans_Def (hG : Trans G) : Trans (Def G) :=
  fun _ hY K hK => subset_Def G hG K (subset_of_mem_Def G hY K hK)

end

/-- info: 'GSet.mem_Def' does not depend on any axioms -/
#guard_msgs in #print axioms mem_Def
/-- info: 'GSet.subset_Def' does not depend on any axioms -/
#guard_msgs in #print axioms subset_Def

end GSet
