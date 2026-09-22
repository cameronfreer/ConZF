import ConZF.Graph.Recursion
/-!
Graph sets. A graph set is a small type of vertices with an edge relation, a root, and a proof
of well-founded induction for stable predicates (`SWF`), an ordinary record in `Type (u+1)`.
The proof is used only in proofs: it is never eliminated into `Type`. Equality is negative
bisimulation (`GSet.Equiv`), membership is negative existence of a bisimilar predecessor of the
root (`GSet.Mem`), both stable. Bisimulations do not mention roots, so a bisimulation between
two graphs relates all their pointed versions at once. This file proves the equivalence laws,
extensionality, and stable membership induction (`GSet.mem_induction`).
-/
universe u

/-- A graph set: vertices, edges, a root, and stable well-founded induction. -/
structure GSet : Type (u+1) where
  A : Type u
  R : A → A → Prop
  r : A
  swf : Graph.SWF R

namespace GSet

/-- The same graph pointed at another vertex. -/
def at' (G : GSet.{u}) (a : G.A) : GSet.{u} := ⟨G.A, G.R, a, G.swf⟩

theorem at'_r (G : GSet.{u}) : G.at' G.r = G := rfl

/-- A stable negative bisimulation between the vertex types of two graphs. -/
structure IsBisim (G H : GSet.{u}) (Z : G.A → H.A → Prop) : Prop where
  stable : ∀ a b, Stable (Z a b)
  forth : ∀ a b, Z a b → ∀ a', G.R a' a → ¬¬∃ b', H.R b' b ∧ Z a' b'
  back : ∀ a b, Z a b → ∀ b', H.R b' b → ¬¬∃ a', G.R a' a ∧ Z a' b'

/-- Equality: negative existence of a bisimulation relating the roots. -/
def Equiv (G H : GSet.{u}) : Prop := ¬¬∃ Z, IsBisim G H Z ∧ Z G.r H.r

/-- Membership: negative existence of a bisimilar predecessor of the root. -/
def Mem (K G : GSet.{u}) : Prop := ¬¬∃ a, G.R a G.r ∧ Equiv K (G.at' a)

instance {G H : GSet.{u}} : Stable (Equiv G H) := inferInstanceAs (Stable (¬_))
instance {K G : GSet.{u}} : Stable (Mem K G) := inferInstanceAs (Stable (¬_))

/-! ### Equivalence laws -/

theorem IsBisim.at' {G H : GSet.{u}} {Z} (h : IsBisim G H Z) {a b} (hab : Z a b) :
    Equiv (G.at' a) (H.at' b) := nn_intro ⟨Z, ⟨h.stable, h.forth, h.back⟩, hab⟩

theorem Equiv.refl (G : GSet.{u}) : Equiv G G :=
  nn_intro ⟨fun a b => ¬¬(a = b), ⟨fun _ _ => inferInstance,
    fun _ _ hab a' ha' => Stable.of_nn hab fun e => nn_intro ⟨a', e ▸ ha', nn_intro rfl⟩,
    fun _ _ hab b' hb' => Stable.of_nn hab fun e => nn_intro ⟨b', e ▸ hb', nn_intro rfl⟩⟩,
    nn_intro rfl⟩

theorem IsBisim.symm {G H : GSet.{u}} {Z} (h : IsBisim G H Z) : IsBisim H G (fun b a => Z a b) :=
  ⟨fun b a => h.stable a b, fun b a hab b' hb' => h.back a b hab b' hb',
   fun b a hab a' ha' => h.forth a b hab a' ha'⟩

theorem Equiv.symm {G H : GSet.{u}} (h : Equiv G H) : Equiv H G :=
  nn_map (fun ⟨Z, hZ, hr⟩ => ⟨fun b a => Z a b, hZ.symm, hr⟩) h

theorem IsBisim.trans {G H K : GSet.{u}} {Z Z'} (h : IsBisim G H Z) (h' : IsBisim H K Z') :
    IsBisim G K (fun a c => ¬¬∃ b, Z a b ∧ Z' b c) :=
  ⟨fun _ _ => inferInstance,
   fun a c hac a' ha' => Stable.of_nn hac fun ⟨b, hab, hbc⟩ =>
     Stable.of_nn (h.forth a b hab a' ha') fun ⟨b', hb', hab'⟩ =>
     nn_map (fun ⟨c', hc', hbc'⟩ => ⟨c', hc', nn_intro ⟨b', hab', hbc'⟩⟩) (h'.forth b c hbc b' hb'),
   fun a c hac c' hc' => Stable.of_nn hac fun ⟨b, hab, hbc⟩ =>
     Stable.of_nn (h'.back b c hbc c' hc') fun ⟨b', hb', hbc'⟩ =>
     nn_map (fun ⟨a', ha', hab'⟩ => ⟨a', ha', nn_intro ⟨b', hab', hbc'⟩⟩) (h.back a b hab b' hb')⟩

theorem Equiv.trans {G H K : GSet.{u}} (h : Equiv G H) (h' : Equiv H K) : Equiv G K :=
  Stable.of_nn h fun ⟨_, hZ, hr⟩ => Stable.of_nn h' fun ⟨_, hZ', hr'⟩ =>
    nn_intro ⟨_, hZ.trans hZ', nn_intro ⟨H.r, hr, hr'⟩⟩

/-! ### Membership respects equivalence -/

theorem Mem.congr_left {K K' G : GSet.{u}} (e : Equiv K K') (h : Mem K G) : Mem K' G :=
  nn_map (fun ⟨a, ha, hK⟩ => ⟨a, ha, e.symm.trans hK⟩) h

theorem Mem.congr_right {K G G' : GSet.{u}} (e : Equiv G G') (h : Mem K G) : Mem K G' :=
  Stable.of_nn e fun ⟨_, hZ, hr⟩ => Stable.of_nn h fun ⟨a, ha, hK⟩ =>
    nn_map (fun ⟨b, hb, hab⟩ => ⟨b, hb, hK.trans (hZ.at' hab)⟩) (hZ.forth _ _ hr a ha)

theorem mem_congr_left {K K' G : GSet.{u}} (e : Equiv K K') : Mem K G ↔ Mem K' G :=
  ⟨Mem.congr_left e, Mem.congr_left e.symm⟩

theorem mem_congr_right {K G G' : GSet.{u}} (e : Equiv G G') : Mem K G ↔ Mem K G' :=
  ⟨Mem.congr_right e, Mem.congr_right e.symm⟩

theorem at'_mem {G : GSet.{u}} {a : G.A} (h : G.R a G.r) : Mem (G.at' a) G :=
  nn_intro ⟨a, h, Equiv.refl _⟩

/-- Membership in a pointed graph, at the vertex level. -/
theorem mem_at' {K G : GSet.{u}} {a : G.A} :
    Mem K (G.at' a) ↔ ¬¬∃ a', G.R a' a ∧ Equiv K (G.at' a') := Iff.rfl

/-! ### Extensionality -/

/-- Graphs with the same members are equivalent. -/
theorem ext {G H : GSet.{u}} (h : ∀ K, Mem K G ↔ Mem K H) : Equiv G H := by
  let Z : G.A → H.A → Prop := fun a b => ∀ K, Mem K (G.at' a) ↔ Mem K (H.at' b)
  refine nn_intro ⟨Z, ⟨fun _ _ => inferInstance, ?_, ?_⟩, h⟩
  · intro a b hab a' ha'
    refine nn_map (fun ⟨b', hb', e⟩ => ⟨b', hb', fun K => ?_⟩) ((hab _).1 (at'_mem ha'))
    exact mem_congr_right e
  · intro a b hab b' hb'
    refine nn_map (fun ⟨a', ha', e⟩ => ⟨a', ha', fun K => ?_⟩) ((hab _).2 (at'_mem hb'))
    exact (mem_congr_right e).symm

theorem equiv_iff_mem {G H : GSet.{u}} : Equiv G H ↔ ∀ K, Mem K G ↔ Mem K H :=
  ⟨fun e _ => mem_congr_right e, ext⟩

/-! ### Stable membership induction -/

/-- `∈`-induction for stable predicates on graph sets, from `SWF` of the vertex relation. -/
theorem mem_induction {F : GSet.{u} → Prop} [∀ G, Stable (F G)]
    (H : ∀ G, (∀ K, Mem K G → F K) → F G) (G : GSet.{u}) : F G := by
  have key : ∀ a, ∀ K, Equiv K (G.at' a) → F K := by
    refine G.swf (fun a => ∀ K, Equiv K (G.at' a) → F K) (fun _ => inferInstance) ?_
    intro a ih K hK
    refine H K fun K' hK' => ?_
    exact Stable.of_nn (Mem.congr_right hK hK') fun ⟨a', ha', e⟩ => ih a' ha' K' e
  exact key G.r G (Equiv.refl G)

end GSet
