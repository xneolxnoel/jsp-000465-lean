/-
Copyright (c) 2026 Justin Sun Prize formalization effort. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Sun Prize formalization effort
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Setoid.Basic
import Jsp000465Lean.Templates

/-!
# Admissible identifications and quotients (paper Def. 2.2–2.4)

An equivalence on a properly 2-colored template is **admissible** when it
identifies only same-color vertices and remains injective on each distinguished
subgraph `T₁`, `T₂`. The quotient graph is the simple graph on equivalence
classes with an edge between classes whenever some representatives are adjacent.
-/

namespace Compactness

open SimpleGraph Function

set_option linter.style.header false
set_option linter.unusedDecidableInType false
set_option linter.unreachableTactic false

/-! ## Proper 2-colorings of the templates -/

/-- Proper 2-coloring of `J₀`. -/
def J0.coloring : Coloring J0 (Fin 2) := Coloring.mk J0.color <| by
  intro u v h; revert u v; decide

/-- Proper 2-coloring of `K₀`. -/
def K0.coloring : Coloring K0 (Fin 2) := Coloring.mk K0.color <| by
  intro u v h
  have mem : s(u, v) ∈ K0.edgeList := by
    simpa [K0, fromEdgeSet_adj] using h.left
  have hprop : K0.edgeProper s(u, v) = true :=
    (List.all_eq_true.mp K0.all_edges_proper) _ mem
  simpa [K0.edgeProper, Sym2.lift_mk, decide_eq_true_eq] using hprop

/-! ## Distinguished subgraphs `T₁`, `T₂` -/

/-- First `S₂` copy inside `J₀`. -/
def J0.T1 : Set (Fin 21) :=
  {0, 1, 2, 4, 5, 8, 9, 10, 11, 12, 13}

/-- Second `S₂` copy inside `J₀`. -/
def J0.T2 : Set (Fin 21) :=
  {3, 1, 2, 6, 7, 14, 15, 16, 17, 18, 19}

/-- First `S₃` copy in `K₀` (vertices `0..14`). -/
def K0.T1 : Set (Fin 30) := {v : Fin 30 | v.val < 15}

/-- Second `S₃` copy in `K₀` (vertices `15..29`). -/
def K0.T2 : Set (Fin 30) := {v : Fin 30 | 15 ≤ v.val}

instance : DecidablePred (· ∈ J0.T1) := by
  classical
  unfold J0.T1
  infer_instance

instance : DecidablePred (· ∈ J0.T2) := by
  classical
  unfold J0.T2
  infer_instance

instance : DecidablePred (· ∈ K0.T1) := by
  classical
  unfold K0.T1
  infer_instance

instance : DecidablePred (· ∈ K0.T2) := by
  classical
  unfold K0.T2
  infer_instance

/-! ## Admissible setoids -/

/-- Paper Def. 2.2: admissible equivalence on a colored template. -/
structure IsAdmissible {V : Type*} (color : V → Fin 2) (T1 T2 : Set V) (s : Setoid V) : Prop where
  sameColor : ∀ {v w}, s.r v w → color v = color w
  injT1 : ∀ {v w}, v ∈ T1 → w ∈ T1 → s.r v w → v = w
  injT2 : ∀ {v w}, v ∈ T2 → w ∈ T2 → s.r v w → v = w

/-- Admissible setoids on `J₀`. -/
def J0.Admissible (s : Setoid (Fin 21)) : Prop :=
  IsAdmissible J0.color J0.T1 J0.T2 s

/-- Admissible setoids on `K₀`. -/
def K0.Admissible (s : Setoid (Fin 30)) : Prop :=
  IsAdmissible K0.color K0.T1 K0.T2 s

/-- Membership condition for `J`: admissible and `x ≉ x'` (`0 ≉ 3`). -/
def J0.AdmissibleForJ (s : Setoid (Fin 21)) : Prop :=
  J0.Admissible s ∧ ¬ s.r 0 3

/-! ## Quotient graph -/

/--
Simple graph on equivalence classes (paper Def. 2.2): `[v][w]` is an edge when
some representatives are adjacent in `G`. Loops are suppressed by `fromRel`.
-/
def quotientGraph {V : Type*} (G : SimpleGraph V) (s : Setoid V) :
    SimpleGraph (Quotient s) :=
  SimpleGraph.fromRel fun q1 q2 =>
    ∃ v w : V, Quotient.mk s v = q1 ∧ Quotient.mk s w = q2 ∧ G.Adj v w

theorem quotientGraph_adj {V : Type*} {G : SimpleGraph V} {s : Setoid V}
    {q1 q2 : Quotient s} :
    (quotientGraph G s).Adj q1 q2 ↔
      q1 ≠ q2 ∧ ∃ v w : V, Quotient.mk s v = q1 ∧ Quotient.mk s w = q2 ∧ G.Adj v w := by
  constructor
  · intro h
    simp only [quotientGraph, SimpleGraph.fromRel] at h
    rcases h with ⟨hne, hrel⟩
    refine ⟨hne, ?_⟩
    rcases hrel with ⟨v, w, hv, hw, hadj⟩ | ⟨v, w, hv, hw, hadj⟩
    · exact ⟨v, w, hv, hw, hadj⟩
    · exact ⟨w, v, hw, hv, hadj.symm⟩
  · rintro ⟨hne, v, w, hv, hw, hadj⟩
    simp only [quotientGraph, SimpleGraph.fromRel]
    exact ⟨hne, Or.inl ⟨v, w, hv, hw, hadj⟩⟩

/-- Under a proper coloring and an admissible setoid, adjacent vertices lie in distinct classes. -/
theorem admissible_adj_not_rel {V : Type*} {G : SimpleGraph V}
    (color : V → Fin 2) {T1 T2 : Set V} {s : Setoid V}
    (hAdm : IsAdmissible color T1 T2 s)
    (hProper : ∀ {u v}, G.Adj u v → color u ≠ color v)
    {a b : V} (hab : G.Adj a b) : ¬ s.r a b := by
  intro hrel
  exact hProper hab (hAdm.sameColor hrel)

/-- Canonical projection homomorphism for admissible quotients of properly colored graphs. -/
def quotientHomAdmissible {V : Type*} {G : SimpleGraph V}
    (color : V → Fin 2) {T1 T2 : Set V} {s : Setoid V}
    (hAdm : IsAdmissible color T1 T2 s)
    (hProper : ∀ {u v}, G.Adj u v → color u ≠ color v) :
    G →g quotientGraph G s where
  toFun := Quotient.mk s
  map_rel' := by
    intro a b hab
    rw [quotientGraph_adj]
    refine ⟨?_, a, b, rfl, rfl, hab⟩
    intro heq
    exact admissible_adj_not_rel color hAdm hProper hab (Quotient.exact heq)

theorem quotientHomAdmissible_surjective {V : Type*} {G : SimpleGraph V}
    (color : V → Fin 2) {T1 T2 : Set V} {s : Setoid V}
    (hAdm : IsAdmissible color T1 T2 s)
    (hProper : ∀ {u v}, G.Adj u v → color u ≠ color v) :
    Surjective (quotientHomAdmissible color hAdm hProper) := by
  intro q
  exact Quotient.mk_surjective q

/-- Quotients of connected graphs by admissible setoids remain connected. -/
theorem quotientGraph_connected_of_admissible {V : Type*} [Nonempty V] {G : SimpleGraph V}
    (hG : G.Connected) (color : V → Fin 2) {T1 T2 : Set V} {s : Setoid V}
    (hAdm : IsAdmissible color T1 T2 s)
    (hProper : ∀ {u v}, G.Adj u v → color u ≠ color v) :
    (quotientGraph G s).Connected := by
  have : Nonempty (Quotient s) := ⟨Quotient.mk s (Classical.arbitrary V)⟩
  exact ⟨hG.preconnected.map (quotientHomAdmissible color hAdm hProper)
    (quotientHomAdmissible_surjective color hAdm hProper)⟩

/-! ## Bipartiteness of admissible quotients -/

noncomputable def quotientColor {V : Type*} (color : V → Fin 2) {T1 T2 : Set V}
    {s : Setoid V} (h : IsAdmissible color T1 T2 s) : Quotient s → Fin 2 :=
  Quotient.lift color fun _a _b hab => h.sameColor hab

theorem quotientGraph_isBipartite {V : Type*} {G : SimpleGraph V}
    (color : V → Fin 2) {T1 T2 : Set V} {s : Setoid V}
    (hAdm : IsAdmissible color T1 T2 s)
    (hProper : ∀ {u v}, G.Adj u v → color u ≠ color v) :
    (quotientGraph G s).IsBipartite := by
  refine ⟨Coloring.mk (quotientColor color hAdm) ?_⟩
  intro q1 q2 hq
  rw [quotientGraph_adj] at hq
  rcases hq with ⟨_, v, w, hv, hw, hadj⟩
  have cv : quotientColor color hAdm q1 = color v := by
    subst hv; rfl
  have cw : quotientColor color hAdm q2 = color w := by
    subst hw; rfl
  rw [cv, cw]
  exact hProper hadj

theorem J0.color_proper {u v : Fin 21} (h : J0.Adj u v) : J0.color u ≠ J0.color v :=
  J0.coloring.valid h

theorem K0.color_proper {u v : Fin 30} (h : K0.Adj u v) : K0.color u ≠ K0.color v :=
  K0.coloring.valid h

theorem J0.quotient_isBipartite {s : Setoid (Fin 21)} (h : J0.Admissible s) :
    (quotientGraph J0 s).IsBipartite :=
  quotientGraph_isBipartite J0.color h J0.color_proper

theorem K0.quotient_isBipartite {s : Setoid (Fin 30)} (h : K0.Admissible s) :
    (quotientGraph K0 s).IsBipartite :=
  quotientGraph_isBipartite K0.color h K0.color_proper

/-! ## Discrete (identity) setoid -/

/-- The discrete setoid (equality). -/
abbrev discreteSetoid (V : Type*) : Setoid V := ⊥

theorem J0.discrete_admissible : J0.Admissible (discreteSetoid (Fin 21)) where
  sameColor := by
    intro v w h
    change v = w at h
    subst h; rfl
  injT1 := by
    intro v w _ _ h
    exact h
  injT2 := by
    intro v w _ _ h
    exact h

theorem J0.discrete_admissibleForJ : J0.AdmissibleForJ (discreteSetoid (Fin 21)) := by
  refine ⟨J0.discrete_admissible, ?_⟩
  change ¬ ((0 : Fin 21) = 3)
  decide

theorem K0.discrete_admissible : K0.Admissible (discreteSetoid (Fin 30)) where
  sameColor := by
    intro v w h
    change v = w at h
    subst h; rfl
  injT1 := by
    intro v w _ _ h
    exact h
  injT2 := by
    intro v w _ _ h
    exact h

/-! ## Cycle survival via injective images of template vertices -/

theorem quotient_contains_C8_of_injOn {n : ℕ} {G : SimpleGraph (Fin n)}
    (verts : Fin 8 → Fin n)
    (hHom : ∀ {a b : Fin 8}, (cycleGraph 8).Adj a b → G.Adj (verts a) (verts b))
    (_hInj : Injective verts)
    (s : Setoid (Fin n))
    (hDistinct : ∀ i j : Fin 8, s.r (verts i) (verts j) → i = j) :
    cycleGraph 8 ⊑ quotientGraph G s := by
  let f : Fin 8 → Quotient s := fun i => Quotient.mk s (verts i)
  have hfInj : Injective f := by
    intro i j hij
    exact hDistinct i j (Quotient.exact hij)
  have hfHom :
      ∀ {a b : Fin 8}, (cycleGraph 8).Adj a b → (quotientGraph G s).Adj (f a) (f b) := by
    intro a b hab
    rw [quotientGraph_adj]
    refine ⟨?_, verts a, verts b, rfl, rfl, hHom hab⟩
    intro heq
    have : a = b := hfInj heq
    exact (cycleGraph 8).irrefl (this ▸ hab)
  exact ⟨Hom.toCopy ⟨f, hfHom⟩ hfInj⟩

theorem J0.C8verts_mem_T1 (i : Fin 8) : J0.C8verts i ∈ J0.T1 := by
  fin_cases i <;> decide

theorem J0.admissible_C8verts_distinct {s : Setoid (Fin 21)} (h : J0.Admissible s) :
    ∀ i j : Fin 8, s.r (J0.C8verts i) (J0.C8verts j) → i = j := by
  intro i j hij
  exact J0.C8verts_injective (h.injT1 (J0.C8verts_mem_T1 i) (J0.C8verts_mem_T1 j) hij)

theorem K0.C8verts_mem_T1 (i : Fin 8) : K0.C8verts i ∈ K0.T1 := by
  fin_cases i <;> decide

theorem K0.admissible_C8verts_distinct {s : Setoid (Fin 30)} (h : K0.Admissible s) :
    ∀ i j : Fin 8, s.r (K0.C8verts i) (K0.C8verts j) → i = j := by
  intro i j hij
  exact K0.C8verts_injective (h.injT1 (K0.C8verts_mem_T1 i) (K0.C8verts_mem_T1 j) hij)

theorem J0.admissible_quotient_contains_C8 {s : Setoid (Fin 21)} (h : J0.Admissible s) :
    cycleGraph 8 ⊑ quotientGraph J0 s :=
  quotient_contains_C8_of_injOn J0.C8verts J0.C8verts_hom J0.C8verts_injective s
    (J0.admissible_C8verts_distinct h)

theorem K0.admissible_quotient_contains_C8 {s : Setoid (Fin 30)} (h : K0.Admissible s) :
    cycleGraph 8 ⊑ quotientGraph K0 s :=
  quotient_contains_C8_of_injOn K0.C8verts K0.C8verts_hom K0.C8verts_injective s
    (K0.admissible_C8verts_distinct h)

theorem J0.admissible_quotient_contains_cycle {s : Setoid (Fin 21)} (h : J0.Admissible s) :
    ∃ (q : Quotient s) (p : (quotientGraph J0 s).Walk q q), p.IsCycle := by
  obtain ⟨v, p, hp, _⟩ :=
    (cycleGraph_isContained_iff (by decide : 2 < 8)).mp (J0.admissible_quotient_contains_C8 h)
  exact ⟨v, p, hp⟩

theorem K0.admissible_quotient_contains_cycle {s : Setoid (Fin 30)} (h : K0.Admissible s) :
    ∃ (q : Quotient s) (p : (quotientGraph K0 s).Walk q q), p.IsCycle := by
  obtain ⟨v, p, hp, _⟩ :=
    (cycleGraph_isContained_iff (by decide : 2 < 8)).mp (K0.admissible_quotient_contains_C8 h)
  exact ⟨v, p, hp⟩

theorem J0.admissible_quotient_not_acyclic {s : Setoid (Fin 21)} (h : J0.Admissible s) :
    ¬ (quotientGraph J0 s).IsAcyclic := by
  rcases J0.admissible_quotient_contains_cycle h with ⟨_, p, hp⟩
  exact fun hac => hac p hp

theorem K0.admissible_quotient_not_acyclic {s : Setoid (Fin 30)} (h : K0.Admissible s) :
    ¬ (quotientGraph K0 s).IsAcyclic := by
  rcases K0.admissible_quotient_contains_cycle h with ⟨_, p, hp⟩
  exact fun hac => hac p hp

/-! ## Connectedness of templates (explicit spanning-tree walks) -/

theorem J0.reachable_zero (v : Fin 21) : J0.Reachable v 0 := by
  fin_cases v
  · exact Reachable.refl _
  · exact (((((by decide : J0.Adj 1 10).reachable).trans ((by decide : J0.Adj 10 4).reachable)).trans ((by decide : J0.Adj 4 8).reachable)).trans ((by decide : J0.Adj 8 0).reachable))
  · exact (((((by decide : J0.Adj 2 12).reachable).trans ((by decide : J0.Adj 12 4).reachable)).trans ((by decide : J0.Adj 4 8).reachable)).trans ((by decide : J0.Adj 8 0).reachable))
  · exact (((by decide : J0.Adj 3 20).reachable).trans ((by decide : J0.Adj 20 0).reachable))
  · exact (((by decide : J0.Adj 4 8).reachable).trans ((by decide : J0.Adj 8 0).reachable))
  · exact (((by decide : J0.Adj 5 9).reachable).trans ((by decide : J0.Adj 9 0).reachable))
  · exact (((((((by decide : J0.Adj 6 16).reachable).trans ((by decide : J0.Adj 16 1).reachable)).trans ((by decide : J0.Adj 1 10).reachable)).trans ((by decide : J0.Adj 10 4).reachable)).trans ((by decide : J0.Adj 4 8).reachable)).trans ((by decide : J0.Adj 8 0).reachable))
  · exact (((((((by decide : J0.Adj 7 17).reachable).trans ((by decide : J0.Adj 17 1).reachable)).trans ((by decide : J0.Adj 1 10).reachable)).trans ((by decide : J0.Adj 10 4).reachable)).trans ((by decide : J0.Adj 4 8).reachable)).trans ((by decide : J0.Adj 8 0).reachable))
  · exact ((by decide : J0.Adj 8 0).reachable)
  · exact ((by decide : J0.Adj 9 0).reachable)
  · exact ((((by decide : J0.Adj 10 4).reachable).trans ((by decide : J0.Adj 4 8).reachable)).trans ((by decide : J0.Adj 8 0).reachable))
  · exact ((((by decide : J0.Adj 11 5).reachable).trans ((by decide : J0.Adj 5 9).reachable)).trans ((by decide : J0.Adj 9 0).reachable))
  · exact ((((by decide : J0.Adj 12 4).reachable).trans ((by decide : J0.Adj 4 8).reachable)).trans ((by decide : J0.Adj 8 0).reachable))
  · exact ((((by decide : J0.Adj 13 5).reachable).trans ((by decide : J0.Adj 5 9).reachable)).trans ((by decide : J0.Adj 9 0).reachable))
  · exact ((((by decide : J0.Adj 14 3).reachable).trans ((by decide : J0.Adj 3 20).reachable)).trans ((by decide : J0.Adj 20 0).reachable))
  · exact ((((by decide : J0.Adj 15 3).reachable).trans ((by decide : J0.Adj 3 20).reachable)).trans ((by decide : J0.Adj 20 0).reachable))
  · exact ((((((by decide : J0.Adj 16 1).reachable).trans ((by decide : J0.Adj 1 10).reachable)).trans ((by decide : J0.Adj 10 4).reachable)).trans ((by decide : J0.Adj 4 8).reachable)).trans ((by decide : J0.Adj 8 0).reachable))
  · exact ((((((by decide : J0.Adj 17 1).reachable).trans ((by decide : J0.Adj 1 10).reachable)).trans ((by decide : J0.Adj 10 4).reachable)).trans ((by decide : J0.Adj 4 8).reachable)).trans ((by decide : J0.Adj 8 0).reachable))
  · exact ((((((by decide : J0.Adj 18 2).reachable).trans ((by decide : J0.Adj 2 12).reachable)).trans ((by decide : J0.Adj 12 4).reachable)).trans ((by decide : J0.Adj 4 8).reachable)).trans ((by decide : J0.Adj 8 0).reachable))
  · exact ((((((by decide : J0.Adj 19 2).reachable).trans ((by decide : J0.Adj 2 12).reachable)).trans ((by decide : J0.Adj 12 4).reachable)).trans ((by decide : J0.Adj 4 8).reachable)).trans ((by decide : J0.Adj 8 0).reachable))
  · exact ((by decide : J0.Adj 20 0).reachable)

theorem J0_connected : J0.Connected :=
  ⟨fun u v => (J0.reachable_zero u).trans (J0.reachable_zero v).symm⟩

theorem K0.reachable_zero (v : Fin 30) : K0.Reachable v 0 := by
  fin_cases v
  · exact Reachable.refl _
  · exact (((((by decide : K0.Adj 1 9).reachable).trans ((by decide : K0.Adj 9 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact (((((by decide : K0.Adj 2 12).reachable).trans ((by decide : K0.Adj 12 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact (((by decide : K0.Adj 3 6).reachable).trans ((by decide : K0.Adj 6 0).reachable))
  · exact (((by decide : K0.Adj 4 7).reachable).trans ((by decide : K0.Adj 7 0).reachable))
  · exact (((by decide : K0.Adj 5 8).reachable).trans ((by decide : K0.Adj 8 0).reachable))
  · exact ((by decide : K0.Adj 6 0).reachable)
  · exact ((by decide : K0.Adj 7 0).reachable)
  · exact ((by decide : K0.Adj 8 0).reachable)
  · exact ((((by decide : K0.Adj 9 3).reachable).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact ((((by decide : K0.Adj 10 4).reachable).trans ((by decide : K0.Adj 4 7).reachable)).trans ((by decide : K0.Adj 7 0).reachable))
  · exact ((((by decide : K0.Adj 11 5).reachable).trans ((by decide : K0.Adj 5 8).reachable)).trans ((by decide : K0.Adj 8 0).reachable))
  · exact ((((by decide : K0.Adj 12 3).reachable).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact ((((by decide : K0.Adj 13 4).reachable).trans ((by decide : K0.Adj 4 7).reachable)).trans ((by decide : K0.Adj 7 0).reachable))
  · exact ((((by decide : K0.Adj 14 5).reachable).trans ((by decide : K0.Adj 5 8).reachable)).trans ((by decide : K0.Adj 8 0).reachable))
  · exact ((((((by decide : K0.Adj 15 21).reachable).trans ((by decide : K0.Adj 21 18).reachable)).trans ((by decide : K0.Adj 18 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact ((((((by decide : K0.Adj 16 24).reachable).trans ((by decide : K0.Adj 24 18).reachable)).trans ((by decide : K0.Adj 18 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact ((((((by decide : K0.Adj 17 27).reachable).trans ((by decide : K0.Adj 27 18).reachable)).trans ((by decide : K0.Adj 18 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact ((((by decide : K0.Adj 18 3).reachable).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact ((((((((by decide : K0.Adj 19 22).reachable).trans ((by decide : K0.Adj 22 15).reachable)).trans ((by decide : K0.Adj 15 21).reachable)).trans ((by decide : K0.Adj 21 18).reachable)).trans ((by decide : K0.Adj 18 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact ((((((((by decide : K0.Adj 20 23).reachable).trans ((by decide : K0.Adj 23 15).reachable)).trans ((by decide : K0.Adj 15 21).reachable)).trans ((by decide : K0.Adj 21 18).reachable)).trans ((by decide : K0.Adj 18 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact (((((by decide : K0.Adj 21 18).reachable).trans ((by decide : K0.Adj 18 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact (((((((by decide : K0.Adj 22 15).reachable).trans ((by decide : K0.Adj 15 21).reachable)).trans ((by decide : K0.Adj 21 18).reachable)).trans ((by decide : K0.Adj 18 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact (((((((by decide : K0.Adj 23 15).reachable).trans ((by decide : K0.Adj 15 21).reachable)).trans ((by decide : K0.Adj 21 18).reachable)).trans ((by decide : K0.Adj 18 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact (((((by decide : K0.Adj 24 18).reachable).trans ((by decide : K0.Adj 18 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact (((((((by decide : K0.Adj 25 16).reachable).trans ((by decide : K0.Adj 16 24).reachable)).trans ((by decide : K0.Adj 24 18).reachable)).trans ((by decide : K0.Adj 18 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact (((((((by decide : K0.Adj 26 16).reachable).trans ((by decide : K0.Adj 16 24).reachable)).trans ((by decide : K0.Adj 24 18).reachable)).trans ((by decide : K0.Adj 18 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact (((((by decide : K0.Adj 27 18).reachable).trans ((by decide : K0.Adj 18 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact (((((((by decide : K0.Adj 28 17).reachable).trans ((by decide : K0.Adj 17 27).reachable)).trans ((by decide : K0.Adj 27 18).reachable)).trans ((by decide : K0.Adj 18 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))
  · exact (((((((by decide : K0.Adj 29 17).reachable).trans ((by decide : K0.Adj 17 27).reachable)).trans ((by decide : K0.Adj 27 18).reachable)).trans ((by decide : K0.Adj 18 3).reachable)).trans ((by decide : K0.Adj 3 6).reachable)).trans ((by decide : K0.Adj 6 0).reachable))

theorem K0_connected : K0.Connected :=
  ⟨fun u v => (K0.reachable_zero u).trans (K0.reachable_zero v).symm⟩

theorem S2.reachable_zero (v : Fin 11) : S2.Reachable v 0 := by
  fin_cases v
  · exact Reachable.refl _
  · exact (((((by decide : S2.Adj 1 7).reachable).trans ((by decide : S2.Adj 7 3).reachable)).trans ((by decide : S2.Adj 3 5).reachable)).trans ((by decide : S2.Adj 5 0).reachable))
  · exact (((((by decide : S2.Adj 2 9).reachable).trans ((by decide : S2.Adj 9 3).reachable)).trans ((by decide : S2.Adj 3 5).reachable)).trans ((by decide : S2.Adj 5 0).reachable))
  · exact (((by decide : S2.Adj 3 5).reachable).trans ((by decide : S2.Adj 5 0).reachable))
  · exact (((by decide : S2.Adj 4 6).reachable).trans ((by decide : S2.Adj 6 0).reachable))
  · exact ((by decide : S2.Adj 5 0).reachable)
  · exact ((by decide : S2.Adj 6 0).reachable)
  · exact ((((by decide : S2.Adj 7 3).reachable).trans ((by decide : S2.Adj 3 5).reachable)).trans ((by decide : S2.Adj 5 0).reachable))
  · exact ((((by decide : S2.Adj 8 4).reachable).trans ((by decide : S2.Adj 4 6).reachable)).trans ((by decide : S2.Adj 6 0).reachable))
  · exact ((((by decide : S2.Adj 9 3).reachable).trans ((by decide : S2.Adj 3 5).reachable)).trans ((by decide : S2.Adj 5 0).reachable))
  · exact ((((by decide : S2.Adj 10 4).reachable).trans ((by decide : S2.Adj 4 6).reachable)).trans ((by decide : S2.Adj 6 0).reachable))

theorem S2_connected : S2.Connected :=
  ⟨fun u v => (S2.reachable_zero u).trans (S2.reachable_zero v).symm⟩

theorem S3.reachable_zero (v : Fin 15) : S3.Reachable v 0 := by
  fin_cases v
  · exact Reachable.refl _
  · exact (((((by decide : S3.Adj 1 9).reachable).trans ((by decide : S3.Adj 9 3).reachable)).trans ((by decide : S3.Adj 3 6).reachable)).trans ((by decide : S3.Adj 6 0).reachable))
  · exact (((((by decide : S3.Adj 2 12).reachable).trans ((by decide : S3.Adj 12 3).reachable)).trans ((by decide : S3.Adj 3 6).reachable)).trans ((by decide : S3.Adj 6 0).reachable))
  · exact (((by decide : S3.Adj 3 6).reachable).trans ((by decide : S3.Adj 6 0).reachable))
  · exact (((by decide : S3.Adj 4 7).reachable).trans ((by decide : S3.Adj 7 0).reachable))
  · exact (((by decide : S3.Adj 5 8).reachable).trans ((by decide : S3.Adj 8 0).reachable))
  · exact ((by decide : S3.Adj 6 0).reachable)
  · exact ((by decide : S3.Adj 7 0).reachable)
  · exact ((by decide : S3.Adj 8 0).reachable)
  · exact ((((by decide : S3.Adj 9 3).reachable).trans ((by decide : S3.Adj 3 6).reachable)).trans ((by decide : S3.Adj 6 0).reachable))
  · exact ((((by decide : S3.Adj 10 4).reachable).trans ((by decide : S3.Adj 4 7).reachable)).trans ((by decide : S3.Adj 7 0).reachable))
  · exact ((((by decide : S3.Adj 11 5).reachable).trans ((by decide : S3.Adj 5 8).reachable)).trans ((by decide : S3.Adj 8 0).reachable))
  · exact ((((by decide : S3.Adj 12 3).reachable).trans ((by decide : S3.Adj 3 6).reachable)).trans ((by decide : S3.Adj 6 0).reachable))
  · exact ((((by decide : S3.Adj 13 4).reachable).trans ((by decide : S3.Adj 4 7).reachable)).trans ((by decide : S3.Adj 7 0).reachable))
  · exact ((((by decide : S3.Adj 14 5).reachable).trans ((by decide : S3.Adj 5 8).reachable)).trans ((by decide : S3.Adj 8 0).reachable))

theorem S3_connected : S3.Connected :=
  ⟨fun u v => (S3.reachable_zero u).trans (S3.reachable_zero v).symm⟩

theorem J0.admissible_quotient_connected {s : Setoid (Fin 21)} (h : J0.Admissible s) :
    (quotientGraph J0 s).Connected :=
  quotientGraph_connected_of_admissible J0_connected J0.color h J0.color_proper

theorem K0.admissible_quotient_connected {s : Setoid (Fin 30)} (h : K0.Admissible s) :
    (quotientGraph K0 s).Connected :=
  quotientGraph_connected_of_admissible K0_connected K0.color h K0.color_proper

end Compactness
