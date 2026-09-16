/-
Copyright (c) 2026 Justin Sun Prize formalization effort. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Sun Prize formalization effort
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fin.Basic

/-!
# Subdivision templates S₂, S₃ and amalgamations J₀, K₀

Following OpenAI *ten-proofs* Chapter 10, Definitions 2.1–2.4.
-/

namespace Compactness

open SimpleGraph Function

set_option linter.style.header false
set_option linter.unusedDecidableInType false

/-! ## Edge-set definitions -/

/--
`S₂` vertices (`Fin 11`):
* `0,1,2` — bases; `3,4` — centers
* `5 + 2*i + j` — subdivision vertex on base `i` — center `j`
-/
def S2.edgeList : List (Sym2 (Fin 11)) :=
  [ s(0, 5), s(5, 3), s(0, 6), s(6, 4)
  , s(1, 7), s(7, 3), s(1, 8), s(8, 4)
  , s(2, 9), s(9, 3), s(2, 10), s(10, 4) ]

def S2 : SimpleGraph (Fin 11) := fromEdgeSet {e | e ∈ S2.edgeList}

instance : DecidableRel S2.Adj := by
  classical
  unfold S2
  infer_instance

/--
`S₃` vertices (`Fin 15`):
* `0,1,2` — bases; `3,4,5` — centers
* `6 + 3*i + j` — subdivision on base `i` — center `j`
-/
def S3.edgeList : List (Sym2 (Fin 15)) :=
  [ s(0, 6), s(6, 3), s(0, 7), s(7, 4), s(0, 8), s(8, 5)
  , s(1, 9), s(9, 3), s(1, 10), s(10, 4), s(1, 11), s(11, 5)
  , s(2, 12), s(12, 3), s(2, 13), s(13, 4), s(2, 14), s(14, 5) ]

def S3 : SimpleGraph (Fin 15) := fromEdgeSet {e | e ∈ S3.edgeList}

instance : DecidableRel S3.Adj := by
  classical
  unfold S3
  infer_instance

/--
`J₀` vertices (`Fin 21`):
* `0=x`, `1=y`, `2=z`, `3=x'`
* `4,5` / `6,7` — centers of the two `S₂` copies
* `8..13` / `14..19` — subdivision vertices
* `20=λ`
-/
def J0.edgeList : List (Sym2 (Fin 21)) :=
  [ s(0, 8), s(8, 4), s(0, 9), s(9, 5)
  , s(1, 10), s(10, 4), s(1, 11), s(11, 5)
  , s(2, 12), s(12, 4), s(2, 13), s(13, 5)
  , s(3, 14), s(14, 6), s(3, 15), s(15, 7)
  , s(1, 16), s(16, 6), s(1, 17), s(17, 7)
  , s(2, 18), s(18, 6), s(2, 19), s(19, 7)
  , s(20, 0), s(20, 3) ]

def J0 : SimpleGraph (Fin 21) := fromEdgeSet {e | e ∈ J0.edgeList}

instance : DecidableRel J0.Adj := by
  classical
  unfold J0
  infer_instance

/--
`K₀` edge list (explicit): first `S₃` on `0..14`, second on `15..29`, plus bridge
`3—18` between centers. Color-reversal of the second copy is reflected only in
`K0.color`, not in the uncolored edge set.
-/
def K0.edgeList : List (Sym2 (Fin 30)) :=
  [ s(0, 6), s(6, 3), s(0, 7), s(7, 4), s(0, 8), s(8, 5)
  , s(1, 9), s(9, 3), s(1, 10), s(10, 4), s(1, 11), s(11, 5)
  , s(2, 12), s(12, 3), s(2, 13), s(13, 4), s(2, 14), s(14, 5)
  , s(15, 21), s(21, 18), s(15, 22), s(22, 19), s(15, 23), s(23, 20)
  , s(16, 24), s(24, 18), s(16, 25), s(25, 19), s(16, 26), s(26, 20)
  , s(17, 27), s(27, 18), s(17, 28), s(28, 19), s(17, 29), s(29, 20)
  , s(3, 18) ]

def K0 : SimpleGraph (Fin 30) := fromEdgeSet {e | e ∈ K0.edgeList}

instance : DecidableRel K0.Adj := by
  classical
  unfold K0
  infer_instance

theorem S2_card : Fintype.card (Fin 11) = 11 := rfl
theorem S3_card : Fintype.card (Fin 15) = 15 := rfl
theorem J0_card : Fintype.card (Fin 21) = 21 := rfl
theorem K0_card : Fintype.card (Fin 30) = 30 := rfl

/-! ## Helper: build `cycleGraph 8 ⊑ G` from an explicit vertex map -/

theorem contains_C8_of_verts {n : ℕ} {G : SimpleGraph (Fin n)}
    (verts : Fin 8 → Fin n)
    (hHom : ∀ {a b : Fin 8}, (cycleGraph 8).Adj a b → G.Adj (verts a) (verts b))
    (hInj : Injective verts) :
    cycleGraph 8 ⊑ G :=
  ⟨Hom.toCopy ⟨verts, hHom⟩ hInj⟩

/-! ## Cycles via injective homs from `cycleGraph 8` -/

/-- Vertices of an 8-cycle in `S₂`: `0-5-3-7-1-8-4-6-(0)`. -/
def S2.C8verts : Fin 8 → Fin 11
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 5
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 7
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 8
  | ⟨6, _⟩ => 4
  | ⟨7, _⟩ => 6

theorem S2.C8verts_hom :
    ∀ {a b : Fin 8}, (cycleGraph 8).Adj a b → S2.Adj (S2.C8verts a) (S2.C8verts b) := by
  intro a b hab; revert a b; decide

theorem S2.C8verts_injective : Injective S2.C8verts := by
  intro a b h; revert a b; decide

theorem S2_contains_C8 : cycleGraph 8 ⊑ S2 :=
  contains_C8_of_verts S2.C8verts S2.C8verts_hom S2.C8verts_injective

theorem S2_contains_cycle : ∃ (v : Fin 11) (p : S2.Walk v v), p.IsCycle := by
  obtain ⟨v, p, hp, _⟩ := (cycleGraph_isContained_iff (by decide : 2 < 8)).mp S2_contains_C8
  exact ⟨v, p, hp⟩

theorem S2_not_acyclic : ¬ S2.IsAcyclic := by
  rcases S2_contains_cycle with ⟨_, p, hp⟩
  exact fun h ↦ h p hp

def S3.C8verts : Fin 8 → Fin 15
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 6
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 9
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 10
  | ⟨6, _⟩ => 4
  | ⟨7, _⟩ => 7

theorem S3.C8verts_hom :
    ∀ {a b : Fin 8}, (cycleGraph 8).Adj a b → S3.Adj (S3.C8verts a) (S3.C8verts b) := by
  intro a b hab; revert a b; decide

theorem S3.C8verts_injective : Injective S3.C8verts := by
  intro a b h; revert a b; decide

theorem S3_contains_C8 : cycleGraph 8 ⊑ S3 :=
  contains_C8_of_verts S3.C8verts S3.C8verts_hom S3.C8verts_injective

theorem S3_contains_cycle : ∃ (v : Fin 15) (p : S3.Walk v v), p.IsCycle := by
  obtain ⟨v, p, hp, _⟩ := (cycleGraph_isContained_iff (by decide : 2 < 8)).mp S3_contains_C8
  exact ⟨v, p, hp⟩

def J0.C8verts : Fin 8 → Fin 21
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 8
  | ⟨2, _⟩ => 4
  | ⟨3, _⟩ => 10
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 11
  | ⟨6, _⟩ => 5
  | ⟨7, _⟩ => 9

theorem J0.C8verts_hom :
    ∀ {a b : Fin 8}, (cycleGraph 8).Adj a b → J0.Adj (J0.C8verts a) (J0.C8verts b) := by
  intro a b hab; revert a b; decide

theorem J0.C8verts_injective : Injective J0.C8verts := by
  intro a b h; revert a b; decide

theorem J0_contains_C8 : cycleGraph 8 ⊑ J0 :=
  contains_C8_of_verts J0.C8verts J0.C8verts_hom J0.C8verts_injective

theorem J0_contains_cycle : ∃ (v : Fin 21) (p : J0.Walk v v), p.IsCycle := by
  obtain ⟨v, p, hp, _⟩ := (cycleGraph_isContained_iff (by decide : 2 < 8)).mp J0_contains_C8
  exact ⟨v, p, hp⟩

theorem J0_not_acyclic : ¬ J0.IsAcyclic := by
  rcases J0_contains_cycle with ⟨_, p, hp⟩
  exact fun h ↦ h p hp

def K0.C8verts : Fin 8 → Fin 30
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 6
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 9
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 10
  | ⟨6, _⟩ => 4
  | ⟨7, _⟩ => 7

theorem K0.C8verts_hom :
    ∀ {a b : Fin 8}, (cycleGraph 8).Adj a b → K0.Adj (K0.C8verts a) (K0.C8verts b) := by
  intro a b hab; revert a b; decide

theorem K0.C8verts_injective : Injective K0.C8verts := by
  intro a b h; revert a b; decide

theorem K0_contains_C8 : cycleGraph 8 ⊑ K0 :=
  contains_C8_of_verts K0.C8verts K0.C8verts_hom K0.C8verts_injective

theorem K0_contains_cycle : ∃ (v : Fin 30) (p : K0.Walk v v), p.IsCycle := by
  obtain ⟨v, p, hp, _⟩ := (cycleGraph_isContained_iff (by decide : 2 < 8)).mp K0_contains_C8
  exact ⟨v, p, hp⟩

theorem K0_not_acyclic : ¬ K0.IsAcyclic := by
  rcases K0_contains_cycle with ⟨_, p, hp⟩
  exact fun h ↦ h p hp

/-! ## Bipartiteness -/

def S2.color : Fin 11 → Fin 2
  | ⟨n, _⟩ => if n < 5 then 0 else 1

theorem S2_isBipartite : S2.IsBipartite := by
  refine ⟨Coloring.mk S2.color ?_⟩
  intro u v h; revert u v; decide

def S3.color : Fin 15 → Fin 2
  | ⟨n, _⟩ => if n < 6 then 0 else 1

theorem S3_isBipartite : S3.IsBipartite := by
  refine ⟨Coloring.mk S3.color ?_⟩
  intro u v h; revert u v; decide

def J0.color : Fin 21 → Fin 2
  | ⟨n, _⟩ => if n < 8 then 0 else 1

theorem J0_isBipartite : J0.IsBipartite := by
  refine ⟨Coloring.mk J0.color ?_⟩
  intro u v h; revert u v; decide

/--
Coloring of `K₀` with the second copy reversed so the bridge is bichromatic:
first-block originals color `0`, first-block subdivs color `1`;
second-block originals color `1`, second-block subdivs color `0`.
-/
def K0.color : Fin 30 → Fin 2
  | ⟨n, _⟩ =>
    if n < 15 then
      if n < 6 then (0 : Fin 2) else 1
    else if n - 15 < 6 then (1 : Fin 2) else 0

/-- Boolean properness of one undirected edge under `K0.color`. -/
def K0.edgeProper (e : Sym2 (Fin 30)) : Bool :=
  Sym2.lift ⟨fun a b : Fin 30 => decide (K0.color a ≠ K0.color b), by
    intro a b
    simp [ne_comm]⟩ e

/-- Every listed edge of `K₀` joins opposite colors. -/
theorem K0.all_edges_proper : K0.edgeList.all K0.edgeProper = true := by
  decide

theorem K0_isBipartite : K0.IsBipartite := by
  refine ⟨Coloring.mk K0.color ?_⟩
  intro u v h
  have mem : s(u, v) ∈ K0.edgeList := by
    simpa [K0, fromEdgeSet_adj] using h.left
  have hprop : K0.edgeProper s(u, v) = true :=
    (List.all_eq_true.mp K0.all_edges_proper) _ mem
  simpa [K0.edgeProper, Sym2.lift_mk, decide_eq_true_eq] using hprop

end Compactness
