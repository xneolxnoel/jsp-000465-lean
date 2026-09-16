/-
Copyright (c) 2026 Justin Sun Prize formalization effort. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Sun Prize formalization effort
-/
import Jsp000465Lean.CompactnessAndDegeneracy
import Jsp000465Lean.Cycles
import Jsp000465Lean.Templates
import Jsp000465Lean.ExtremalNumber

/-!
# Forbidden family `F` (paper Def. 2.5)

We index the manuscript family by the official encoding
`CompactnessConjecture.proposedFamily` from OpenAI *ten-proofs*
(`CompactnessAndDegeneracy.lean`): `{C₄, C₆} ∪ J ∪ K`. Structural
properties and the asymptotic cores are taken from that formalization.
-/

namespace Compactness

open SimpleGraph CompactnessConjecture

set_option linter.style.header false
set_option linter.unusedDecidableInType false

/-! ## Index type for the family -/

/-- Indices for members of `F`: elements of the official `proposedFamily`. -/
abbrev FIndex := { g : FiniteGraph // g ∈ proposedFamily }

/-- Vertex type of the member indexed by `i`. -/
def FIndex.Vertex (i : FIndex) : Type := Fin i.1.order

/-- The forbidden graph at index `i`. -/
def FIndex.graph (i : FIndex) : SimpleGraph i.Vertex := i.1.graph

/-- The compactness family as an indexed collection (paper (4)). -/
abbrev F := FIndex.graph

/-! ## Slice-1 generators (kept for continuity with template modules) -/

inductive F0Member
  | c4 | c6 | j0 | k0
  deriving DecidableEq, Repr

def F0 : List F0Member := [.c4, .c6, .j0, .k0]

theorem F0_nodup : F0.Nodup := by decide
theorem F0_length : F0.length = 4 := by decide

theorem F0Member.contains_cycle :
    (∃ (p : C4.Walk 0 0), p.IsCycle) ∧
    (∃ (p : C6.Walk 0 0), p.IsCycle) ∧
    (∃ (v : Fin 21) (p : J0.Walk v v), p.IsCycle) ∧
    (∃ (v : Fin 30) (p : K0.Walk v v), p.IsCycle) :=
  ⟨C4_contains_cycle, C6_contains_cycle, J0_contains_cycle, K0_contains_cycle⟩

theorem F0Member.not_acyclic :
    ¬ C4.IsAcyclic ∧ ¬ C6.IsAcyclic ∧ ¬ J0.IsAcyclic ∧ ¬ K0.IsAcyclic :=
  ⟨C4_not_acyclic, C6_not_acyclic, J0_not_acyclic, K0_not_acyclic⟩

theorem F0Member.isBipartite :
    C4.IsBipartite ∧ C6.IsBipartite ∧ J0.IsBipartite ∧ K0.IsBipartite :=
  ⟨C4_isBipartite, C6_isBipartite, J0_isBipartite, K0_isBipartite⟩

/-! ## Structural properties of every member of `F` -/

theorem FIndex.isBipartite (i : FIndex) : (F i).IsBipartite :=
  proposedFamily_member_isBipartite i.2

theorem FIndex.not_acyclic (i : FIndex) : ¬ (F i).IsAcyclic :=
  proposedFamily_isCyclic i.1 i.2

theorem FIndex.connected (i : FIndex) : (F i).Connected :=
  proposedFamily_member_connected i.2

theorem FIndex.contains_cycle (i : FIndex) :
    ∃ (v : i.Vertex) (p : (F i).Walk v v), p.IsCycle := by
  have h := FIndex.not_acyclic i
  simp [SimpleGraph.IsAcyclic, not_forall, Classical.not_not] at h
  exact h

theorem F_nonempty : Nonempty FIndex :=
  ⟨⟨finiteCycle 4, four_cycle_mem_proposedFamily⟩⟩

/-- Witness: the 4-cycle member. -/
def FIndex.c4 : FIndex := ⟨finiteCycle 4, four_cycle_mem_proposedFamily⟩

/-- Witness: the 6-cycle member. -/
def FIndex.c6 : FIndex := ⟨finiteCycle 6, six_cycle_mem_proposedFamily⟩

theorem F_contains_C4 : F FIndex.c4 = C4 := rfl

theorem F_contains_C6 : F FIndex.c6 = C6 := rfl

/-! ## Extremal identification with the official family encoding -/

/-- Indexed freeness matches the official `Finset` freeness. -/
theorem familyFree_F_iff_proposedFamily {n : ℕ} (G : SimpleGraph (Fin n)) :
    FamilyFree (ι := FIndex) (W := FIndex.Vertex) F G ↔
      CompactnessConjecture.FamilyFree proposedFamily G := by
  constructor
  · intro h forbidden hmem
    exact h ⟨forbidden, hmem⟩
  · intro h i
    exact h i.1 i.2

/-- Family extremal numbers agree. -/
theorem ex_eq_familyExtremal (n : ℕ) :
    ex n F = familyExtremal proposedFamily n := by
  classical
  simp only [ex, familyExtremal, familyFree_F_iff_proposedFamily]

end Compactness
