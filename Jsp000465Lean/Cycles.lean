/-
Copyright (c) 2026 Justin Sun Prize formalization effort. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Sun Prize formalization effort
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Even cycles C₄ and C₆

Paper definitions (ten-proofs Ch.10, Def. 2.5): the compactness family begins with
`{C₄, C₆}`. We identify these with Mathlib's `cycleGraph`.
-/

namespace Compactness

open SimpleGraph

/-- The 4-cycle as a Mathlib `cycleGraph`. -/
abbrev C4 : SimpleGraph (Fin 4) := cycleGraph 4

/-- The 6-cycle as a Mathlib `cycleGraph`. -/
abbrev C6 : SimpleGraph (Fin 6) := cycleGraph 6

/-- Explicit Hamilton cycle of `C4` (`cycleGraph.cycle 1` lives on `Fin 4`). -/
def C4.hamiltonCycle : C4.Walk 0 0 := cycleGraph.cycle 1

/-- Explicit Hamilton cycle of `C6` (`cycleGraph.cycle 3` lives on `Fin 6`). -/
def C6.hamiltonCycle : C6.Walk 0 0 := cycleGraph.cycle 3

theorem C4.hamiltonCycle_isCycle : C4.hamiltonCycle.IsCycle :=
  cycleGraph.isCycle_cycle

theorem C6.hamiltonCycle_isCycle : C6.hamiltonCycle.IsCycle :=
  cycleGraph.isCycle_cycle

/-- `C4` contains a cycle. -/
theorem C4_contains_cycle : ∃ (p : C4.Walk 0 0), p.IsCycle :=
  ⟨C4.hamiltonCycle, C4.hamiltonCycle_isCycle⟩

/-- `C6` contains a cycle. -/
theorem C6_contains_cycle : ∃ (p : C6.Walk 0 0), p.IsCycle :=
  ⟨C6.hamiltonCycle, C6.hamiltonCycle_isCycle⟩

theorem C4_not_acyclic : ¬ C4.IsAcyclic :=
  fun h ↦ h C4.hamiltonCycle C4.hamiltonCycle_isCycle

theorem C6_not_acyclic : ¬ C6.IsAcyclic :=
  fun h ↦ h C6.hamiltonCycle C6.hamiltonCycle_isCycle

/-- `C4` is bipartite (2-colorable). -/
theorem C4_isBipartite : C4.IsBipartite := by
  refine ⟨Coloring.mk (fun v : Fin 4 ↦ ⟨v.val % 2, Nat.mod_lt _ (by decide)⟩) ?_⟩
  intro u v h
  revert u v
  decide

/-- `C6` is bipartite (2-colorable). -/
theorem C6_isBipartite : C6.IsBipartite := by
  refine ⟨Coloring.mk (fun v : Fin 6 ↦ ⟨v.val % 2, Nat.mod_lt _ (by decide)⟩) ?_⟩
  intro u v h
  revert u v
  decide

end Compactness
