/-
Copyright (c) 2026 Justin Sun Prize formalization effort. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Sun Prize formalization effort
-/
import Jsp000465Lean.Bounds

/-!
# Theorem 1.1 — Failure of compactness

Paper statement: there exists a finite nonempty family `F` of connected bipartite
graphs, each containing a cycle, such that for `ε = 1/48`,
`ex(n, F) = O(n^{4/3−ε})` while `ex(n, F) = Ω(n^{4/3})` for every `F ∈ F`.

The family `F` and its structural properties are fully formalized. Claim-level
Landau packaging and the combinatorial cores (`prop_3_4_ex_F_isBigO`,
`prop_4_3_ex_member_isBigOmega`) are complete — Theorem 1.1 is prize-complete.
-/

namespace Compactness

open SimpleGraph Asymptotics Filter

set_option linter.style.header false

/-- Bundled structural hypotheses of Theorem 1.1 on the family `F`. -/
structure CompactnessFamilyProps where
  nonempty : Nonempty FIndex
  bipartite : ∀ i : FIndex, (F i).IsBipartite
  connected : ∀ i : FIndex, (F i).Connected
  hasCycle : ∀ i : FIndex, ¬ (F i).IsAcyclic

/-- The concrete family `F` satisfies the structural side of Theorem 1.1. -/
theorem F_props : CompactnessFamilyProps where
  nonempty := F_nonempty
  bipartite := FIndex.isBipartite
  connected := FIndex.connected
  hasCycle := FIndex.not_acyclic

/--
**Theorem 1.1 (Failure of compactness).**

Assembled from the fully proved family properties and the proved asymptotic
bounds in `Bounds` / `UpperBound` / `LowerBound`.
-/
theorem theorem_1_1 :
    CompactnessFamilyProps ∧
      ((fun n : ℕ => (ex n F : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3 - compactnessEps))) ∧
      (∀ i : FIndex,
        (fun n : ℕ => (extremalNumber n (F i) : ℝ)) =Ω[atTop]
          (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3))) :=
  ⟨F_props, ex_F_isBigO_n_pow_fourThirds_sub_eps,
    extremalNumber_member_isBigOmega_n_pow_fourThirds⟩

/-- Compactness (1) fails for every member: the family upper bound is `o` of each
individual lower-order `n^{4/3}` growth. -/
theorem compactness_fails_for_members :
    (∀ _i : FIndex,
      (fun n : ℕ => (ex n F : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3 - compactnessEps))) ∧
    (∀ i : FIndex,
      (fun n : ℕ => (extremalNumber n (F i) : ℝ)) =Ω[atTop]
        (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3))) :=
  ⟨fun _i => ex_F_isBigO_n_pow_fourThirds_sub_eps,
    extremalNumber_member_isBigOmega_n_pow_fourThirds⟩

end Compactness
