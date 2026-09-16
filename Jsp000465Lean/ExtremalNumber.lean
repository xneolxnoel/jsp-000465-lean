/-
Copyright (c) 2026 Justin Sun Prize formalization effort. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Sun Prize formalization effort
-/
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Extremal numbers for finite families

Paper §1: for a family `ℱ` of graphs,
`ex(n, ℱ) := max {|E(G)| : |V(G)| = n, G is ℱ-free}`.
-/

namespace Compactness

open SimpleGraph Finset Fintype Asymptotics

set_option linter.style.header false

/-- `G` is free of every graph in the indexed family `F`. -/
def FamilyFree {ι : Type*} {W : ι → Type*} (F : ∀ i, SimpleGraph (W i)) {V : Type*}
    (G : SimpleGraph V) : Prop :=
  ∀ i, (F i).Free G

/-- Extremal number of an indexed family of forbidden graphs. -/
noncomputable def ex {ι : Type*} {W : ι → Type*} (n : ℕ) (F : ∀ i, SimpleGraph (W i)) : ℕ :=
  open scoped Classical in
  sup { G : SimpleGraph (Fin n) | FamilyFree F G } (#·.edgeFinset)

/-- Single-graph extremal number matches Mathlib when the family is a singleton. -/
theorem ex_singleton (n : ℕ) {W : Type*} (H : SimpleGraph W) :
    ex n (fun _ : Unit => H) = extremalNumber n H := by
  classical
  simp only [ex, extremalNumber, FamilyFree]
  congr 1
  ext G
  simp

/-- `ex n F` is at most `m` iff every `F`-free `n`-vertex graph has ≤ `m` edges. -/
theorem ex_le_iff {ι : Type*} {W : ι → Type*} (F : ∀ i, SimpleGraph (W i)) (n m : ℕ) :
    ex n F ≤ m ↔
      ∀ ⦃G : SimpleGraph (Fin n)⦄ [DecidableRel G.Adj], FamilyFree F G → #G.edgeFinset ≤ m := by
  classical
  simp_rw [ex, Finset.sup_le_iff, mem_filter_univ]
  exact ⟨fun h _ _ h' ↦ by convert! h _ h', fun h _ h' ↦ by convert! h h'⟩

/-- Lower bound certificate: an `F`-free graph on `n` vertices contributes its edge count. -/
theorem le_ex_of_familyFree {ι : Type*} {W : ι → Type*} {F : ∀ i, SimpleGraph (W i)}
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hFree : FamilyFree F G) : #G.edgeFinset ≤ ex n F := by
  classical
  have hmem : G ∈ ({ G : SimpleGraph (Fin n) | FamilyFree F G } : Finset _) := by
    simpa [mem_filter_univ] using hFree
  convert le_sup (f := fun G : SimpleGraph (Fin n) => #G.edgeFinset) hmem
  simp [ex]

/-- Landau Ω via Big-O reversal (Mathlib has no `IsBigOmega`). -/
def IsBigOmega {α E F : Type*} [Norm E] [Norm F] (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  g =O[l] f

@[inherit_doc IsBigOmega]
scoped notation:50 f " =Ω[" l:50 "] " g:50 => IsBigOmega l f g

end Compactness
