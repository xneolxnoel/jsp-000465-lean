/-
Copyright (c) 2026 Justin Sun Prize formalization effort. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Sun Prize formalization effort
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Jsp000465Lean.ExtremalNumber
import Jsp000465Lean.ForbiddenFamily
import Jsp000465Lean.SymplecticGQ

/-!
# Lower bound (paper §4 / Proposition 4.3)

For every member `F ∈ F`, `ex(n, F) = Ω(n^{4/3})`, via incidence graphs of
symplectic generalized quadrangles `W(q)`. The combinatorial freeness /
padding argument is supplied by `CompactnessAndDegeneracy.lean`; density (8)
is also available in `SymplecticGQ.lean`.
-/

namespace Compactness

open SimpleGraph Asymptotics Filter Real CompactnessConjecture

set_option linter.style.header false

/-- Field size `2^{j+1}` (even characteristic witnesses). -/
def evenPrimePower (j : ℕ) : ℕ := 2 ^ (j + 1)

/-- Field size `3^{j+1}` (odd characteristic witnesses). -/
def oddPrimePower (j : ℕ) : ℕ := 3 ^ (j + 1)

lemma evenPrimePower_ge_one (j : ℕ) : 1 ≤ evenPrimePower j :=
  Nat.one_le_pow _ _ (by decide)

lemma oddPrimePower_ge_one (j : ℕ) : 1 ≤ oddPrimePower j :=
  Nat.one_le_pow _ _ (by decide)

/-- Density along the even tower: `eq (2^{j+1}) ≥ 2^{-4/3} nq(2^{j+1})^{4/3}`. -/
theorem eq_ge_nq_rpow_along_even (j : ℕ) :
    (2 : ℝ) ^ (-(4 : ℝ) / 3) * (nq (evenPrimePower j) : ℝ) ^ ((4 : ℝ) / 3) ≤
      (eq (evenPrimePower j) : ℝ) :=
  eq_ge_two_pow_neg_four_thirds_mul_nq_rpow _ (evenPrimePower_ge_one j)

/-- Density along the odd tower. -/
theorem eq_ge_nq_rpow_along_odd (j : ℕ) :
    (2 : ℝ) ^ (-(4 : ℝ) / 3) * (nq (oddPrimePower j) : ℝ) ^ ((4 : ℝ) / 3) ≤
      (eq (oddPrimePower j) : ℝ) :=
  eq_ge_two_pow_neg_four_thirds_mul_nq_rpow _ (oddPrimePower_ge_one j)

private lemma rpow_le_of_mul_const_le
    {c x y : ℝ} (hc : 0 < c) (h : c * x ≤ y) : x ≤ c⁻¹ * y := by
  have h' := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hc.le)
  rwa [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at h'

/-- Landau `Ω` form of the official uniform member lower bound. -/
theorem isBigOmega_of_uniformMemberLower (i : FIndex) :
    (fun n : ℕ => (extremalNumber n i.1.graph : ℝ)) =Ω[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3)) := by
  change (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3)) =O[atTop]
    (fun n : ℕ => (extremalNumber n i.1.graph : ℝ))
  refine (isBigO_iff).2 ⟨manuscriptLowerConstant⁻¹, ?_⟩
  have hpos : 0 < manuscriptLowerConstant := manuscriptLowerConstant_pos
  filter_upwards [proposedFamily_uniformMemberLower i.1 i.2] with n hn
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hext : (0 : ℝ) ≤ (extremalNumber n i.1.graph : ℝ) := by
    exact_mod_cast (Nat.zero_le _)
  have hn' : manuscriptLowerConstant * ((n : ℝ) ^ ((4 : ℝ) / 3)) ≤
      (extremalNumber n i.1.graph : ℝ) := by
    simpa [extremalScale] using hn
  have hle := rpow_le_of_mul_const_le hpos hn'
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnnonneg _),
    abs_of_nonneg hext] using hle

/--
**Proposition 4.3.** For every `F ∈ F`, `ex(n, F) = Ω(n^{4/3})`.
-/
theorem prop_4_3_ex_member_isBigOmega (i : FIndex) :
    (fun n : ℕ => (ex n (fun _ : Unit => F i) : ℝ)) =Ω[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3)) := by
  have h := isBigOmega_of_uniformMemberLower i
  dsimp [IsBigOmega] at h ⊢
  -- Goal: (n ↦ n^{4/3}) =O (n ↦ ex n {F i})
  -- Have: (n ↦ n^{4/3}) =O (n ↦ extremalNumber n i.graph)
  convert h with n
  rw [ex_singleton]
  -- Now: extremalNumber n (F i) = extremalNumber n i.1.graph
  rfl

end Compactness
