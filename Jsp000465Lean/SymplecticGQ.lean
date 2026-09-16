/-
Copyright (c) 2026 Justin Sun Prize formalization effort. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Sun Prize formalization effort
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Numerical counts for the symplectic GQ `W(q)` (paper §4, display (8))

`nq = 2(q+1)(q²+1)` and `eq = (q+1)²(q²+1)` are the order and size of the incidence
graph `Iq`. The inequality `n_q⁴ ≤ 16 e_q³` (hence `e_q ≥ 2^{-4/3} n_q^{4/3}`) is
proved here.
-/

namespace Compactness

set_option linter.style.header false

/-- Paper (8): `n_q = 2(q+1)(q²+1)`. -/
def nq (q : ℕ) : ℕ := 2 * (q + 1) * (q ^ 2 + 1)

/-- Paper (8): `e_q = (q+1)²(q²+1)`. -/
def eq (q : ℕ) : ℕ := (q + 1) ^ 2 * (q ^ 2 + 1)

lemma nq_pos {q : ℕ} (_hq : 1 ≤ q) : 0 < nq q := by
  dsimp [nq]
  positivity

lemma eq_pos {q : ℕ} (_hq : 1 ≤ q) : 0 < eq q := by
  dsimp [eq]
  positivity

lemma qsq_add_one_le_sq_succ (q : ℕ) : q ^ 2 + 1 ≤ (q + 1) ^ 2 := by
  calc
    q ^ 2 + 1 ≤ q ^ 2 + 2 * q + 1 := by lia
    _ = (q + 1) ^ 2 := by ring

/-- Integer form of paper (8): `n_q⁴ ≤ 16 e_q³`. -/
theorem nq_pow_four_le_sixteen_mul_eq_pow_three (q : ℕ) :
    nq q ^ 4 ≤ 16 * eq q ^ 3 := by
  set a := q + 1
  set b := q ^ 2 + 1
  have hba : b ≤ a ^ 2 := qsq_add_one_le_sq_succ q
  have hn : nq q = 2 * a * b := rfl
  have he : eq q = a ^ 2 * b := rfl
  have hstep : a ^ 4 * b ^ 4 ≤ a ^ 6 * b ^ 3 := by
    calc
      a ^ 4 * b ^ 4 = (a ^ 4 * b ^ 3) * b := by ring
      _ ≤ (a ^ 4 * b ^ 3) * a ^ 2 := Nat.mul_le_mul_left _ hba
      _ = a ^ 6 * b ^ 3 := by ring
  calc
    nq q ^ 4 = (2 * a * b) ^ 4 := by rw [hn]
    _ = 16 * (a ^ 4 * b ^ 4) := by ring
    _ ≤ 16 * (a ^ 6 * b ^ 3) := Nat.mul_le_mul_left _ hstep
    _ = 16 * (a ^ 2 * b) ^ 3 := by ring
    _ = 16 * eq q ^ 3 := by rw [he]

/-- From `n⁴ ≤ 16 e³` deduce `n^{4/3} ≤ 2^{4/3} e` (`q ≥ 1`). -/
theorem nq_rpow_fourThirds_le_two_rpow_mul_eq (q : ℕ) (hq : 1 ≤ q) :
    (nq q : ℝ) ^ ((4 : ℝ) / 3) ≤ (2 : ℝ) ^ ((4 : ℝ) / 3) * (eq q : ℝ) := by
  have hn_pos : (0 : ℝ) < nq q := by exact_mod_cast nq_pos hq
  have he_pos : (0 : ℝ) < eq q := by exact_mod_cast eq_pos hq
  have hR : (nq q : ℝ) ^ (4 : ℕ) ≤ 16 * (eq q : ℝ) ^ (3 : ℕ) := by
    exact_mod_cast nq_pow_four_le_sixteen_mul_eq_pow_three q
  have hpow :=
    Real.rpow_le_rpow (by positivity) hR (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have lhs : ((nq q : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 3) = (nq q : ℝ) ^ ((4 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hn_pos)]
    ring_nf
  have rhs : (16 * (eq q : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) =
      (2 : ℝ) ^ ((4 : ℝ) / 3) * (eq q : ℝ) := by
    have h16 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
    rw [← Real.rpow_natCast, Real.mul_rpow (by positivity) (by positivity), h16,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul (le_of_lt he_pos)]
    ring_nf
    simp [Real.rpow_one]
  rwa [lhs, rhs] at hpow

/-- Paper (8): `2^{-4/3} n_q^{4/3} ≤ e_q` for `q ≥ 1`. -/
theorem eq_ge_two_pow_neg_four_thirds_mul_nq_rpow (q : ℕ) (hq : 1 ≤ q) :
    (2 : ℝ) ^ (-(4 : ℝ) / 3) * (nq q : ℝ) ^ ((4 : ℝ) / 3) ≤ (eq q : ℝ) := by
  have h := nq_rpow_fourThirds_le_two_rpow_mul_eq q hq
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hnonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-(4 : ℝ) / 3) :=
    Real.rpow_nonneg (le_of_lt h2pos) _
  have hmul := mul_le_mul_of_nonneg_left h hnonneg
  have simplify_right :
      (2 : ℝ) ^ (-(4 : ℝ) / 3) * ((2 : ℝ) ^ ((4 : ℝ) / 3) * (eq q : ℝ)) = (eq q : ℝ) := by
    rw [← mul_assoc, ← Real.rpow_add h2pos]
    norm_num
  rwa [simplify_right] at hmul

end Compactness
