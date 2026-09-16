/-
Copyright (c) 2026 Justin Sun Prize formalization effort. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Sun Prize formalization effort
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Jsp000465Lean.ExtremalNumber
import Jsp000465Lean.ForbiddenFamily
import Jsp000465Lean.UpperBound
import Jsp000465Lean.LowerBound

/-!
# Extremal bounds for Theorem 1.1 (paper §3–§4)

Claim-level Landau packaging for Theorem 1.1. The combinatorial cores are the
proved propositions `prop_3_4_ex_F_isBigO` and `prop_4_3_ex_member_isBigOmega`.
-/

namespace Compactness

open SimpleGraph Asymptotics Filter Real

set_option linter.style.header false

/-- Exponent appearing in Theorem 1.1. -/
noncomputable def compactnessEps : ℝ := 1 / 48

/-- Paper’s intermediate exponent `21/16`. -/
noncomputable def compactnessUpperExp : ℝ := 21 / 16

theorem compactnessUpperExp_eq :
    compactnessUpperExp = (4 : ℝ) / 3 - compactnessEps := by
  simp [compactnessUpperExp, compactnessEps]
  norm_num

/-! ## Upper bound (paper Prop. 3.4 / §3) -/

/-- `ex(n, F) = O(n^{21/16})` — claim-level form of Prop. 3.4. -/
theorem ex_F_isBigO_n_pow_21_16 :
    (fun n : ℕ => (ex n F : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ compactnessUpperExp) := by
  convert prop_3_4_ex_F_isBigO using 1
  simp [compactnessUpperExp]

/-- Corollary form with exponent `4/3 − 1/48`. -/
theorem ex_F_isBigO_n_pow_fourThirds_sub_eps :
    (fun n : ℕ => (ex n F : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3 - compactnessEps)) := by
  convert ex_F_isBigO_n_pow_21_16 using 1
  funext n
  rw [compactnessUpperExp_eq]

/-! ## Lower bounds (paper Prop. 4.3 / §4) -/

/-- For every member `F ∈ F`, `ex(n, F) = Ω(n^{4/3})` — claim-level form of Prop. 4.3. -/
theorem ex_member_isBigOmega_n_pow_fourThirds (i : FIndex) :
    (fun n : ℕ => (ex n (fun _ : Unit => F i) : ℝ)) =Ω[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3)) :=
  prop_4_3_ex_member_isBigOmega i

/-- Convenience: Mathlib single-graph form. -/
theorem extremalNumber_member_isBigOmega_n_pow_fourThirds (i : FIndex) :
    (fun n : ℕ => (extremalNumber n (F i) : ℝ)) =Ω[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3)) := by
  simpa [ex_singleton] using ex_member_isBigOmega_n_pow_fourThirds i

end Compactness
