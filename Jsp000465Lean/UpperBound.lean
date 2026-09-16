/-
Copyright (c) 2026 Justin Sun Prize formalization effort. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Sun Prize formalization effort
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Jsp000465Lean.ExtremalNumber
import Jsp000465Lean.ForbiddenFamily

/-!
# Upper bound (paper §3 / Proposition 3.4)

`ex(n, F) = O(n^{21/16})`, via the official combinatorial formalization in
`CompactnessAndDegeneracy.lean` (Lemmas 3.1–3.3 + Prop. 3.4 counting).
-/

namespace Compactness

open SimpleGraph Asymptotics Filter Real CompactnessConjecture

set_option linter.style.header false

/--
**Proposition 3.4.** For the family `F` of Definition 2.5,
`ex(n, F) = O(n^{21/16}) = O(n^{4/3 − 1/48})`.
-/
theorem prop_3_4_ex_F_isBigO :
    (fun n : ℕ => (ex n F : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((21 : ℝ) / 16)) := by
  simpa [ex_eq_familyExtremal] using proposedFamily_familyExtremal_isBigO

end Compactness
