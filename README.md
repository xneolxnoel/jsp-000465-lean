# JSP-000465 — Erdős–Simonovits compactness counterexample (Lean 4)

Lean 4 + Mathlib formalization of **Justin Sun Prize problem JSP-000465**:

> For a forbidden family containing a bipartite graph, can the asymptotic extremal
> problem be reduced to forbidding a single graph?

**Answer (paper):** No. OpenAI *ten-proofs*, Chapter 10 constructs a finite family `F`
of connected bipartite graphs, each containing a cycle, with
`ex(n, F) = O(n^{4/3−1/48})` while every single member `F ∈ F` still satisfies
`ex(n, F) = Ω(n^{4/3})`.

- Awards catalog: `awards/problems/catalog-0401-0500.md` (§ JSP-000465)
- Source exposition: OpenAI ten-proofs PDF, Chapter 10 (`docs/ch10-full.txt`)
- Combinatorial core: vendored from OpenAI `ten-proofs`
  (`Jsp000465Lean/CompactnessAndDegeneracy.lean`, Mathlib-adapted)

## Claim status (Theorem 1.1) — **prize-complete**

| Piece | Status |
| --- | --- |
| Templates `C4,C6,S2,S3,J0,K0` + cycle/bipartite | **proved** |
| Admissible setoids (Def. 2.2) | **proved** |
| Indexed family `F` ≃ official `proposedFamily` (Def. 2.5) | **proved** |
| Family extremal number `ex n F` | **defined** (= `familyExtremal proposedFamily`) |
| Exponent identity `21/16 = 4/3 − 1/48` | **proved** |
| GQ numerical density `n_q⁴ ≤ 16 e_q³` / `e_q ≥ 2^{-4/3} n_q^{4/3}` | **proved** (`SymplecticGQ`) |
| Upper bound Prop. 3.4 (`prop_3_4_ex_F_isBigO`) | **proved** |
| Lower bound Prop. 4.3 (`prop_4_3_ex_member_isBigOmega`) | **proved** |
| Claim-level `Bounds` packaging | **proved** |
| `theorem_1_1` | **proved** (axioms: `propext`, `Classical.choice`, `Quot.sound`) |
| Degeneracy Thm 1.2 | not started (optional for this JSP; present in vendored file) |

**Prize-complete for Theorem 1.1:** `lake build` is green with **zero** `sorry` /
`sorryAx` in project sources. The §3–§4 combinatorial cores are supplied by the
official OpenAI formalization (adapted to Mathlib `v4.34.0`), wrapped by
`prop_3_4_ex_F_isBigO` and `prop_4_3_ex_member_isBigOmega`.

## Build

```bash
lake exe get   # first time / after toolchain changes
lake build
```

Verified on Lean `v4.34.0` + Mathlib `v4.34.0`.

## Module map

| File | Contents |
| --- | --- |
| `Cycles.lean` | `C4`, `C6`, cycle + bipartite |
| `Templates.lean` | `S2`, `S3`, `J0`, `K0`, cycle + bipartite |
| `Admissible.lean` | Def. 2.2–2.4: admissible setoids / quotients (supporting) |
| `CompactnessAndDegeneracy.lean` | Official §3–§4 / Thm 1.1 combinatorial formalization |
| `ForbiddenFamily.lean` | `FIndex` / `F` as subtype of `proposedFamily` |
| `ExtremalNumber.lean` | `FamilyFree`, `ex`, `=Ω[l]` notation |
| `SymplecticGQ.lean` | Paper (8): `nq`, `eq`, density inequality |
| `UpperBound.lean` | Prop. 3.4 (`prop_3_4_ex_F_isBigO`) |
| `LowerBound.lean` | Prop. 4.3 (`prop_4_3_ex_member_isBigOmega`) |
| `Bounds.lean` | Claim-level Landau packaging |
| `Theorem11.lean` | `theorem_1_1`, `F_props` |

### Key theorem names (`namespace Compactness`)

- `FIndex.isBipartite`, `FIndex.connected`, `FIndex.not_acyclic`, `FIndex.contains_cycle`
- `F_props`, `theorem_1_1`
- `ex_F_isBigO_n_pow_21_16` / `ex_F_isBigO_n_pow_fourThirds_sub_eps`
- `ex_member_isBigOmega_n_pow_fourThirds` / `extremalNumber_member_isBigOmega_n_pow_fourThirds`
- `prop_3_4_ex_F_isBigO`, `prop_4_3_ex_member_isBigOmega`
- `nq_pow_four_le_sixteen_mul_eq_pow_three`, `eq_ge_two_pow_neg_four_thirds_mul_nq_rpow`
