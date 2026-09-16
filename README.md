# JSP-000465 — Erdős–Simonovits compactness (Lean packaging / Mathlib port)

> **Attribution correction (2026-09-16).** This repository is a **Mathlib port / packaging** of OpenAI’s existing Lean formalization of *Ten Advances…* Chapter 10, Theorem 1.1. The combinatorial core in `Jsp000465Lean/CompactnessAndDegeneracy.lean` is **vendored and adapted from OpenAI `ten-proofs`**. It is **not** an independent formalization contribution for Justin Sun Prize formalizer credit.
>
> Awards Recipient nomination https://github.com/TheJustinSunPrize/awards/issues/59 has been **withdrawn**. Correction https://github.com/TheJustinSunPrize/awards/issues/58 was revised so Lean Yes attribution points to OpenAI `ten-proofs`, and Eligible remains **No** for a separate packaging-based claim.

## What this repo is

Lean 4 + Mathlib packaging around Justin Sun Prize problem **JSP-000465** (corrected Erdős–Simonovits compactness failure):

> For a forbidden family containing a bipartite graph, can the asymptotic extremal
> problem be reduced to forbidding a single graph?

**Answer (paper):** No. OpenAI *ten-proofs*, Chapter 10 constructs a finite family `F`
of connected bipartite graphs, each containing a cycle, with
`ex(n, F) = O(n^{4/3−1/48})` while every single member still satisfies
`ex(n, F) = Ω(n^{4/3})`.

| Role | Attribution |
| --- | --- |
| Mathematical discovery / paper | OpenAI *Ten Advances…* Ch.10 Thm 1.1 |
| Primary Lean formalization | OpenAI `ten-proofs` (official combinatorial Lean) |
| This repository | Mathlib `v4.34.0` adaptation, wrappers, and packaging only |

- Awards catalog: `problems/catalog-0401-0500.md` (§ JSP-000465)
- Source exposition: OpenAI ten-proofs PDF (`docs/ch10-full.txt`)
- Upstream Lean core: OpenAI `ten-proofs` → vendored as `Jsp000465Lean/CompactnessAndDegeneracy.lean`

## Status (not a prize formalizer claim)

| Piece | Status |
| --- | --- |
| Templates / family / wrappers | present in this packaging |
| §3–§4 combinatorial core | **from OpenAI formalization** (vendored/adapted) |
| `theorem_1_1` packaging | builds here after Mathlib adaptation |
| Independent formalizer prize claim | **withdrawn / not asserted** |

`lake build` may succeed with no `sorry` in project sources; a green build of a vendored formalization is **not** a new formalizer claim.

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
| `CompactnessAndDegeneracy.lean` | **Vendored** OpenAI §3–§4 / Thm 1.1 combinatorial formalization |
| `ForbiddenFamily.lean` | `FIndex` / `F` as subtype of `proposedFamily` |
| `ExtremalNumber.lean` | `FamilyFree`, `ex`, `=Ω[l]` notation |
| `SymplecticGQ.lean` | Paper (8): `nq`, `eq`, density inequality |
| `UpperBound.lean` | Prop. 3.4 wrapper (`prop_3_4_ex_F_isBigO`) |
| `LowerBound.lean` | Prop. 4.3 wrapper (`prop_4_3_ex_member_isBigOmega`) |
| `Bounds.lean` | Claim-level Landau packaging |
| `Theorem11.lean` | `theorem_1_1`, `F_props` packaging |

### Key theorem names (`namespace Compactness`)

- `FIndex.isBipartite`, `FIndex.connected`, `FIndex.not_acyclic`, `FIndex.contains_cycle`
- `F_props`, `theorem_1_1`
- `ex_F_isBigO_n_pow_21_16` / `ex_F_isBigO_n_pow_fourThirds_sub_eps`
- `ex_member_isBigOmega_n_pow_fourThirds` / `extremalNumber_member_isBigOmega_n_pow_fourThirds`
- `prop_3_4_ex_F_isBigO`, `prop_4_3_ex_member_isBigOmega`
- `nq_pow_four_le_sixteen_mul_eq_pow_three`, `eq_ge_two_pow_neg_four_thirds_mul_nq_rpow`
