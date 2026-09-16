# GitHub Issue — Recommend a recipient (paste into form)

**Title:** `[Recipient] JSP-000465 formalization — RECIPIENT-JSP-000465-A`

### Related problem or entry
JSP-000465 — For a forbidden family containing a bipartite graph, can the asymptotic extremal problem be reduced to forbidding a single graph? (Erdős–Simonovits compactness, corrected form.)

### Recipient placeholder or confirmed public ID
`RECIPIENT-JSP-000465-A`  
(Use this placeholder until written confirmation; do not put an unconfirmed legal name in the issue.)

### Contributions and evidence

**Mathematical discovery / proof route (not claimed as this recipient’s original research):**
- OpenAI internal model, exposition in *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 10, Theorem 1.1 (failure of compactness), PDF: https://cdn.openai.com/pdf/ten-proofs-oai.pdf

**Formalization (this recommendation):**
- Public Lean 4 + Mathlib formalization of Theorem 1.1 at `YOUR_PUBLIC_REPO_URL`, immutable commit `0a33cdb87115672123a79deeea9546c46b97ef7b`.
- Top-level theorem: `Compactness.theorem_1_1` in `Jsp000465Lean/Theorem11.lean`.
- States existence of a finite family `F` of connected bipartite graphs each containing a cycle such that `ex(n,F)=O(n^{4/3-1/48})` while every member satisfies `ex(n,F)=Ω(n^{4/3})`.
- Toolchain: Lean `v4.34.0`; Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
- Reproduction: `lake exe get && lake build` on the pinned commit.
- Contribution roles to record after confirmation: formalization / packaging / adaptation of the Chapter 10 combinatorial core into a Mathlib-compatible Lean library; **not** first discovery of the counterexample.

If maintainers split credits: keep OpenAI (or paper authorship as published) as solver credit; `RECIPIENT-JSP-000465-A` as Lean formalization credit.

### Confirmation status
pending

### Attribution questions and conflicts
- Solver vs formalizer must stay distinct (OpenAI paper vs Lean repository contributors).
- Large module `CompactnessAndDegeneracy.lean` vendors/adapts the paper’s combinatorial development; third-party mathematical content remains attributed to the paper.
- Operator / assistant tooling used during formalization does not by itself create solver credit (per awards attribution conventions).
- Disclose any public professional relationship to OpenAI or prize curators if applicable; otherwise none.
