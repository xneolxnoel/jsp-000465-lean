# GitHub Issue — Correction (paste into form)

**Title:** `[Correction] JSP-000465 Lean proof and claim eligibility`

### Record or document
`problems/catalog-0401-0500.md` — section `JSP-000465`  
Also update the matching row in `problems/README.md` problem index.

### Current text and proposed correction

**Current (as of awards catalog clone):**
- Current status: Solved by An internal OpenAI model (counterexample for a finite family of connected bipartite graphs).
- Lean proof: No
- Eligible to claim: No
- Claim status: Unavailable

**Proposed:**
- Current status: leave the OpenAI mathematical credit unchanged (solution of the compactness counterexample).
- Lean proof: **Yes** — public repository `YOUR_PUBLIC_REPO_URL`, commit `0a33cdb87115672123a79deeea9546c46b97ef7b`, theorem `Compactness.theorem_1_1` (Lean `v4.34.0`, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
- Eligible to claim: **Yes** (Solved + Lean Yes), subject to curator verification that the formal statement matches the intended Erdős–Simonovits compactness failure (corrected form: finite family of connected bipartite cyclic graphs).
- Claim status: **Unclaimed**

Optional note under Lean proof / Public review:
> Formalization packages OpenAI *Ten Advances…* Chapter 10 (Theorem 1.1). Independent mathematical peer review of the paper and independent Lean verification by prize verifiers remain separate from this catalog update.

### Evidence and affected records
- Mathematical source: https://cdn.openai.com/pdf/ten-proofs-oai.pdf (Chapter 10, Theorem 1.1).
- Lean project: `YOUR_PUBLIC_REPO_URL` @ `0a33cdb87115672123a79deeea9546c46b97ef7b`
- Build: `lake build` succeeds; theorem axioms limited to `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`).
- Affected: JSP-000465 detail table; problems README index columns Lean / Eligible / Claim status.

### Relevant conflicts
None known for this catalog correction. Formalization contributors and OpenAI authorship are distinct; see the parallel recipient recommendation issue.
