# JSP-000465 submission checklist

Do these in order before opening GitHub issues on `TheJustinSunPrize/awards`.

1. **Publish the Lean repo**
   - Create a **public** GitHub repository.
   - Push this project (`master` commit below).
   - Replace every `YOUR_PUBLIC_REPO_URL` in the drafts with that HTTPS URL.
   - Prefer pinning the commit SHA (immutable), not a floating branch tip.

2. **Reproduce locally (attach log summary)**
   ```bash
   git clone YOUR_PUBLIC_REPO_URL
   cd <repo>
   git checkout 0a33cdb87115672123a79deeea9546c46b97ef7b   # or the SHA you pin
   lake exe get
   lake build
   ```
   Archive the build log externally (or gist); keep SHA-256 + byte size for the verification record.

3. **Open two issues** on https://github.com/TheJustinSunPrize/awards/issues/new/choose
   - **Correction** — update problem-bank Lean / eligibility fields (paste `01-ISSUE-correction.md`).
   - **Recommend a recipient** — formalization credit with placeholder (paste `02-ISSUE-recommend-recipient.md`).

4. **Optional PR** into `candidates/observation/<entry-id>/` using files under `candidate-draft/` once maintainers invite a PR (or open after issues).

5. **Do not** put private email, payment info, or unconfirmed real names in public issues/commits. Use `RECIPIENT-JSP-000465-A` until written confirmation.

## Pinned local commit (before push)

- Commit: `0a33cdb87115672123a79deeea9546c46b97ef7b`
- Lean: `v4.34.0`
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`
- Top theorem: `Compactness.theorem_1_1`
