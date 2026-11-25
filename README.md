# Machine-Checked Exact-Rational Sign-Vector Flags, Quasipolyhedral Non-Attainment, Frame Slices, and Acyclic Chamber DAG Certificates for Hyperplane Arrangements

**Author:** Lluis Eriksson (prepared with transparent AI assistance via Google Antigravity)
**Target Reference:** Brennan Dury, *Traversing hyperplane arrangements with an affine objective*, `arXiv:2611.32976` (November 24, 2026).
**Licenses:** Manuscript (`paper/main.tex`, `paper/main.pdf`) under `CC-BY-4.0`; code, Lean 4 proofs, and exact certificates under `MIT`.

## Highlights
- **Zero-Dependency Lean 4 Kernel (`lean/HyperplaneTraversal.lean`, Lean 4.35.0):** 18 constructive theorems, `0` `sorry`, `0` warnings, `0` `Classical.choice`, `0` `Lean.ofReduceBool` (5 zero-axiom `none`, 1 `[propext]`, 12 `[propext, Quot.sound]`).
- **Pure-Stdlib Zero-Float Verifier (`ARRANGEMENT-TRAVERSAL-CERT-1.0`, `src/arrangement_certifier.py`):** Four exact-$\mathbb{Q}$ modes auditing Proposition 1 & Theorem 2's $2^r - 1$ sign-vector flag targets, Section 2 Figure 2's quasipolyhedral non-attainment counterexample, Section 6 Lemma 17 & Proposition 3's Frame-strategy slice updates and strict lexicographic potential, and complete acyclic chamber DAGs with exact KKT primal/dual LP optimality and Theorem 3 uniform escape length $L$.
- **Canonical Atlas & Adversarial Audit:** 16/16 canonical certificates replayed in `0.110–1.003 ms` and **66/66 live adversarial forgery attacks rejected**.

## Quick Reproduction
```bash
# 1. Build & audit Lean 4 kernel
cd lean && lake build && lake env lean AuditAxioms.lean && cd ..

# 2. Run deterministic end-to-end verification (Lean + 16 certs + 66/66 attacks + SHA-256 manifest)
python scripts/verify_all.py

# Optional: regenerate certificates, wall-clock benchmark JSONs, and figures
python scripts/run_all_experiments.py
python scripts/make_figures.py
```
