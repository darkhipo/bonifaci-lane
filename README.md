# Bonifaci Thm 1.1 — Lean 4 formalization

**What this is.** A kernel-checked Lean 4 formalization of **Bonifaci's Theorem 1.1** — the convergence-time bound for the natural Physarum-type dynamics for linear programming (*On the Convergence Time of a Natural Dynamics for Linear Programming*, Algorithmica **82**(2):300–315, 2020; arXiv:1611.06729) — plus the μ-bound corollary, the Laplacian-solve (`Step`) discharge, the flow-Lipschitz estimate, the shortest-path instantiation, and the connectivity ⇔ full-row-rank bridge. 18 modules; `lake build Bonnifaci` builds everything in one command; **every declaration checks under exactly `[propext, Classical.choice, Quot.sound]`**; zero `sorry`, zero `axiom` commands (the only `sorry` strings in the tree are prose in docstrings). Build pin: Mathlib `d13f23b7`, Lean v4.34.1.

**State, honestly.** Complete on this pin except one named seam: `LPData.HasSolution` — the global *two-sided* ODE existence the paper cites as [SV16, Thm 1.1]. The local-Lipschitz half of the existence hypothesis is proved here (`FlowLipschitzOnOrthant`, `RhsLipschitzOnOrthant`); Picard–Lindelöf yields only local forward existence, so the gap is stated, not glossed. The `W/μ` constant is explicit, not tight.

**Why it is up.** An unpublished proof is indistinguishable from a claim. This is a re-runnable, reusable, machine-checked anchor for the paper's theorem — the mathematics is Bonifaci's; the formalization exists to be checked, not believed.

**What work can be done here.** (1) `LPData.HasSolution` — discharge SV16 (global/two-sided), or the documented-structural route; (2) tighten the `W/μ` Lipschitz constant; (3) the ODE-library route to (1) — measured on this pin at a 6,616-module unbuilt closure (`receipts/closure_cost.py` kept; note its constant offset of 2 in this tree). Successors: do **not** re-derive the rank bridge, grounding necessity, or the triangle cycle witness — they are landed and receipted (`STMTS.md` §9).

**License.** Released under the [Copy-Free/Stays-Free (CFSF) License](https://github.com/darkhipo/cfsf) — see `LICENSE`. Copy-free: use it for any purpose. Stays-free: nobody gets to fence it.

**Attribution.** Theorem 1.1, the dynamics, the potential, and the shortest-path instance are **Vincenzo Bonifaci's** (the paper above). Construction details follow the paper's own lemmas (4.1–4.4, Prop 3.1, Lemma 3.2, Thm 4.7). The formalization is ours. Statements were verified against the full paper text, not the abstract.
