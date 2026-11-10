# bonifaci-lane

Formalization of **Bonifaci 2016, Theorem 1.1** — the Physarum dynamics for linear
programming, with the KL-type Lyapunov potential and the convex-duality
identification. Campaign banked road 2 (GLOBAL POTENTIAL).

* **Ledger (read this first):** [STMTS.md](STMTS.md) — verified primary source,
  statement-fidelity table, named-premise seams, milestone map M0–M8, incidents.
* **Pins:** Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
  (campaign family).
* **Anchor DOI:** `10.1007/s00453-019-00615-3` (Algorithmica 82(2):300–315, 2020;
  arXiv:1611.06729, 2016).

## Module family (`Bonnifaci/` — namespace per lane brief)

| File | Contents |
|---|---|
| `Bonnifaci/Model.lean` | `LPData`, `Step` (quarantined Laplacian-solve seam), `Solution` (ODE trajectory) |
| `Bonnifaci/KL.lean` | finite KL + Gibbs (`KL_nonneg`) |
| `Bonnifaci/Core.lean` | `cs_step` (Lem 4.1 CS core), `phi_decrease_core` (Lem 4.4 two-case core) |
| `Bonnifaci/Optimality.lean` | fixed point ⇒ dual tightness ⇒ LP optimality |
| `Bonnifaci/Features.lean` | `edge_no_retirement` (constraint (b) as a theorem) |
| `Bonnifaci/Thm11.lean` | **WIP** — proof-carrying `thm11` (statement kept in sync by `Theorem.lean`) |
| `Bonnifaci/Theorem.lean` | `thm11_statement` — Thm 1.1 as a machine-checked Prop, premises P1–P3 named |

No `sorry`, no axioms; analytic gaps are named hypotheses of `thm11` (P1–P3, each with
a documented downstream discharge route in STMTS.md §2).

## Build

Standard `lake build Bonnifaci` against the shared campaign Mathlib (packages are an
APFS clone of `sssp-nlogn-lane`'s build; re-clone if swept — see STMTS.md §6).

Build discipline on this host: swap gate (`vm.swapusage` > 12 GB ⇒ wait),
`flock /Volumes/Substrate-1/bigo/.build.lock`, detached `trap "" TERM` launches,
receipts to `receipts/`.

## Credit

Theorem: Vincenzo Bonifaci (2016/2020). Formalization: this lane, 2026-11-09.
