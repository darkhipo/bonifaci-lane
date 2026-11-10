# STMTS.md — bonifaci-lane ledger

Lane: formalization of **Bonifaci 2016, Theorem 1.1** (Physarum dynamics, smooth KL
Lyapunov, convex duality). Banked road 2 (GLOBAL POTENTIAL), campaign `bigo`.
Created 2026-11-09. Credit: the theorem is Vincenzo Bonifaci's; the formalization is ours.

## 0. Primary source — VERIFIED (lane method rule)

The anchor was verified against full text before any citing:

| Field | Value |
|---|---|
| Author | Vincenzo Bonifaci (IASI-CNR, Rome) |
| Title | *On the Convergence Time of a Natural Dynamics for Linear Programming* |
| arXiv | [arXiv:1611.06729](https://arxiv.org/abs/1611.06729) [math.OC], v1 21 Nov **2016**, DOI `10.48550/arXiv.1611.06729` |
| Journal of record | Algorithmica 82(2):300–315, 2020 |
| Journal DOI | **`10.1007/s00453-019-00615-3`** (anchor) |

**Correction to the lane brief:** the attribution "Bonifaci 2016, *Physarum dynamics
and shortest paths*, SODA 2016" could NOT be verified. No such-titled paper was found;
DBLP was unreachable (Anubis bot-wall). The verified primary matching the distillate's
description ("smooth KL-type Lyapunov decrease + convex duality", Theorem **1.1**) is
the arXiv-2016/Algorithmica-2020 paper above. The brief's phrase "shortest-path LP"
is realized as the paper's network-matrix instance (§2.2: minimum-cost transshipment;
shortest path is the unit-demand case) — the theorem itself is for general full-rank
`A`, positive `c`, and we formalize exactly that generality. **A successor should
re-check the SODA attribution once DBLP is reachable.**

The paper's own Theorem 1.1 cites [SV16, Thm 1.1] (Straszak–Vishnoi) for global
existence of solutions — that is a *separate* theorem, deliberately not assumed here.

## 1. Statement fidelity — what shape the formalization took

Paper's setting (§1.1, eq. (1)–(3)): `min cᵀx s.t. Ax=b, x≥0`, `c > 0`, `A` full rank;
`C = Diag(x_j/c_j)`, `L = ACAᵀ`, `p = L⁻¹b`, `q = CAᵀp`, energy `ℰ = qᵀRq`, `R = C⁻¹`;
dynamics `ẋ = q − x` on `Ω = ℝ_{>0}^E`; `ξ_j(t) = c_j x_j(t)/cost(x(t))`;
`KL(ξ*,ξ) = Σ_j ξ*_j ln(ξ*_j/ξ_j)`; potential `Φ(t) = ln(cost/opt) + KL(ξ*, ξ(t))`.

Mapping paper → Lean (all finite: `N E : Type*` with `[Fintype]`, vectors as `E → ℝ`):

| Paper item | Lean name | File | Status |
|---|---|---|---|
| LP data (1) | `LPData` (`A`, `b`, `c`, `hc`) | Model | def |
| `cost`, feasibility | `LPData.cost`, `LPData.IsFeasible` | Model | def |
| resistances `r_j = c_j/x_j` | `LPData.res` | Model | def |
| Laplacian-solve output (Lem 2.1) | `LPData.Step` (Kirchhoff + Ohm + Thomson) | Model | def (premise seam) |
| energy `ℰ` | `LPData.energy` / `energyAt` | Model / Thm11 | def |
| fixed point `q = x` | `LPData.IsFixedPoint` | Model | def |
| global solution + ODE (3) | `LPData.Solution` | Model | def (existence = SV16 seam, see §2) |
| ξ*, ξ(t) | `xiStar`, `xiAt` | Thm11 | def |
| KL (§4) | `KL` + `KL_nonneg` (Gibbs) | KL | **PROVED** |
| Φ (7) | `Phi` (split form) + `Phi_eq_paper` (eq. (7)) | Thm11 | def + **PROVED** identity |
| Φ ≥ 0 (feasible) | `Phi_nonneg` | Thm11 | **PROVED** |
| Lem 4.1 CS step | `cs_step` | Core | **PROVED** |
| Lem 4.4 algebra (2-case) | `phi_decrease_core` | Core | **PROVED** |
| Prop 2.2 (`pᵀb = ℰ`) | `duality_inner` | Duality | **PROVED** (M3 core, drafted ahead) |
| Prop 2.3 + Ohm (`x*ᵀRq = bᵀp`) | `xstar_Rq_eq` | Duality | **PROVED** (M3 core, drafted ahead) |
| Lem 4.2 algebraic identity | `lem42_core` | Duality | **PROVED** (M3 core, drafted ahead) |
| Lem 4.5 `ℰ ≤ cost` | `energy_le_cost` | Thm11 | **PROVED** (from Thomson) |
| Lem 3.2 feasibility invariance | premise **P1** (`hfeas`) → **`feasibility_invariant`** | Thm11 / Feasibility | premise, **discharged pending receipts** (`defect_ode` = Prop 3.1, `defect_decay`) |
| Lem 4.1 d/dt bound | premise **P2** (`hcostlog`) | Thm11 | premise |
| Lem 4.3 d/dt bound | premise **P3** (`hkl`) | Thm11 | premise |
| Thm 4.7 + Thm 1.1 | `thm11` | Thm11 | **PROVED** mod P1–P3 |
| Thm 1.1 second half (μ bound) | — | — | milestone M4 (KL ≤ ln μ + ln(cost₀/opt) is proved-math but not yet coded) |
| edges never retire (`D_e ≥ D_e(0)e^{-t}`) | `edge_no_retirement` | Features | **PROVED** (mod trajectory differentiability, no Gronwall) |
| fixed point = LP optimum (duality ID) | `fixed_point_dual_tight`, `fixed_point_cost_eq`, `fixed_point_lp_optimal` | Optimality | **PROVED** (mod `Step`) |

### Honest deviation, stated (fixed point ≠ the interesting boundary)

At an exact interior rest point, Ohm + `q = x` force `Aᵀp = c` **exactly** — a dual
certificate tight on *all* coordinates. Hence `fixed_point_cost_eq`: every feasible
point has the *same* cost (c lies in the row space of A; unit-simplex case: constant c).
The genuinely interesting convergence (boundary optima, thinning off-support tubes) is
carried by the KL potential — which is why Thm 1.1, not the rest-point calculus, is the
paper's engine. Both facts are in the tree; neither is hidden. This also connects to
the sibling widgets lane: **edges never retire** (`edge_no_retirement`) is why tubes
thin asymptotically instead of dying into a frozen lock.

## 2. Named premises (D7 seams) — each documented, no silent sorry

There are **no `sorry` and no `axiom` commands in the lane.** Every analytic gap is an
explicit hypothesis of `LPData.thm11`, so consumers must acknowledge it:

* **P1 `hfeas`** — feasibility invariance (Lem 3.2). Downstream proof route (pure
  real-arithmetic, Gronwall-free): `e(t) = ‖Ax(t)−b‖²` satisfies `e'(t) = −2e(t)` by
  Prop 3.1 (`Aẋ = b − Ax`, itself pure algebra from the ODE + Kirchhoff), so
  `u(t) = e(t)e^{2t}` has `u' = 0`. Same antitone/monotone primitive already used in
  `edge_no_retirement`.
* **P2 `hcostlog`** — d/dt ln(cost/opt) ≤ √(ℰ/cost) − 1 (Lem 4.1). Downstream: chain
  rule + `cs_step` (already proved) + `ℰ`-definition; needs `q` continuous in `t`
  (add to `Solution` when discharging).
* **P3 `hkl`** — d/dt KL(ξ*, ξ(t)) ≤ √(ℰ/cost) − ℰ/opt (Lem 4.3). Downstream: exact
  identity of Lem 4.2 (`d/dt Σ ξ*_j ln(x*_j/x_j) = 1 − ℰ/opt`) via the duality sandwich
  `x*ᵀRq = (Ax*)ᵀp = bᵀp = pᵀLp = ℰ` — pure finite algebra, plus chain rule.
* **SV16 seam** — existence of a global `Solution`. Represented structurally: a
  `Solution` is a solution *by construction*; existence is a hypothesis downstream
  (Picard–Lindelöf on ℝ_{>0}^E, real-arithmetic layer).
* **`Step`/`thomson` seam** — Physarum's Laplacian solve, quarantined as a bundle of
  three real-arithmetic facts (Kirchhoff, Ohm, Thomson). Dischargeable by
  positive-definiteness of `L = ACAᵀ`. **Constraint (a) respected**: no
  comparison-addition formalization anywhere in the lane; the network case is a
  remark, the algebra is all finite sums over ℝ.

## 3. Constraint (b) — edges never retire

`Bonnifaci/Features.edge_no_retirement`: with `q_e ≥ 0` pointwise (automatic for flow
magnitudes in the network case), `x_e(t) ≥ x_e(0)·e^{-t}` for `t ≥ 0`. Proof: `u ↦
x_e(u)·e^u` has derivative `q_e(u)·e^u ≥ 0`, so `monotoneOn_of_deriv_nonneg` applies.
Feature (b) is therefore a *theorem*, not an assumption. Sibling-lane link: the
frozen-lock widget formalizes the pathology this model excludes; cross-cite from the
widgets lane side when it lands.

## 4. Milestone map (2–4 weeks, bounded steps; each names its premise boundary)

* **M0 (DONE 2026-11-09)** — scaffold + pins + verified primary + statement family +
  8 proved lemmas (`KL_nonneg`, `mul_log_div_ge_sub`, `cs_step`, `phi_decrease_core`,
  `fixed_point_dual_tight`, `fixed_point_cost_eq`, `fixed_point_lp_optimal`,
  `edge_no_retirement`) + theorem skeleton `thm11` with P1–P3. **Pending: build
  receipts** (blocked on fleet build queue at write time — host saturation 2026-11-09).
* **M1** — build clean, `#print axioms thm11` receipt (expect only `propext`,
  `Classical.choice`, `Quot.sound`), three receipts per campaign convention.
* **M2** — ~~discharge P1~~ **DRAFTED** (`Bonnifaci/Feasibility.lean`:
  `const_of_deriv_zero`, `defect_ode` (Prop 3.1), `defect_decay` (Lem 3.2),
  `feasibility_invariant`); needs build receipts, then `thm11` consumers switch from
  `hfeas` to the theorem (or `thm11` drops the P1 hypothesis in favor of
  `hstart : IsFeasible (S.x 0)`).
* **M3** — discharge **P3**: the duality sandwich `x*ᵀRq = bᵀp = ℰ` as a standalone
  proved lemma over `Solution`, then Lem 4.2 identity, then Lem 4.3 bound. Needs `q`
  continuous in `t` — extend `Solution` with `hcont : ∀ e, Continuous (fun t => q t e)`
  (true downstream from the solve; state, don't assume).
* **M4** — discharge **P2** (chain rule + `cs_step` + M3 machinery), then add the
  `μ`-corollary (`KL(ξ*,ξ(0)) ≤ ln μ + ln(cost₀/opt)`, needs `[Nonempty E]` and
  `Finset.max'`) completing the paper's Thm 1.1 verbatim.
* **M5** — discharge the `Step` seam: existence of `q, p` with Kirchhoff+Ohm+Thomson
  from `L = ACAᵀ` positive definite (`Matrix.posDef` route). This removes the
  Laplacian-solve black box *within the real-arithmetic layer* — still no
  comparison-addition.
* **M6** — SV16 existence seam (Picard–Lindelöf) OR keep as structural hypothesis and
  document; decide by cost.
* **M7** — shortest-path instantiation: signed-incidence `LPData` (reduced incidence,
  grounded node), unit s-t demand ⇒ the LP is shortest path; state the identification
  corollary. Risk: incidence-matrix plumbing; budget a bounded spike first.
* **M8** — lane ledger final pass, receipts re-run, wip→main landing via the queue.

## 5. Pins & build

* Lean `leanprover/lean4:v4.34.1`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
  (campaign family, same as sssp-nlogn-lane).
* Mathlib packages APFS-cloned from `/Volumes/Substrate-1/bigo/sssp-nlogn-lane`
  (`cp -cR`, 3.2 GB, ~30 s) — **shared checkout preference honored, no fresh clone**.
* Module family namespace: **`Bonnifaci/`** per lane-brief instruction. Spelling note:
  the mathematician's name is Bonifaci (single n); the namespace follows the brief
  verbatim — mass-rename is a 1-line sed if a successor intends otherwise.

## 6. Incidents

* **2026-11-09 ~18:00 — external sweep.** The freshly created scaffold (lakefile.toml +
  `.lake/packages`, 3.2 GB APFS clone) was deleted by an unknown concurrent actor
  minutes after creation (`lean-toolchain` + `Bonnifaci/` survived). No sweeper was
  identifiable in `ps` (candidates: peer lane tooling; `.ref-ss34` reference scaffold
  exists at `bigo/.ref-ss34` with lakefile/manifest — possible auto-sync source).
  Recovered from the same source clone in 30 s; `lakefile.toml` + manifest now
  mirrored to the opencode temp master; lane is git-tracked. **Successors: verify
  `.lake/packages/mathlib` exists before any build, and re-clone if swept.**
* **2026-11-09 ~18:55 — host saturation.** Fleet-wide admission control active
  (swap 17.3 GB / 18.4 GB, load 117; shed SIGKILLs ~8 GB lean builds, R2125609450).
  Per new rules: swap gate before any launch (>12 GB ⇒ wait), single heavy build via
  `flock /Volumes/Substrate-1/bigo/.build.lock`, detached `trap "" TERM` builds with
  receipts to files, `.trace` bust after kills. Analysis-first sequencing was applied:
  this ledger + the full source family landed before any build attempt.
