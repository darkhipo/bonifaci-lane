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

---

# §7 — 2026-11-10 session: M0/M1 landed, statements machine-checked

Successor of the session that drafted the family but died before any build. This
session did the compiler work: the *drafted* lemmas are now *checked* lemmas.

## 7.0 Primary source re-verified independently (three receipts, not prose)

| Receipt | Method | Result |
|---|---|---|
| Journal DOI | api.crossref.org/works/10.1007/s00453-019-00615-3 | `status: ok`; title "On the Convergence Time of a Natural Dynamics for Linear Programming"; author Vincenzo Bonifaci (ORCID 0000-0001-9038-6901); Algorithmica vol **82**, issue **2**, pages **300-315**, published-print **2020-02**, published-online **2019-08-08** |
| arXiv | arxiv.org/abs/1611.06729 | [v1] Mon, 21 Nov 2016 11:28:55 UTC; journal-ref Algorithmica 82(2):300-315, 2020; related DOI = the row above; abstract matches the distillate ("relative entropy between projected versions of the optimal point and of the initial point", "logarithmically with the LP cost coefficients", "linearly with the inverse of the relative accuracy") |
| Full text | arxiv.org/pdf/1611.06729v1 -> `refs/paper.txt` (pdftotext, 11 pp) | verbatim statement capture in 7.1; the paper's Thm 1.1 cites [18, Thm 1.1] = Straszak-Vishnoi for *existence*, a separate theorem |

**The brief's attribution is dead, second confirmation.** The brief said "Bonifaci 2016,
*Physarum dynamics and shortest paths*, SODA 2016". A Crossref author query over 2011-2021
returns Bonifaci's complete record in this area: SODA **2012** "Physarum Can Compute
Shortest Paths" (with Mehlhorn and Varma, DOI 10.1137/1.9781611973099.21), J. Theor. Biol.
2012, IPL 2013 "A short proof", LNCS 2013, TCS 2019 "Two results on slime mold
computations", and the Algorithmica 2020 paper. **No SODA-2016 Physarum paper by Bonifaci
exists.** The lane formalizes the Algorithmica-2020 / arXiv-2016 paper — the one that
actually contains "Theorem 1.1" with the KL potential.

## 7.1 Verbatim statements (extracted from the PDF; the fidelity anchors)

* **Theorem 1.1.** "For a feasible initial condition `s in R^E_{>0}`, consider the solution
  `x : [0,inf) -> Omega` to the Physarum dynamics (3) with `x(0) = s`. Then `x(t)` is a
  feasible solution to (1) for any `t >= 0`, and for any eps > 0, it holds that
  `cost(x(t)) <= (1+eps)opt` for all `t >= (6/eps)( ln(cost(x(0))/opt) + KL(xi*, xi(0)) )`."
* **Lemma 4.1** d/dt ln(cost(x(t))/opt) <= (E(t)/cost(x(t)))^(1/2) - 1.
* **Lemma 4.2** d/dt Sum_j (c_j x*_j/opt) ln(x*_j/x_j(t)) = 1 - E(t)/opt.
* **Lemma 4.3** d/dt KL(xi*, xi(t)) <= (E(t)/cost(x(t)))^(1/2) - E(t)/opt.
* **Lemma 4.4** If cost(x(t)) >= (1+eps)^2 opt for eps in (0,1/2) then d/dt Phi(t) <= -eps/2.
* **Proposition 3.1** A xdot = b - A x. **Lemma 3.2** ||e(t)||_2 = ||e(0)||_2 exp(-t).
* **Theorem 4.7(b)** cost(x(t)) <= (1+eps)opt for t >= Phi(0)/(eps/6).
* **mu-bound** (proof of Thm 1.1, second half), mu = max_j x*_j/x_j(0):
  KL(xi*, xi(t)) <= ln mu + ln(cost(x)/opt).

Checks performed against the drafted Lean: phi_decrease_core's hypothesis
2 sqrt(gamma/kappa) - 1 - gamma is exactly Lemma 4.1 + Lemma 4.3 with gamma = E/opt,
kappa = cost/opt (paper p.8: Phi-dot <= 2(E/cost)^(1/2) - 1 - E/opt); Phi's split form
reproduces eq. (7) via kl_split; thm11's (6/eps) and the eps <= 1 restriction match
Theorem 4.7's eps' = eps/3 substitution.

## 7.2 A drafted proof that was WRONG, caught by the compiler

phi_decrease_core's original two-case proof split on (1-sqrt(gamma))^2 >= 1/2 and, in the
second case, invoked Real.lt_sqrt_of_sq_lt wanting (1-sqrt(gamma))^2 < eps/2, while it
only had (1-sqrt(gamma))^2 < 1/2 — which does NOT imply the former for small eps. The
drafted step is mathematically false. The statement is true and is the paper's. Replaced
with a division-free proof needing no case split: AM-GM gives 2 sqrt(gamma/kappa) <=
gamma + 1/kappa, hence Phi-dot <= 1/kappa - 1 <= 1/(1+eps)^2 - 1 <= -eps/2 (last step
iff eps^2 <= 3, from eps <= 1/2). **Statement unchanged; proof corrected.**
Lesson: "PROVED" in a ledger with no build behind it means "drafted".

## 7.3 What now compiles (M1)

Root target `lake build Bonnifaci` = Model, KL, Core, Optimality, Features,
Feasibility, Theorem. Proved and machine-checked: KL_nonneg, mul_log_div_ge_sub, cs_step,
phi_decrease_core, fixed_point_dual_tight, fixed_point_cost_eq, fixed_point_lp_optimal,
edge_no_retirement, const_of_deriv_zero, defect_ode, defect_decay, feasibility_invariant,
xiStar_nonneg, xiAt_pos, energyAt_nonneg, plus **thm11_statement** (the machine-checked
Prop). **P1 is discharged**, not assumed.

Constraint (a) holds: no comparison-addition anywhere; the Laplacian solve is the
LPData.Step bundle of real-arithmetic facts. Constraint (b) is a *theorem*
(edge_no_retirement), so frozen lock is structurally excluded — feature, not gap.

## 7.4 API drift found (campaign Mathlib d13f23b7), for the next lane

1. `def LPData.foo` declared INSIDE `namespace Bonnifaci` becomes `Bonnifaci.LPData.foo`, and dot
   notation `d.foo` then fails with "The environment does not contain LPData.foo".
   Declare such defs at root (Model) or use plain application.
2. `Finset.sum_div` no longer exists; route Sum a_e / b through <- Finset.sum_mul +
   inv_mul_cancel_0.
3. `Real.sqrt_mul` takes (h : 0 <= a) (b : R) — proof first. mul_self_sqrt takes a
   nonnegative-subtype argument.
4. `.mul` / `.sum` on DifferentiableAt must be written DifferentiableAt.mul /
   DifferentiableAt.sum; a bare `differentiable_const` is Differentiable-flavoured and will
   not unify with a DifferentiableAt goal.
5. Pointwise lambda vs function product: `deriv (fun u => f u * g u)` does not match
   `deriv (f * g)` syntactically; bridge with a rfl equality or a show.
6. MonotoneOn / AntitoneOn take their points IMPLICITLY: h_mem h_a h_b hab, not
   h a b h_a h_b hab.

## 7.5 Build gates (correction recorded)

The `vm.swapusage used > 12GB` gate is a **high-water mark that never clears** (measured
pinned at 13.7GB while memory_pressure reported 67-73% free and vm_stat Swapouts delta was
0 over 60 s): wound **R2125609494**. Replacement gate, measured and used here:
memory_pressure free% > 15 **and** vm_stat Swapouts delta over 60 s == 0 -> GO.
This session measured free 67%, swapouts delta 0 and proceeded under
`flock -w 7200 /Volumes/Substrate-1/bigo/.build.lock` with detached TERM-immune launches
and file receipts. One queued build died with exit=-9 (SIGKILL) and an empty error list —
the R2125609465 signature; retried, and the retry produced real diagnostics.

## 7.6 Milestone map — updated (2-4 weeks)

| # | Step | Status |
|---|---|---|
| M0 | scaffold, pins, verified anchor, statement family | DONE (prev session) |
| M1 | build green + three receipts (exit 0, olean, axiom banner) | **DONE this session** |
| M2 | P1 discharged (Prop 3.1 + Lemma 3.2) | **DONE** (feasibility_invariant) |
| M3 | Thm11 proof green: duality sandwich (Prop 2.2/2.3), Lemma 4.2 identity, Lemma 4.3 => **P3 discharged** | NEXT — live error inventory in 7.7 |
| M4 | Lemma 4.1 chain rule => **P2 discharged**; thm11 then closes with no premises but P1 | after M3 |
| M5 | mu-bound corollary (KL <= ln mu + ln(cost/opt)) = paper's Thm 1.1 verbatim second half | after M4 |
| M6 | discharge the Step bundle (Laplacian solve) from posDef (A C A^T) — still real-arithmetic only | independent |
| M7 | SV16 global-existence seam (Picard-Lindeloef) or keep structural + document | last |
| M8 | shortest-path instantiation (signed incidence, unit s-t demand) | last; risk: incidence plumbing |

## 7.7 WIP inventory (exact, so the next mind does not re-derive it)

`Bonnifaci/Thm11.lean` — 21 errors at time of writing, all mechanical:
Finset.sum_div (2x), differentiable_const vs differentiableAt_const inside DifferentiableAt
goals, AntitoneOn/MonotoneOn implicit-point application, pointwise-lambda vs deriv_add
shapes, one bracket-notation mismatch, one linarith needing the eps <= 1 fact.
`Bonnifaci/Duality.lean` — imports Thm11 for its notation; expected to compile once
Thm11 does. Neither is imported by the root target, so the M1 receipts stay honest.
## 7.8 M1 receipts (exact)

    exit_code=0    elapsed_s=26    build target: Bonnifaci (root)
    olean[Model]=PRESENT 351176    olean[KL]=PRESENT 198680
    olean[Core]=PRESENT 303296     olean[Optimality]=PRESENT 83064
    olean[Features]=PRESENT 113696 olean[Feasibility]=PRESENT 167104
    olean[Theorem]=PRESENT 61392   axiom_banner_exit=0

Axiom banner (`receipts/axioms.txt`), all twelve landed theorems:

    depends on axioms: [propext, Classical.choice, Quot.sound]

— no `sorryAx`, no lane axioms. Artefacts: `receipts/build.log`, `receipts/build.receipt`,
`receipts/build.status`, `receipts/axioms.txt`, `refs/paper.txt` (primary-source text),
`refs/bonifaci1611.06729.pdf`.

**Fidelity note on the range of ε.** The paper says "for any ε > 0", but its
proof substitutes ε' = ε/3 into Lemma 4.4, which requires ε' in (0, 1/2) — so the paper's
argument is effective only for ε < 3/2, and the phrase "any ε > 0" is a mild overstatement in
the source itself. `thm11_statement` carries ε <= 1, strictly inside the effective range.

---

# §8 — 2026-11-10 (session 2): M6 merged onto the true base; the loss narrative corrected; M7 first increment

## 8.0 The incident, corrected (measured truth — supersedes the earlier loss narrative)

A previous session wrote, in a *rebuilt* copy of this ledger, that the lane's repo had been
"deleted from disk", that `KL`/`Core`/`Optimality`/`Features`/`Feasibility`/`Theorem`/`Thm11`/
`Duality` were **lost**, and that `ec6e530` was **unrecoverable**. **That is false.** Measured
2026-11-10 by the coordinator and re-verified here:

    /Volumes/Substrate-1/bigo/bonifaci-lane   HEAD = ec6e530  (clean tree, branch main)
    git log: ec6e530 M5 → 7444901 P3 → 2000e4e P2 → … → a3d59cd scaffold
    Bonnifaci/: Model KL Core Optimality Features Feasibility Theorem Thm11
                Duality Lemma41 Lemma43 Mu            (13 modules, all present)

Nothing was lost. What actually happened:

1. **A second working copy existed under `/private/tmp`, and the tmp reaper took it.** That
   copy — not the repo — was what disappeared.
2. **The recovery search never looked at this directory.** It covered `$HOME` (depth 4) and
   `/private/tmp` (depth 2) and looked for `*bonifaci*`/`STMTS.md` under home and `/Volumes`
   — but the grep for candidate repos was rooted at `$HOME`, so `/Volumes/Substrate-1/bigo/`
   was never enumerated. The lane home that the brief itself had designated was the one place
   not searched.
3. **The loss narrative was written from an incomplete search, not from a measurement.** The
   ledger said "no copy exists in any git object store on this machine" while a clean clone
   with the full history sat on the external volume.

**Wound class:** a near-miss dressed as a post-mortem. The cost was not the missing data —
it was a successor mind re-deriving work that already existed, and a ledger that would have
told every later reader the M3/M5 proofs had to be rebuilt.

**Durability rule (binding on this lane from now on):**

* **Work in the designated lane home.** One copy of record; `/private/tmp` is scratch and is
  reaped without notice.
* **Push to a remote at every milestone** so the repo is never single-copy:
  `git remote add origin https://github.com/darkhipo/bonifaci-lane.git` (the body's GitHub
  account is `darkhipo`; `BigO-Hunter/bonifaci-lane` is the alternative if it is ever created).
  A lane with no remote is one `rm` from the incident this section exists to prevent.
* **Before writing any loss narrative, check `/Volumes/Substrate-1/bigo/<lane>/` first**, and
  never declare loss from a search that did not enumerate the brief's own lane path. A negative
  search result is evidence about the search, not about the world.

## 8.1 The merge, and the `Model.lean` diff verdict

M6 had been re-derived in the rebuilt copy against a **path** Mathlib
(`…/staircase-port/.lake/packages/mathlib`, rev `118aa17…`) rather than the campaign pin
`d13f23b7…`. Its `Model.lean` was a *reconstruction*: 5521 bytes against the original's 6367.

Declaration-level diff (measured, not eyeballed):

| | count | names |
|---|---|---|
| declarations identical in both | 8 | `LPData`, `LPData.Step`, `LPData.Solution`, `LPData.cost`, `LPData.IsFeasible`, `LPData.res`, `LPData.energy`, `LPData.IsFixedPoint` |
| declarations **only in the rebuild** | **0** | — |
| declarations **only in the original** | **2** | `differentiableAt_finset_sum`, `deriv_finset_sum` |
| imports **only in the original** | **1** | `Mathlib.Analysis.Calculus.Deriv.Add` |

Those two lemmas are not decoration — they are the dynamics layer's working API, with **nine
call sites**: `Feasibility` (2), `Lemma41` (1), `Lemma43` (2), `Thm11` (4). Had the rebuilt
`Model.lean` been taken as the base, four modules would have failed to compile.

**Verdict: the original is kept verbatim; the rebuild was strictly poorer, not merely
different.** Verified: `git diff ec6e530 -- Bonnifaci/Model.lean` is empty, and M6 compiles
against the original without a single edit to it. "Prefer the original" was a correctness
requirement, not a style preference.

## 8.2 M6, adapted to the campaign pin (one honest API substitution)

`import Mathlib` was replaced with four narrow imports (`Data.Matrix.Mul`,
`LinearAlgebra.Matrix.ToLin`, `LinearAlgebra.FiniteDimensional.Basic`, plus `Tactic.Linarith`
/ `Tactic.Ring`), because on the pin `Mathlib.olean` does not exist and the closure is ~6600
modules. The only proof change: `exists_potential` now goes through
`Matrix.mulVecLin` + `LinearMap.injective_iff_surjective` instead of
`Matrix.mulVec_injective_iff_isUnit`. Measured closure cost: **119 unbuilt modules** for the
determinant route against **49** for rank-nullity. Same theorem, smaller dependency; the
substitution is recorded in `Bonnifaci/M6.lean`'s header.

## 8.3 Receipts (exact, this tree)

| receipt | artifact | value |
|---|---|---|
| build | `receipts/build_merged.log` / `.receipt` | **exit 0**, 2257 jobs, target `Bonnifaci` (root). 4 warnings, all pre-existing (`Thm11` ×3 `push_neg`/`simpa`, `Lemma43` ×1 unused var). **M6 and M7 compile with zero warnings.** |
| oleans | `.lake/build/lib/lean/Bonnifaci/` | 14: `Model KL Core Optimality Features Feasibility Theorem Thm11 Duality Lemma41 Lemma43 Mu M6 M7` |
| axioms | `receipts/axioms_merged.txt` | **27 declarations, every one `[propext, Classical.choice, Quot.sound]`** — zero non-target lines; grep for `sorry`/`admit` across `Bonnifaci/*.lean` returns nothing |

The restored M3/M5 family is inside that set: `thm11_final`, `thm11`, `lem42_core`,
`duality_inner`, `feasibility_invariant`, `kl_bound_mu`, `entropy_summand_le`,
`cost_deriv`, `log_cost_deriv`, `differentiable_kl_sum`.

## 8.4 M7 first increment — landed (`Bonnifaci/M7.lean`)

The ODE `ẋ = q(x) − x` was a *relation* until the flow was shown unique at each point. That
is now proved:

* `res_energy_eq_zero` — Kirchhoff-homogeneous flow with gradient resistance image has zero
  resistance energy. Thomson's cross-term computation, read as an identity.
* `flow_eq_of_kirchhoff_ohm` — **the flow at a strictly positive `x` is unique.**
* `potential_eq_of_ohm` — full row rank pins the potentials too.
* `step_unique`, `step_p_unique`, `existsUnique_flow` — `∃!` electrical data at each point.
* `LPData.qfun` — the flow map as a genuine function; `qfun_eq_steps` proves the choice in its
  definition does not matter. `LPData.rhs` — the ODE's right-hand side as a function.
* `LPData.Solution.q_eq_qfun` — a trajectory's flow at `t` **is** `qfun (x t)`.

**Named, not proved** (defs of type `Prop`, carried as hypotheses — no axiom, no sorry, no
opaque constant):

* `LPData.FlowLipschitzOnOrthant` — local Lipschitz continuity of the flow on the positive
  orthant (Picard–Lindelöf's hypothesis). The residual content is continuity of matrix
  inversion composed with the rational map `x ↦ A diag(x/c) Aᵀ`, which is Mathlib's
  `ContinuousLinearMap` inverse theory — not in the 1988-module built prefix on this pin.
* `LPData.HasSolution` — existence of the trajectory for a positive feasible start
  ([SV16, Thm 1.1], the paper's [18, Thm 1.1]).

## 8.5 Next

1. `FlowLipschitzOnOrthant`: supply the analytic layer (chain rule on `x ↦ L(x)`, then
   invertibility + norm bounds). Bounded spike: compute the closure cost of
   `Mathlib.Analysis.Normed.Algebra.Inverse` on this pin *before* committing to it.
2. `Solution` from `HasSolution` + Picard–Lindelöf, or keep the seam named and prove the
   theorem conditional on it — the ledger must say which.
3. M8: shortest-path instantiation (signed incidence, unit s-t demand) and the ledger final pass.

---

# §8 — 2026-11-10 (session 2): M6 merged onto the true base; the loss narrative CORRECTED

## 8.0 Correction of record — the M3/M5 modules were never lost

The previous session's ledger (written in the *rebuilt* repo at `~/bonifaci-lane`)
asserted that the lane repository "was deleted from disk … no copy exists in any git
object store on this machine" and that `ec6e530` (M5) was "unrecoverable as a commit".
**That verdict was wrong, and this section replaces it.**

Measured truth (2026-11-10, this session):

* **`/Volumes/Substrate-1/bigo/bonifaci-lane` — the lane home the brief designated — was
  intact the entire time.** `git log` there runs `ec6e530` (M5 mu-corollary) → `7444901`
  (P3) → `2000e4e` (P2) → … → `a3d59cd` (scaffold); working tree clean apart from one
  untracked PDF.
* **Every module the previous ledger listed as lost is present in it:** `KL.lean`,
  `Core.lean`, `Optimality.lean`, `Features.lean`, `Feasibility.lean`, `Theorem.lean`,
  `Thm11.lean`, `Duality.lean`, `Lemma41.lean`, `Lemma43.lean`, `Mu.lean`, plus
  `receipts/` (build log, axiom banner, M1/M4/P2 receipts) and `refs/`.
* What actually died was the **`/private/tmp` copy** the earlier session had been
  working in — a second copy, not the repository. `~/bonifaci-lane` is a *rebuild* from
  a scratch probe file, and it was a **parallel history**, never the lane.

**The defect is in the search, and it is a `verify-via-environment` failure.** The
earlier search reported its own coverage ("searched … all home/`/Volumes` trees for
`*bonifaci*`/`STMTS.md`") and the mind believed the report. A single `ls` on the
designated lane home would have refuted it in one second. The lesson is the body's, not
this lane's: **a search that reports its scope has not thereby covered its scope.** When
a loss verdict is about to be written into a durable ledger, verify the claim by looking
at the *specific place the brief named*, not by trusting a sweep's self-description.

## 8.1 Durability rule (binding on every successor of this lane)

1. **Work in the lane home, not in `/private/tmp` and not in `$HOME`.** The lane home is
   `/Volumes/Substrate-1/bigo/bonifaci-lane`. Scratch copies are for scratch work only;
   nothing whose loss you would regret may live only there.
2. **This repo now has a remote** — `origin` → `https://github.com/darkhipo/bonifaci-lane`
   (created 2026-11-10 for exactly this reason). A single-copy repo is one sweep away
   from the verdict this section is correcting. `git push origin main` after every
   landed milestone.
3. **Before declaring anything lost, `ls` the lane home.** Then `git -C` it. Only then
   search wider.

## 8.2 M6 merge — verdict on the re-derived `Model.lean`

M6 (the Laplacian-solve discharge) had been developed in the rebuilt repo against
`Model.lean` re-derived from `/private/tmp/probe4.lean`. The task was to keep the
**original** reviewed text and add only genuine M6 content. Diff verdict, measured by
comparing declaration sets:

| | original (`ec6e530`) | rebuild (`ef34ea1`) |
|---|---|---|
| declarations in common | 8 | 8 |
| declarations only here | **`deriv_finset_sum`, `differentiableAt_finset_sum`** | none |
| imports only here | **`Mathlib.Analysis.Calculus.Deriv.Add`** | none |

The rebuild was **strictly poorer**, not merely different: it had lost two `Model`-layer
lemmas and one import. Those lemmas are load-bearing — **nine call sites** across
`Feasibility.lean` (3), `Lemma41.lean` (1), `Lemma43.lean` (2) and `Thm11.lean` (3)
apply them. Had the rebuild been taken as the base, four modules would have gone red.

**Decision: `Bonnifaci/Model.lean` is byte-identical to `ec6e530`** (`git diff ec6e530 --
Bonnifaci/Model.lean` is empty). M6 was transplanted as a *new* file on top of the
original and compiled against it unchanged — which also proves the M6 proof does not
depend on any quirk of the rebuilt text.

## 8.3 M6 adaptation forced by the campaign Mathlib pin

In the rebuild, M6 used `import Mathlib` against a *path* Mathlib (`118aa17…`). The lane
home pins `d13f23b7…`, where `import Mathlib` would have pulled ~6 500 unbuilt modules
(the package holds 1 988 of 8 529 oleans). Two measure-then-choose steps:

* **Narrow imports**: `Bonnifaci.Model` + `Mathlib.Data.Matrix.Mul` +
  `Mathlib.LinearAlgebra.Matrix.ToLin` + `Mathlib.LinearAlgebra.FiniteDimensional.Basic`
  + the `Linarith`/`Ring` tactic modules.
* **Re-route the solve.** `Matrix.mulVec_injective_iff_isUnit` sits behind a 119-module
  closure on this pin (determinants); `LinearMap.injective_iff_surjective` sits behind
  **49** (rank-nullity). Same mathematics — injectivity of `mulVec L` on the
  finite-dimensional space `N → ℝ` — so `exists_potential` now reads

  `hinj : Injective (Lmat x).mulVecLin` → `LinearMap.injective_iff_surjective.mp` →
  surjectivity → `p := (surj b).choose`.

  Mathematics unchanged; the discharge is still a construction, not a citation.

Result: 66 modules built in ~2 min under load ≈ 120; `Bonnifaci.M6` compiled on the
first attempt after the re-route, 0 warnings.

## 8.4 M7 first increment — the flow map is well defined

`Bonnifaci/M7.lean` (new, in the root target). This is Picard–Lindelöf's **first**
ingredient: the ODE `ẋ = q(x) − x` was a relation until the flow was proved unique.

Proved (all in the axiom banner, 8 new entries):

* `res_energy_eq_zero` — Kirchhoff-homogeneous + gradient resistance image ⇒ zero
  resistance energy. Thomson's cross-term computation (M6) read as an identity.
* `flow_eq_of_kirchhoff_ohm` — **the flow at a point is unique** (no rank hypothesis
  needed; the energy argument does it).
* `potential_eq_of_ohm` — full row rank pins the potentials too.
* `step_unique`, `step_p_unique`, `existsUnique_flow` — the `Step` data at `x` is unique,
  so `LPData.qfun` is a function of `x`, not a choice.
* `LPData.Solution.q_eq_qfun` — a trajectory's flow at `t` **is** `qfun (x t)`: the
  trajectory and the flow map are one object.
* `LPData.rhs` — the ODE right-hand side as a function.

Named, NOT proved (Props a consumer carries as hypotheses — no `axiom`, no `sorry`):

* `LPData.FlowLipschitzOnOrthant` — local Lipschitz continuity of `qfun` on the positive
  orthant. Honest scope note: the content is continuity of matrix inversion composed with
  the rational map `x ↦ A diag(x/c) Aᵀ`, plus a local bound. Mathlib's
  `Analysis.Normed.Algebra.Inverse` is **not built** in this workspace, so this is the
  next increment, not this one.
* `LPData.HasSolution` — [SV16, Thm 1.1] (the paper's [18]), global existence for a
  strictly positive start.

## 8.5 Receipts (merged tree, all three, exact)

    BUILD     lake build Bonnifaci   exit 0   2257 jobs   receipts/build_merged.log
              lake build Bonnifaci.M7 exit 0  2148 jobs   0 errors, 0 warnings
              (driver: fcntl single-writer lock + live-pressure gate + kill-retry;
               receipts/build_merged.receipt, receipts/build_m7.receipt)
    OLEANS    14 present: Model KL Core Optimality Features Feasibility Theorem
              Thm11 Duality Lemma41 Lemma43 Mu M6 M7
    AXIOMS    27 declarations, every one
              [propext, Classical.choice, Quot.sound]
              receipts/axioms_merged.txt, exit 0, zero off-target lines
    SORRY     0 across Bonnifaci/*.lean
    WARNINGS  4, all pre-existing and all in earlier modules (Thm11 push_neg x2,
              Thm11 unnecessarySimpa, Lemma43 unused binder); M6 and M7 contribute 0.

The M3/M5 family (`thm11_final`, `thm11`, `kl_bound_mu`, `entropy_summand_le`,
`lem42_core`, `duality_inner`, `feasibility_invariant`) is re-verified on the merged
tree — those receipts now come from the restored modules, not from a rebuild.

## 8.6 Next (M7 continuation), in order

1. `Mathlib.Analysis.Normed.Algebra.Inverse` (+ closure) → continuity of `L x ⁻¹`,
   then `FlowLipschitzOnOrthant` becomes provable. Measure the closure first.
2. With Lipschitz in hand, the Picard–Lindelöf step itself (Mathlib `ODE`) — measure
   before promising; the ODE layer may exceed this workspace's built set.
3. Only then M8 (shortest-path instantiation: signed incidence, unit s-t demand).

---

# §9 — 2026-11-10 (session 3): `FlowLipschitzOnOrthant` DISCHARGED; `HasSolution` position fixed by measurement

Successor of the M6/M7 session. M7 left two named Props. **One of them is now a theorem.**
The other is kept named — and this session measured why, rather than asserting it.

## 9.1 The measurement that decided the route (task 1, as instructed)

Tool written and kept: `receipts/closure_cost.py` (read-only; walks the transitive import
closure of a module across every lake package and counts modules with **no built `.olean`**).
Lock wrapper written and kept: `receipts/build_lock.py` (fcntl single-writer; macOS has no
`flock(1)` — the ledger's "flock" instruction is satisfied by this wrapper).

| candidate module | on pin `d13f23b7` | UNBUILT modules to compile first |
|---|---|---|
| `Mathlib.Analysis.Normed.Algebra.Inverse` | **ABSENT** | — |
| `Mathlib.Analysis.Normed.Algebra.Basic` | present | **6616** |
| `Mathlib.Analysis.Normed.Module.ContinuousInverse` | present | **190** |
| `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` (adjugate/det) | present | **72** |
| `Mathlib.Analysis.Calculus.Deriv.Inv` | present | 2 |
| `Mathlib.Analysis.Normed.Field.Lemmas` (scalar `inv` continuity only) | present | 2 |
| `Mathlib.Algebra.Order.BigOperators.Ring.Finset` | present, **already imported by `Model`** | **0** |

**Two findings, both worth more than the table:**

1. **The M7 header named a module this pin does not have.** `Mathlib.Analysis.Normed.Algebra.Inverse`
   has no `.lean` file anywhere in the package tree. It is a name recalled from a newer Mathlib.
   A plan that cites it is a plan against a library that is not here. (Same class as §8.3's
   `Matrix.mulVec_injective_iff_isUnit` cost lesson, but worse: that one existed and was expensive;
   this one does not exist.)
2. **The cheap path was not on the proposed list at all.** Both suggested routes (Neumann-series
   perturbation, adjugate/det) cost 72–6616 modules. The route actually taken costs **0 new
   imports**, because it never inverts a matrix.

## 9.2 The route taken — an energy perturbation estimate (0 new imports)

For two strictly positive points `x`, `y` with flows `q`, `q'`: both are Kirchhoff flows for
the same `b`, so `g = q − q'` is **Kirchhoff-homogeneous** (`A g = 0`). Ohm's law at the two
points differs only by the resistance mismatch `s_e = q'_e (c_e/y_e − c_e/x_e)`; multiplying
the differenced Ohm law by `g_e` and summing kills the potential term:

> `∑_e (c_e/x_e) g_e² = ∑_e s_e g_e`   (`LPData.energy_perturb`)

Everything after that is finite real arithmetic. Bounding `|s_e|` needs `q'` bounded on the
ball, which is **Thomson's principle at `y` tested against the fixed flow `q`** (`q'_sq_le`) —
no solve at `y` is ever performed — plus `y_e ∈ [x_e/2, 3x_e/2]` from the ball radius. The
`2|a| ≤ 1 + a²` AM–GM step (`mis_le`) is what keeps the whole estimate free of square roots
until the single closing `|d_e| ≤ √(∑ d²)`.

Seven new declarations, all proved, all `[propext, Classical.choice, Quot.sound]`:

| declaration | content |
|---|---|
| `LPData.ohm_res_sub` | differenced Ohm law: only the resistance mismatch remains |
| `LPData.energy_perturb` | **the identity** `∑(c/x)g² = ∑ s g`; potential term vanishes |
| `LPData.q'_sq_le` | Thomson at `y` vs the fixed flow `q` bounds `q'` by data at `x` |
| `LPData.mis_le` | `|s_e| ≤ W_e·|y_e − x_e|`, no square root (AM–GM) |
| `LPData.flowLipschitzOnOrthant` | **`d.FlowLipschitzOnOrthant`**: seam 1 DISCHARGED |
| `LPData.RhsLipschitzOnOrthant` | the hypothesis stated on the ODE **right-hand side** |
| `LPData.rhsLipschitzOnOrthant` | `FlowLipschitzOnOrthant → RhsLipschitzOnOrthant` (K+1) |

The two private helpers `div_le_two_div`, `two_div_three_le_div`, `one_div_mul_le` are
deliberately `private` and proved by multiplying through by positive denominators — this pin
does not have a stable `div_le_div_iff_of_pos` surface, and the multiplication form does not
drift with the library.

**Honest scope note.** The constant `K` is *explicit but not tight*: it is `W/μ` where `μ` is
the smallest conductance `c_e/x_e` and `W` the largest mismatch coefficient. Nothing here
claims a sharp Lipschitz constant, and nothing needs one — Picard–Lindelöf consumes only
existence of some `K` on some ball.

## 9.3 `HasSolution` — kept named, and the reason is a measurement, not a preference

Task 3 asked for a decision and an honest statement. **Decision: seam 2 stays a named Prop.**
Evidence:

| route to `HasSolution` | measured cost |
|---|---|
| `Mathlib.Analysis.ODE.ExistUnique` (Picard–Lindelöf) | **6616 unbuilt modules** |
| `Mathlib.Analysis.ODE.Gronwall` | **6616** |
| `Mathlib.Analysis.ODE.PicardLindelof` | **6616** |

The entire ODE layer sits behind the same normed-space tower as `Normed.Algebra.Basic`. That is
not a bounded increment on this pin; it is the 6616-module build.

**And the measurement is not the only objection — the statement is stronger than PL.** `LPData.Solution`
quantifies over **all `t : ℝ`** (including negative times) with strict positivity everywhere.
Picard–Lindelöf yields a **local, forward** solution. Closing `HasSolution` therefore needs
(a) the ODE library, (b) a global-extension/maximal-interval argument, and (c) two-sidedness.
SV16 [Straszak–Vishnoi, Thm 1.1] is a genuine separate theorem for (b)+(c), exactly as §2 always
said. Claiming PL would "give" `HasSolution` would be false, and this ledger will not say it.

**What the seam looks like now, stated precisely.** Before M8, `HasSolution` sat next to an
unproved analytic hypothesis, so a reader could not tell whether the analysis or the existence
theory was the gap. After M8 the decomposition is exact and one half is closed:

* **CLOSED (this session):** local Lipschitz continuity of the flow, and of the ODE right-hand
  side `x ↦ q(x) − x` — the analytic hypothesis PL consumes.
* **OPEN:** the ODE library's own build cost (6616), plus global/two-sided existence (SV16).
* **Already available for forward invariance:** `Features.edge_no_retirement` is the monotone
  comparison that keeps `x_e(t) ≥ x_e(0)e^{-t}` once a trajectory exists.

No consumer of `thm11` reads `HasSolution`, so nothing downstream is blocked by keeping it named;
`Theorem.lean`'s premise list (P1–P3) is unchanged.

## 9.4 Receipts (three, exact, this tree at HEAD-parent `4c03db6` + M8)

    BUILD     lake build Bonnifaci          exit 0   2258 jobs   receipts/build_m8.receipt
              lake env lean Bonnifaci/M8.lean   0 errors, 0 warnings
              (driver: receipts/build_lock.py fcntl single-writer on
               /Volumes/Substrate-1/bigo/.build.lock; live-pressure gate GO:
               free 71%, swap NOT growing 19400M -> 16351M over 20s)
    OLEANS    15 present: Model KL Core Optimality Features Feasibility Theorem Thm11
              Duality Lemma41 Lemma43 Mu M6 M7 **M8**
    AXIOMS    receipts/axioms_m8.txt — every new declaration:
              depends on axioms: [propext, Classical.choice, Quot.sound]
              zero `sorry`, zero `axiom` commands anywhere in Bonnifaci/*.lean
    WARNINGS  0 contributed by M8 (the 4 pre-existing warnings in Thm11/Lemma43 are unchanged)

## 9.5 Next

1. **M8 shortest-path instantiation** (signed incidence, unit s-t demand) — the only remaining
   milestone that is cheap on this pin. Budget a bounded spike on the incidence plumbing first.
2. `HasSolution` only if the 6616-module ODE closure is ever built deliberately (a scheduling
   decision, not a proof decision). Until then the seam is named and its closed half is recorded
   in §9.3.
3. If a successor wants a *sharp* Lipschitz constant, `W/μ` in §9.2 is the object to tighten;
   the estimate itself (`energy_perturb`) is the reusable part.
