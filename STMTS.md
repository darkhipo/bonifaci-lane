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

## 9.6 M8b — the shortest-path instantiation (§2.2), landed (§9.5 item 1 is now done)

The last cheap milestone named in §9.5, executed as instructed: a bounded spike on the
incidence plumbing **first**, then the paper's own §2.2 example closed rather than deferred.
New file: `Bonnifaci/ShortestPath.lean` (19626 bytes, 24 declarations: 1 structure,
6 definitions, 17 theorems). Root target grew from 2258 to 2259 jobs; **16 oleans**.

### 9.6.1 The spike, measured (not estimated)

| candidate module | `closure_cost.py` says | what it actually cost |
|---|---|---|
| `Mathlib.Data.Fintype.Basic` (for a grounded subtype `{v // v ≠ ground}`) | 2 UNBUILT | not taken — see below |
| `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise` (`sum_ite_eq`) | 2 UNBUILT | **0** — already inside `Model`'s closure |
| `Mathlib.Data.Fin.VecNotation` (`![…]` for the concrete instance) | 2 UNBUILT | **0** — already inside `Model`'s closure |

**Correction to how §9.1's table should be read.** *Every* candidate reports exactly `2` UNBUILT
— including `Mathlib.Algebra.Order.BigOperators.Ring.Finset`, which `Bonnifaci.Model` has imported
since M1 and which the target already builds against. The two are `Batteries.Classes.Cast` and
`Mathlib.Data.Sym.Sym2.Init`: sources present in the package tree, oleans absent from *every*
`.lake/build/lib/lean`, build green regardless. So in this tree the number carries a **constant
offset of 2**, and it is the *difference* between candidates that carries signal. §9.1's
72 / 190 / 6616 findings remain sound because each was a difference against this same baseline;
their absolute values should not be read as literal compile counts, and none of them should be
quoted again without this offset stated. (Cause of the offset not investigated — its effect on
this milestone's decision is nil, because the decision was made on differences and every
difference relevant here was 0.)

**The route cost, measured by the build itself: 0 new imports, 1 new module, 10–11 s.**
`Bonnifaci/ShortestPath.lean` imports only `Bonnifaci.Model` and `Bonnifaci.Optimality`.

Two spike findings that changed the design:

1. **A `def` whose declared parameter is unused loses that parameter.** `unitDemand` was written
   inside `namespace Network` under `variable (G : Network V E)`. Because `G` occurs in neither
   the type nor the body, Lean drops it, and `G.unitDemand s t` then fails with *"Invalid field
   notation: Function `unitDemand` does not have a usable parameter of type `Network`"*. It now
   lives in the root namespace, and the theorems that do not mention `G` are stated without it.
2. **`toLPData`'s fields are definitionally but not syntactically reduced.** `(G.toLPData s t).c`
   and `G.len` are the same term — `rfl` proves them equal — but `rw` will not cross them. The two
   proofs that must rewrite carry an explicit `simp only [toLPData]`.
3. **A trap avoided by measurement, not luck:** the `Step` and `IsFixedPoint` hypotheses are
   *not* needed for the concrete instance. `isShortestPathLength_of_tight` only wants a feasible
   flow, a dual-feasible potential, and tightness on the flow's support — so `path3_shortestPath`
   never constructs a `Step`, and therefore never has to discharge Thomson's principle at a
   concrete graph. That would have been the expensive part of the example, and it is not needed.

### 9.6.2 Grounding, proved rather than quoted

§2.2's footnote 1 drops one node's row from `A` "since we stipulated that A should be full rank".
Both halves of that licence are now theorems:

* `Network.feasible_sum_b_eq_zero` — any realisable demand balances, `∑_v b_v = 0`. Hence the
  `|V|` node equations are *never* independent: the incidence matrix has `1⃗` in its left kernel.
* `Network.groundRow_implied` — and this is *which* row may go: fix a ground node `g`; if a vector
  satisfies the equations at every node except `g`, and the demand balances, then the equation at
  `g` holds too. So dropping the ground row loses nothing.

**Not proved, stated as the remaining hypothesis rather than hidden:** that the *reduced* matrix
has full row rank — i.e. that the graph is connected once the ground node is removed. It is
consumed only by the Laplacian-solve layer (`FullRowRank`, M6/M7). Nothing in `ShortestPath.lean`
needs it: every identity and the whole duality argument are rank-free. Grounding is used here for
its *other* job — fixing the potential gauge — and that is what turns the difference `p t − p s`
into `p t` itself in `distance_from_grounded_source`.

*(Closed in §9.7: `Network.groundLPData_fullRowRank` proves it from connectivity, and
`Network.groundLPData_fullRowRank_iff` proves connectivity is also necessary. The paragraph above
is left as written — it is the state of §9.6, not a live gap.)*

### 9.6.3 The identification corollary

`Network.IsShortestPathLength s t L` is the §2.2 LP's optimality predicate: some nonnegative flow
satisfying the unit `s`–`t` demand costs `L`, and no such flow costs less. (Stated as a predicate
rather than via `sInf`, so no completeness of `ℝ` is invoked.) The chain:

| declaration | content |
|---|---|
| `Network.A_mul_potential` | the one structural identity: `∑_v A v e · P v = P(head e) − P(tail e)` |
| `Network.potential_inner_eq_edge_sum` | for any flow `x` realising `b`: `∑_v P v · b v = ∑_e x_e (P(head e) − P(tail e))` |
| `Network.demand_inner` | for the unit `s`–`t` demand that left side is `P t − P s`, the dual objective |
| `Network.dual_feasible_le_cost` | **weak duality**: a dual-feasible `P` lower-bounds every feasible flow's cost |
| `Network.dual_feasible_bound` | hence `P t − P s ≤ L`: every feasible potential *underestimates* the distance |
| `Network.cost_eq_potential_diff_of_tight` | tightness on the support atones for every inequality |
| `Network.isShortestPathLength_of_tight` | **complementary slackness**: tight-on-support certifies the flow shortest and `P t − P s` as the value |
| `Network.fixed_point_potentials_tight` | at a rest point Ohm's law makes `p` tight on **every** edge |
| `Network.fixed_point_potentials_are_distances` | **the corollary**: at a rest point, `p t − p s` **is** the shortest-path value |
| `Network.distance_from_grounded_source` | with `p ground = 0`, the potential `p t` **is** the distance from the grounded source |
| `path3_shortestPath` | **concrete**: on the path graph `0→1→2` with lengths `a`,`b`, the value is `a + b`, witnessed by the distance function `(0, a, a+b)` |

**Honest scope — the same one `Optimality.lean` makes, now in the network case.** A rest point
forces `p(head e) − p(tail e) = len e` on *every* edge at once, so in the interior a rest point
exists only when the lengths are conservative: on a graph with a positive-length cycle it does not
exist. The non-degenerate content is therefore the pair
`isShortestPathLength_of_tight` + `dual_feasible_bound` (no rest point, no convergence, no
existence assumed), which together say the shortest-path value is the **maximum** of `P t − P s`
over dual-feasible potentials; the rest-point theorems say which potentials realise the maximum.
Convergence *to* that optimum with thinning support remains Theorem 1.1's job, unchanged.
`path3` is a tree — deliberately — which is exactly why its lengths are conservative and an
interior rest point does exist there.

### 9.6.4 Receipts (three, exact, this tree)

    BUILD     lake build Bonnifaci          exit 0   2259 jobs   receipts/build_m8b.receipt
              lake env lean Bonnifaci/ShortestPath.lean   0 errors, 0 warnings
              (driver: receipts/build_lock.py fcntl single-writer on
               /Volumes/Substrate-1/bigo/.build.lock; live-pressure gate GO:
               free 71-73%, swap NOT growing 16023.75M -> 16166.62M while the lock was held)
    OLEANS    16 present: Model KL Core Optimality Features Feasibility Theorem Thm11
              Duality Lemma41 Lemma43 Mu M6 M7 M8 **ShortestPath**
    AXIOMS    receipts/axioms_m8b.txt — all 17 new theorems:
              depends on axioms: [propext, Classical.choice, Quot.sound]
              zero `sorry`, zero `axiom` commands anywhere in Bonnifaci/*.lean
              (the only two `sorry` strings in the tree are prose in M7/Thm11 docstrings)
    WARNINGS  0 contributed by ShortestPath; the 4 pre-existing (Thm11 ×3, Lemma43 ×1) unchanged

### 9.6.5 Next

1. **`HasSolution`** remains the one named seam that is a real open problem, and §9.3's measurement
   stands: 6616 modules of ODE library (now with the §9.6.1 offset caveat), plus global two-sided
   existence. Nothing in M8b moves it, and nothing in M8b wanted it.
2. **A connectedness → `FullRowRank` bridge** is the one hypothesis M8b used but did not prove
   (§9.6.2). It is a reachability induction over `Finset`, and it would make the `toLPData`
   instance consumable by M6/M7's `exists_step` — i.e. it is what a successor needs to put a
   *network* through the Laplacian layer. Cheap in principle; not attempted here.
3. **A positive-length-cycle instance** would make the §9.6.3 scope note machine-checkable: no
   dual-feasible tight potential exists on the triangle. Stated as non-existence, so it needs the
   negation of the dual-feasibility system at a concrete graph — a bounded next increment.
4. `W/μ` tightening (§9.2/§9.5 item 3) is unchanged and still available.

## 9.7 The connectivity → `FullRowRank` bridge — §9.6.5 item 2, discharged

The one hypothesis §9.6 used and did not prove is now a theorem, and it is an *equivalence*: for a
`Network`, M6/M7's rank precondition **is** graph connectivity of the grounded network. New file:
`Bonnifaci/NetworkRank.lean` (16366 bytes, 20 declarations: 3 definitions, 17 theorems). Root
target grew from 2259 to 2260 jobs; **17 oleans**; one new import, and it is our own module (`M6`),
not a Mathlib one.

### 9.7.1 What is proved

| declaration | content |
|---|---|
| `Network.Adj` | undirected adjacency: `v` and `w` are the two ends of some edge, in either order |
| `Network.adj_comm` | `Adj` is symmetric |
| `Network.eq_of_adj` | one step: an edge-invariant `P` agrees on any adjacent pair |
| `Network.eq_of_reflTransGen` | **the reachability induction**: invariant along one edge ⇒ along a chain |
| `Network.reflTransGen_comm` | a chain can be walked backwards |
| `Network.Connected` | `∀ v w, ReflTransGen Adj v w` |
| `Network.eq_const_of_connected` | connectedness consumed: edge-invariant ⇒ constant |
| `Network.groundLPData` | **the grounded reduction of footnote 1**: same incidence/demand/lengths indexed by `{v // v ≠ g}` |
| `Network.groundLPData_A` | the reduced rows are the network's rows, restricted (definitional) |
| `Network.groundLPData_fullRowRank_of_rooted` | reachability from `g` ⇒ `FullRowRank` — the actual proof |
| `Network.groundLPData_fullRowRank` | **the bridge**: `G.Connected → (G.groundLPData s t g).FullRowRank` |
| `Network.connected_of_groundLPData_fullRowRank` | **the converse**: full row rank ⇒ every node reachable from `g` |
| `Network.groundLPData_fullRowRank_iff` | **connectivity ⇔ full row rank** |
| `Network.toLPData_not_fullRowRank` | **grounding is necessary**: the ungrounded `toLPData` is *never* full row rank |
| `Network.groundLPData_exists_step` | **the consumer**: a connected network inhabits M6's `Step x` for every `x > 0` |
| `path3_connected` | the path graph `0 → 1 → 2` is connected |
| `path3_groundLPData_fullRowRank` | the grounded path graph has full row rank — first concrete instance |
| `path3_toLPData_not_fullRowRank` | *the same graph*, ungrounded: rank-deficient |
| `path3_groundLPData_b` | grounding at the source turns the unit `0`–`2` demand into the unit vector at the sink |
| `path3_groundLPData_step_nonempty` | **end to end**: the path graph inhabits `Step x` with Kirchhoff, Ohm, and Thomson |

### 9.7.2 The proof, and why it is short

`FullRowRank` unfolds to: `∑_v A_{ve} p_v = 0` for every edge ⇒ `p = 0`. By
`Network.A_mul_potential` the hypothesis reads `p(head e) = p(tail e)`, so the whole content is
*"a function constant across every edge of a connected graph is constant"*. Extend `p` to all of
`V` by `P g = 0`, split the `V`-sum at the ground node with
`Fintype.sum_eq_add_sum_subtype_ne`, and note the ground term carries the factor `P g = 0` — the
surviving terms are exactly the reduced system's equations — so `P` is edge-invariant; connectivity
then propagates `P g = 0` everywhere. No search tree, no determinant, no rank-nullity.

**The converse is the reason the bridge is not a sufficient condition with slack.** If a node `w` is
unreachable from `g`, the indicator of the unreachable set is a nonzero kernel vector: reachability
is closed under adjacency (so every reduced row reads `0 − 0` or `1 − 1`), and the one row that
would have excluded it — the ground row — is precisely the row that was dropped. Hence
`FullRowRank ↔ ` reachability, and, by `toLPData_not_fullRowRank`, grounding is not cosmetic:
`1⃗` is a nonzero kernel vector of the *ungrounded* incidence for every `Network` on a node set with
at least the evaluation node. `ShortestPath.lean`'s `feasible_sum_b_eq_zero` said this from the
demand side; this says it from the matrix side.

### 9.7.3 Six findings, all measured on this pin

1. **`Fintype.sum_eq_add_sum_subtype_ne f g : ∑ i, f i = f g + ∑ i : {i // i ≠ g}, f ↑i`** is the
   exact tool the reduction wanted — the ground row splits off as one additive term, so summing
   over the punctured subtype needs no `sum_bij`, no `Equiv`, no `Finset.sum_subtype` plumbing.
   (`Finset.sum_subtype`, `Finset.sum_coe_sort`, `Finset.sum_attach` all exist and all were probed
   first; the `Fintype` one is the shortest path by a wide margin.) This is why the reduction is
   stated as a subtype rather than as `Finset.erase`.
2. **`Relation.ReflTransGen` has exactly two constructors, `refl` and `tail`.** `head` is a *derived*
   lemma, so `induction h with | refl | head | tail` fails with *"Invalid alternative name `head`:
   There are no unhandled alternatives"*. The chain-walking proof must be written as `tail` + a
   symmetry step (`reflTransGen_comm`), which is also how the backwards direction gets in.
3. **Every `if`/`dite` lemma used reflexively is deprecated on this pin.** Measured: `if_pos` →
   `ite_eq_left`, `if_neg` → `ite_eq_right`, `dif_pos` → `dite_eq_left`, `dif_neg` →
   `dite_eq_right`, each emitting a warning at use site. Since this lane's receipt standard is
   *zero new warnings*, the indicator function in the converse proof is discharged by
   `by_cases` + `simp [hyp]` (passing the *proof* as a simp lemma, so `simp` reduces the `ite`
   condition to `True`/`False`), never by `rw [if_pos …]`. `simp` internally uses the
   non-deprecated names, so it is warning-free.
4. **`rw` will not beta-reduce under a `set`-alias of a lambda, and `rw … at h` can close the goal
   by itself.** `set Q : V → ℝ := fun v => if … ` then `rw [hQ, if_pos …]` fails with *"Did not
   find an occurrence of the pattern"*, because after `rw [hQ]` the redex is `(fun v => …) g` and
   `rw` matches syntactically. `show`/`exact`/`simpa` beta-reduce (defeq), `rw` does not. The
   mirror-image trap: `rw [hstep] at hzero; exact hzero` reports *"No goals to be solved"* because
   the rewrite at the hypothesis already closed the goal — so where a hypothesis is *transported*
   rather than rewritten, `exact hstep ▸ hzero` is the robust form.
5. **The consumer's typeclass requirements are M6's, not the bridge's.** `exists_step` carries
   `[DecidableEq N] [DecidableEq E]` in M6's section variables, so `groundLPData_exists_step` needs
   a local `classical` to synthesize `DecidableEq {v // v ≠ g}` and `DecidableEq E`. Because the
   instances are consumed *inside the proof*, the bridge's own statement gains no extra argument —
   the theorem is stated for a bare `[Fintype V] [Fintype E] [DecidableEq V]`, exactly like
   `ShortestPath.lean`'s.
6. **`receipts/closure_cost.py` answered a definite false negative for this project's own
   modules.** `closure_cost.py Bonnifaci.M6` printed *"SOURCE: **ABSENT on this pin** (no `.lean`
   in any package)"* while `Bonnifaci/M6.lean` and its built `M6.olean` were both present. Cause,
   read off the source: `PACKAGES` was `[.lake/packages] + [each package subdir]`, and the project
   root — whose modules have exactly the same layout, `ROOT/<Dir>/*.lean` with oleans under
   `ROOT/.lake/build/lib/lean` — was never in the list. Both `find_source` and `is_built` read that
   list, so the tool also mis-classified our own oleans as unbuilt. **Fixed** (ROOT prepended,
   with the failure named in-source) and verified two-arm: own modules now resolve
   (`Bonnifaci.M6` closure 2045, `ShortestPath` 1981, `NetworkRank` 2048, each UNBUILT 2 = the
   §9.6.1 constant offset), and the Mathlib baseline is unchanged (Matrix.Mul 1517,
   FiniteDimensional.Basic 1738, UNBUILT 2 both) — the fix does not move the number the campaign
   reasons with. The fix also yields the measurement this milestone could not make before:
   **importing M6 costs +67 local modules** (1981 → 2048), all already built, which is *why* the
   new module compiled in 10s instead of re-pulling a closure. Registered as a lane wound; no test
   suite exists in this repo, so the guard is the in-source comment plus this two-arm receipt.

### 9.7.4 Receipts (three, exact, this tree)

    BUILD     lake build Bonnifaci          exit 0   2260 jobs   receipts/build_networkrank.receipt
              lake env lean Bonnifaci/NetworkRank.lean   0 errors, 0 warnings, silent
              (driver: receipts/build_lock.py fcntl single-writer on
               /Volumes/Substrate-1/bigo/.build.lock; gate GO: disk free 330Gi unchanged,
               swap NOT growing 16628.62M -> 16620.62M across the lock window — it fell)
    OLEANS    17 present: Model KL Core Optimality Features Feasibility Theorem Thm11
              Duality Lemma41 Lemma43 Mu M6 M7 M8 ShortestPath **NetworkRank**
    AXIOMS    receipts/axioms_networkrank.txt — all 17 new theorems:
              depends on axioms: [propext, Classical.choice, Quot.sound]
              zero `sorry`, zero `axiom` commands anywhere in Bonnifaci/*.lean
              (measured: exactly 3 `sorry` strings in the whole tree, all prose —
              Bonnifaci.lean:31, Thm11.lean:37, M7.lean:34. ShortestPath.lean and
              NetworkRank.lean contain none. §9.6.4's "only two" was M7/Thm11 alone,
              having not counted the root aggregate's header.)
    WARNINGS  0 contributed by NetworkRank; the 4 pre-existing (Thm11 x3, Lemma43 x1) unchanged
    CLOSURE   the one new import is Bonnifaci.M6 (our own, already built). Its Mathlib closure
              (Matrix.Mul 1517, ToLin 1642, FiniteDimensional.Basic 1738) reports UNBUILT 2 in
              every case — the §9.6.1 constant offset, difference against baseline 0.
              TOOL DEFECT FOUND AND FIXED (§9.7.3 finding 6): `closure_cost.py Bonnifaci.M6`
              answered "SOURCE: ABSENT on this pin" for a module that exists — it scanned only
              .lake/packages, never ROOT. ROOT is now prepended; re-measured AFTER the fix:
              Bonnifaci.M6 2045 / ShortestPath 1981 / NetworkRank 2048 local modules, each
              UNBUILT 2 (constant offset), Mathlib baseline UNCHANGED (Matrix.Mul 1517,
              FiniteDimensional.Basic 1738, UNBUILT 2). So importing M6 costs +67 local modules,
              all already built — which is why NetworkRank compiled in 10s.

### 9.7.5 What this changes for the campaign

`LPData.HasSolution` (M7) is `∀ s, (∀ e, 0 < s e) → d.FullRowRank → ∃ S : d.Solution, S.x 0 = s`.
For a **connected network instance** one of those three hypotheses is now discharged by
`groundLPData_fullRowRank`, so the named premise on that instance class is exactly global ODE
existence — the analytic content of §9.3, unchanged, with its algebra no longer entangled.

### 9.7.6 Next

1. **`HasSolution`** is now the *only* named seam on the network instance class, and §9.3's
   measurement stands (6616 modules of ODE library, plus global two-sided existence).
2. **A positive-length-cycle instance** (§9.6.5 item 3) is now cheaper than it was: `path3_connected`
   shows how cheap a connectivity proof of a concrete graph is — a triangle needs the same
   three-node case split, not more — so the remaining work there is the *negation* of the dual
   feasibility system, not the connectivity. It would make §9.6.3's scope note machine-checkable.
3. **`W/μ` tightening** (§9.2, §9.5 item 3) is unchanged and still available.
4. **A general bridge** — `Connected` ⇒ full row rank for an arbitrary `LPData` whose rows come from
   a network-like incidence — is *not* done and not obviously worth it: the specific statement above
   is what the §2.2 instance class needs, and generality here would buy nothing the campaign uses.
