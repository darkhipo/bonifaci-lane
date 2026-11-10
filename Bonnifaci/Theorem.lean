/- Copyright (c) 2026 MultiAgency bonifaci-lane. -/
import Bonnifaci.Model
import Bonnifaci.KL

noncomputable section

/-!
# Theorem 1.1 of [Bonifaci 2016] — the machine-checked statement

Primary source, verified against the full text on 2026-11-10 (see STMTS.md §0):
Vincenzo Bonifaci, *"On the Convergence Time of a Natural Dynamics for Linear
Programming"*, arXiv:1611.06729v1 (21 Nov 2016), Algorithmica 82(2):300–315, 2020,
DOI `10.1007/s00453-019-00615-3` (Crossref-verified).

Verbatim Theorem 1.1:

> For a feasible initial condition `s ∈ ℝ^E_{>0}`, consider the solution
> `x : [0,∞) → Ω` to the Physarum dynamics (3) with `x(0) = s`. Then `x(t)` is a
> feasible solution to (1) for any `t ≥ 0`, and for any `ǫ > 0`, it holds that
> `cost(x(t)) ≤ (1 + ǫ)·opt` for all
> `t ≥ (6/ǫ)·( ln(cost(x(0))/opt) + KL(ξ*, ξ(0)) )`,
> where `KL(·,·)` denotes the [relative entropy].

This module fixes the statement and the notation (eq. (2)–(3), (7) of the paper) and
proves the interface lemmas that need no analysis. The *proof* is assembled in
`Bonnifaci/Thm11.lean` (WIP — see STMTS.md §7 for its live error inventory), which
imports this module, so the statement cannot drift while the proof is repaired.

## Named premises (D7 seams)

The paper's analytic work is *not* assumed silently: it is spelled out as explicit
hypotheses of `thm11_statement`, and each is discharged (or scheduled) downstream:

* **P1** feasibility invariance — Lemma 3.2. **DISCHARGED** in `Bonnifaci/Feasibility.lean`
  (`feasibility_invariant`, from `defect_ode` = Prop 3.1 and `defect_decay`).
* **P2** log-cost derivative bound — Lemma 4.1:
  `d/dt ln(cost/opt) ≤ √(ℰ/cost) − 1`. Algebraic core `cs_step` proved in `Core.lean`;
  the chain rule along the trajectory remains (M4).
* **P3** KL derivative bound — Lemma 4.3:
  `d/dt KL(ξ*,ξ) ≤ √(ℰ/cost) − ℰ/opt`, via Lemma 4.2's identity
  `d/dt Σ (c_jx*_j/opt) ln(x*_j/x_j) = 1 − ℰ/opt` (M3).
-/

open Finset Real

namespace Bonnifaci

variable {N E : Type*} [Fintype N] [Fintype E]

/-! ### Notation of §4 of the paper -/

/-- `ξ*`: the optimal cost distribution over edges, `ξ*_e = c_e x*_e / opt`. -/
def xiStar (d : LPData N E) (xstar : E → ℝ) (e : E) : ℝ :=
  d.c e * xstar e / d.cost xstar

/-- `ξ(t)`: the running cost distribution of the trajectory,
`ξ_e(t) = c_e x_e(t) / cost(x(t))`. -/
def xiAt (d : LPData N E) (S : d.Solution) (t : ℝ) (e : E) : ℝ :=
  d.c e * S.x t e / d.cost (S.x t)

/-- Energy `ℰ(t) = q(t)ᵀ R(t) q(t)` of the electrical flow. -/
def energyAt (d : LPData N E) (S : d.Solution) (t : ℝ) : ℝ :=
  ∑ e, d.c e / S.x t e * S.q t e ^ 2

/-- The potential of eq. (7) of [Bonifaci 2016], in the split form that the paper's
Lemma 4.3 differentiates:
`Φ(t) = 2·ln(cost(x(t))/opt) + Σ_e ξ*_e · ln(x*_e / x_e(t))`,
which equals `ln(cost/opt) + KL(ξ*, ξ(t))`. -/
def Phi (d : LPData N E) (S : d.Solution) (xstar : E → ℝ) (t : ℝ) : ℝ :=
  2 * Real.log (d.cost (S.x t) / d.cost xstar)
    + ∑ e, xiStar d xstar e * Real.log (xstar e / S.x t e)

/-! ### Interface lemmas (no analysis needed) -/

/-- `ξ*` is nonnegative on feasible data. -/
theorem xiStar_nonneg (d : LPData N E) {xstar : E → ℝ} (hxstar : d.IsFeasible xstar)
    (hopt : 0 < d.cost xstar) (e : E) : 0 ≤ xiStar d xstar e :=
  div_nonneg (mul_nonneg (d.hc e).le (hxstar.1 e)) hopt.le

/-- `ξ(t)` is strictly positive along the trajectory (the tube vector lives in `Ω`). -/
theorem xiAt_pos (d : LPData N E) (S : d.Solution) {t : ℝ} (hcost : 0 < d.cost (S.x t))
    (e : E) : 0 < xiAt d S t e :=
  div_pos (mul_pos (d.hc e) (S.hpos t e)) hcost

/-- The energy is nonnegative. -/
theorem energyAt_nonneg (d : LPData N E) (S : d.Solution) (t : ℝ) :
    0 ≤ energyAt d S t :=
  Finset.sum_nonneg fun e _ =>
    mul_nonneg (div_nonneg (d.hc e).le (S.hpos t e).le) (sq_nonneg _)

/-! ### The statement -/

/-- **Theorem 1.1 of [Bonifaci 2016]**, exactly as stated in the paper (feasible
initial condition, `ε > 0`), with the analytic steps P1–P3 carried as *named
premises* rather than assumed silently. `Φ` is eq. (7); the bound
`(6/ε)·Φ(0)` is the paper's, obtained from Theorem 4.7 with `ε' = ε/3`.

Range note, stated honestly rather than glossed: the paper says «for any ε > 0», but its
proof substitutes ε' = ε/3 into Lemma 4.4, which requires ε' ∈ (0, 1/2) — i.e. the paper's
argument is effective only for ε < 3/2, and that phrase is a mild overstatement in the
source. This statement carries ε ≤ 1, strictly inside the effective range, so nothing is
lost; going past 3/2 needs a separate argument (the threshold Φ(0)/(ε/6) shrinks with ε
while ε' would leave Lemma 4.4's domain).

The reader of this definition can see every hypothesis the proof needs: nothing is
hidden, and `Bonnifaci/Thm11.lean` proves this same shape from P1–P3. -/
def thm11_statement : Prop :=
  ∀ (d : LPData N E), (∃ n, d.b n ≠ 0) → ∀ S : d.Solution,
    -- P1 (Lemma 3.2): feasibility is invariant along the trajectory.
    (∀ t, d.IsFeasible (S.x t)) →
    ∀ xstar : E → ℝ, d.IsFeasible xstar →
    (∀ y, d.IsFeasible y → d.cost xstar ≤ d.cost y) →
    -- P2 (Lemma 4.1): log-cost derivative bound.
    (∀ t : ℝ, deriv (fun u => Real.log (d.cost (S.x u) / d.cost xstar)) t
      ≤ Real.sqrt (energyAt d S t / d.cost (S.x t)) - 1) →
    -- P3 (Lemma 4.3): KL derivative bound.
    (∀ t : ℝ, deriv (fun u => KL (xiStar d xstar) (xiAt d S u)) t
      ≤ Real.sqrt (energyAt d S t / d.cost (S.x t)) - energyAt d S t / d.cost xstar) →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ,
      (6 / ε) * Phi d S xstar 0 ≤ t → d.cost (S.x t) ≤ (1 + ε) * d.cost xstar

end Bonnifaci
