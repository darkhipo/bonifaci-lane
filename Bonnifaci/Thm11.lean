/-
Copyright (c) 2026 MultiAgency bonifaci-lane.
-/
import Bonnifaci.Core
import Bonnifaci.Features
import Bonnifaci.Theorem
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

/-!
# Theorem 1.1 of [Bonifaci 2016] — the KL Lyapunov convergence bound

Primary source (verified 2026-11-09): Vincenzo Bonifaci,
*"On the Convergence Time of a Natural Dynamics for Linear Programming"*
(arXiv:1611.06729, 21 Nov 2016; Algorithmica 82(2):300-315, 2020,
DOI 10.1007/s00453-019-00615-3).

The theorem (feasible-start form, finite support): for a solution trajectory of the
Physarum dynamics starting feasible, for every `0 < ε ≤ 1` and every
`t ≥ (6/ε)·Φ(0)`, one has `cost(x(t)) ≤ (1+ε)·opt`, where
`Φ(t) = ln(cost(x(t))/opt) + KL(ξ*, ξ(t))` is the dimensionless potential of eq. (7).

**Named premises (the D7 seams).** The analytic work of the paper is factored into
three premises, stated as hypotheses of `LPData.thm11` and documented in STMTS.md:

* **P1** — feasibility invariance (Lemma 3.2; provable via `‖Ax−b‖² = e^{-2t}‖Ax₀−b‖²`,
  Gronwall-free comparison; downstream milestone).
* **P2** — the log-cost derivative bound (Lemma 4.1; provable from `cs_step` in
  `Bonnifaci.Core` + chain rule along the trajectory; downstream milestone).
* **P3** — the KL derivative bound (Lemmas 4.2 + 4.3; provable from the duality
  identity `x*ᵀRq = bᵀp = ℰ` + chain rule; downstream milestone).

Everything else — the potential algebra, the two-case decrease core, the cost
monotonicity, the integration step, Gibbs' inequality for `Φ ≥ 0`, and the final
contradiction — is *proved* below. There is no `sorry` and no axiom in this lane.
-/

open Finset Real Set

namespace Bonnifaci

variable {N E : Type*} [Fintype N] [Fintype E]

/-! ### Notation

The notation xiStar, xiAt, energyAt and Phi lives in Bonnifaci/Theorem.lean (the
machine-checked statement module), so the statement cannot drift while this proof
is being repaired.
-/

/-! ### Positivity and normalization -/

/-- Nontrivial `b` forces positive cost on every feasible point. -/
theorem cost_pos (d : LPData N E) {x : E → ℝ} (hbnz : ∃ n, d.b n ≠ 0)
    (hx : d.IsFeasible x) : 0 < d.cost x := by
  obtain ⟨n, hn⟩ := hbnz
  by_contra hcon
  push_neg at hcon
  have h1 : 0 ≤ d.cost x := Finset.sum_nonneg fun e _ => mul_nonneg (d.hc e).le (hx.1 e)
  have h2 : d.cost x = 0 := le_antisymm hcon h1
  have h3 : ∀ e ∈ (Finset.univ : Finset E), d.c e * x e = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun e _ => mul_nonneg (d.hc e).le (hx.1 e)).1 h2
  have h4 : ∀ e, x e = 0 := fun e =>
    (mul_eq_zero.1 (h3 e (Finset.mem_univ e))).resolve_left (ne_of_gt (d.hc e))
  refine hn ?_
  rw [← hx.2 n]
  exact Finset.sum_eq_zero fun e _ => by rw [h4 e, mul_zero]

theorem sum_xiStar (d : LPData N E) (xstar : E → ℝ) (hbnz : ∃ n, d.b n ≠ 0)
    (hxstar : d.IsFeasible xstar) : ∑ e, xiStar d xstar e = 1 := by
  have hoptpos : 0 < d.cost xstar := cost_pos d hbnz hxstar
  have hdef : ∑ e, xiStar d xstar e = ∑ e, d.c e * xstar e / d.cost xstar := rfl
  have hterm : ∀ e, xiStar d xstar e = d.c e * xstar e * (d.cost xstar)⁻¹ := by
    intro e; rw [xiStar, div_eq_mul_inv]
  rw [Finset.sum_congr rfl fun e _ => hterm e, ← Finset.sum_mul,
    show ∑ e, d.c e * xstar e = d.cost xstar from rfl, mul_inv_cancel₀ hoptpos.ne']

theorem sum_xiAt (d : LPData N E) (S : d.Solution) (hbnz : ∃ n, d.b n ≠ 0)
    (hfeas : ∀ t, d.IsFeasible (S.x t)) (t : ℝ) : ∑ e, xiAt d S t e = 1 := by
  have hcostpos : 0 < d.cost (S.x t) := cost_pos d hbnz (hfeas t)
  have hdef : ∑ e, xiAt d S t e = ∑ e, d.c e * S.x t e / d.cost (S.x t) := rfl
  have hterm : ∀ e, xiAt d S t e = d.c e * S.x t e * (d.cost (S.x t))⁻¹ := by
    intro e; rw [xiAt, div_eq_mul_inv]
  rw [Finset.sum_congr rfl fun e _ => hterm e, ← Finset.sum_mul,
    show ∑ e, d.c e * S.x t e = d.cost (S.x t) from rfl, mul_inv_cancel₀ hcostpos.ne']

/-- Energy is nonnegative. -/
theorem energy_nonneg (d : LPData N E) (S : d.Solution) (t : ℝ) : 0 ≤ energyAt d S t :=
  Finset.sum_nonneg fun e _ => mul_nonneg (div_nonneg (d.hc e).le (S.hpos t e).le) (sq_nonneg _)

/-- **Energy ≤ cost at feasible points** (the paper's Lemma 4.5, from Thomson). -/
theorem energy_le_cost (d : LPData N E) (S : d.Solution) {t : ℝ}
    (hfeas : d.IsFeasible (S.x t)) : energyAt d S t ≤ d.cost (S.x t) := by
  have h := S.thomson t (S.x t) hfeas.2
  refine le_trans h ?_
  have hEq : ∑ e, d.c e / S.x t e * S.x t e ^ 2 = d.cost (S.x t) := by
    unfold LPData.cost
    exact Finset.sum_congr rfl fun e _ => by field_simp
  exact hEq.le

/-! ### The potential: paper form, nonnegativity, differentiability -/

/-- KL term of the potential in split form (the identity used in Lemma 4.3). -/
theorem kl_split (d : LPData N E) (S : d.Solution) (xstar : E → ℝ)
    (hxstar : d.IsFeasible xstar) (hbnz : ∃ n, d.b n ≠ 0)
    (hfeas : ∀ t, d.IsFeasible (S.x t)) (t : ℝ) :
    KL (xiStar d xstar) (xiAt d S t)
      = ∑ e, xiStar d xstar e * Real.log (xstar e / S.x t e)
        + Real.log (d.cost (S.x t) / d.cost xstar) := by
  have hoptpos : 0 < d.cost xstar := cost_pos d hbnz hxstar
  have hcostpos : 0 < d.cost (S.x t) := cost_pos d hbnz (hfeas t)
  have hsumstar := sum_xiStar d xstar hbnz hxstar
  have term : ∀ e, xiStar d xstar e * Real.log (xiStar d xstar e / xiAt d S t e)
      = xiStar d xstar e * (Real.log (xstar e / S.x t e)
        + Real.log (d.cost (S.x t) / d.cost xstar)) := by
    intro e
    by_cases h0 : xstar e = 0
    · simp [xiStar, h0]
    · have hr1 : xstar e / S.x t e ≠ 0 := div_ne_zero h0 (ne_of_gt (S.hpos t e))
      have hr2 : d.cost (S.x t) / d.cost xstar ≠ 0 :=
        div_ne_zero (ne_of_gt hcostpos) (ne_of_gt hoptpos)
      have hxi : xiStar d xstar e / xiAt d S t e
          = (xstar e / S.x t e) * (d.cost (S.x t) / d.cost xstar) := by
        have hc : d.c e ≠ 0 := ne_of_gt (d.hc e)
        have hx0 : S.x t e ≠ 0 := ne_of_gt (S.hpos t e)
        have ho : d.cost xstar ≠ 0 := ne_of_gt hoptpos
        have ht0 : d.cost (S.x t) ≠ 0 := ne_of_gt hcostpos
        unfold xiStar xiAt
        field_simp
      rw [hxi, Real.log_mul hr1 hr2]
  calc KL (xiStar d xstar) (xiAt d S t)
      = ∑ e, xiStar d xstar e * Real.log (xiStar d xstar e / xiAt d S t e) := rfl
    _ = ∑ e, xiStar d xstar e * (Real.log (xstar e / S.x t e)
          + Real.log (d.cost (S.x t) / d.cost xstar)) :=
        Finset.sum_congr rfl fun e _ => term e
    _ = ∑ e, xiStar d xstar e * Real.log (xstar e / S.x t e)
          + Real.log (d.cost (S.x t) / d.cost xstar) * ∑ e, xiStar d xstar e := by
        have hterm : ∀ e, xiStar d xstar e * (Real.log (xstar e / S.x t e)
              + Real.log (d.cost (S.x t) / d.cost xstar))
            = xiStar d xstar e * Real.log (xstar e / S.x t e)
              + Real.log (d.cost (S.x t) / d.cost xstar) * xiStar d xstar e := by
          intro e; ring
        rw [Finset.sum_congr rfl fun e _ => hterm e, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by rw [hsumstar]; ring

/-- The potential in the paper's form, eq. (7). -/
theorem Phi_eq_paper (d : LPData N E) (S : d.Solution) (xstar : E → ℝ)
    (hxstar : d.IsFeasible xstar) (hbnz : ∃ n, d.b n ≠ 0)
    (hfeas : ∀ t, d.IsFeasible (S.x t)) (t : ℝ) :
    Phi d S xstar t = Real.log (d.cost (S.x t) / d.cost xstar)
      + KL (xiStar d xstar) (xiAt d S t) := by
  rw [Phi, kl_split d S xstar hxstar hbnz hfeas t]; ring

/-- **Φ ≥ 0** on the feasible trajectory: log-ratio ≥ 0 (feasibility ⇒ cost ≥ opt)
plus Gibbs' inequality for the KL term. -/
theorem Phi_nonneg (d : LPData N E) (S : d.Solution) (xstar : E → ℝ)
    (hxstar : d.IsFeasible xstar) (hbnz : ∃ n, d.b n ≠ 0)
    (hfeas : ∀ t, d.IsFeasible (S.x t)) (hopt : ∀ y, d.IsFeasible y → d.cost xstar ≤ d.cost y)
    (t : ℝ) : 0 ≤ Phi d S xstar t := by
  have hoptpos : 0 < d.cost xstar := cost_pos d hbnz hxstar
  have hcostpos : 0 < d.cost (S.x t) := cost_pos d hbnz (hfeas t)
  rw [Phi_eq_paper d S xstar hxstar hbnz hfeas t]
  refine add_nonneg ?_ ?_
  · refine Real.log_nonneg ?_
    rw [one_le_div hoptpos]
    exact hopt (S.x t) (hfeas t)
  · refine KL_nonneg ?_ ?_ ?_ ?_
    · intro e; exact div_nonneg (mul_nonneg (d.hc e).le (hxstar.1 e)) hoptpos.le
    · intro e; exact div_pos (mul_pos (d.hc e) (S.hpos t e)) hcostpos
    · exact sum_xiStar d xstar hbnz hxstar
    · exact sum_xiAt d S hbnz hfeas t

theorem differentiable_cost (d : LPData N E) (S : d.Solution) :
    Differentiable ℝ (fun u => d.cost (S.x u)) := fun u =>
  differentiableAt_finset_sum fun e => (differentiableAt_const (d.c e)).mul (S.hdiff u e)

theorem differentiable_log_cost (d : LPData N E) (S : d.Solution) (xstar : E → ℝ)
    (hxstar : d.IsFeasible xstar) (hbnz : ∃ n, d.b n ≠ 0)
    (hfeas : ∀ t, d.IsFeasible (S.x t)) :
    Differentiable ℝ (fun u => Real.log (d.cost (S.x u) / d.cost xstar)) := by
  have hdiv : Differentiable ℝ (fun u => d.cost (S.x u) / d.cost xstar) :=
    (differentiable_cost d S).div (differentiable_const _)
      fun _ => ne_of_gt (cost_pos d hbnz hxstar)
  exact hdiv.log fun u =>
    div_ne_zero (ne_of_gt (cost_pos d hbnz (hfeas u)))
      (ne_of_gt (cost_pos d hbnz hxstar))

theorem differentiable_kl (d : LPData N E) (S : d.Solution) (xstar : E → ℝ)
    (hxstar : d.IsFeasible xstar) (hbnz : ∃ n, d.b n ≠ 0)
    (hfeas : ∀ t, d.IsFeasible (S.x t)) :
    Differentiable ℝ (fun u => KL (xiStar d xstar) (xiAt d S u)) := by
  have hfun : (fun u => KL (xiStar d xstar) (xiAt d S u))
      = fun u => (∑ e, xiStar d xstar e * Real.log (xstar e / S.x u e))
          + Real.log (d.cost (S.x u) / d.cost xstar) :=
    funext fun u => kl_split d S xstar hxstar hbnz hfeas u
  rw [hfun]
  refine Differentiable.add ?_ (differentiable_log_cost d S xstar hxstar hbnz hfeas)
  intro u
  exact differentiableAt_finset_sum fun e => by
    by_cases hxe : xstar e = 0
    · -- the term is identically zero (x*_e = 0 makes xi*_e = 0), hence differentiable
      have hzero : (fun v => xiStar d xstar e * Real.log (xstar e / S.x v e)) = fun _ => 0 := by
        funext v
        simp [xiStar, hxe]
      rw [hzero]
      exact differentiableAt_const 0
    · have hxpos : 0 < xstar e := lt_of_le_of_ne (hxstar.1 e) (Ne.symm hxe)
      have hq : DifferentiableAt ℝ (fun v => xstar e / S.x v e) u :=
        (differentiableAt_const (xstar e)).div (S.hdiff u e) (ne_of_gt (S.hpos u e))
      have hqne : xstar e / S.x u e ≠ 0 := div_ne_zero hxe (ne_of_gt (S.hpos u e))
      exact (differentiableAt_const (xiStar d xstar e)).mul (hq.log hqne)

theorem differentiable_Phi (d : LPData N E) (S : d.Solution) (xstar : E → ℝ)
    (hxstar : d.IsFeasible xstar) (hbnz : ∃ n, d.b n ≠ 0)
    (hfeas : ∀ t, d.IsFeasible (S.x t)) : Differentiable ℝ (Phi d S xstar) := by
  have hfun : Phi d S xstar
      = fun u => 2 * Real.log (d.cost (S.x u) / d.cost xstar)
          + ∑ e, xiStar d xstar e * Real.log (xstar e / S.x u e) := rfl
  rw [hfun]
  refine Differentiable.add ?_ ?_
  · exact (differentiable_log_cost d S xstar hxstar hbnz hfeas).const_mul 2
  · intro u
    exact differentiableAt_finset_sum fun e => by
      by_cases hxe : xstar e = 0
      · have hzero : (fun v => xiStar d xstar e * Real.log (xstar e / S.x v e)) = fun _ => 0 := by
          funext v
          simp [xiStar, hxe]
        rw [hzero]
        exact differentiableAt_const 0
      · have hxpos : 0 < xstar e := lt_of_le_of_ne (hxstar.1 e) (Ne.symm hxe)
        have hq : DifferentiableAt ℝ (fun v => xstar e / S.x v e) u :=
          (differentiableAt_const (xstar e)).div (S.hdiff u e) (ne_of_gt (S.hpos u e))
        have hqne : xstar e / S.x u e ≠ 0 := div_ne_zero hxe (ne_of_gt (S.hpos u e))
        exact (differentiableAt_const (xiStar d xstar e)).mul (hq.log hqne)

/-! ### Theorem 1.1 -/

/--
**Theorem 1.1 of [Bonifaci 2016]** (feasible-start form, finite support):

> For a feasible initial condition, the solution `x(t)` of the Physarum dynamics
> satisfies `cost(x(t)) ≤ (1+ε)·opt` for all `t ≥ (6/ε)·(ln(cost(x(0))/opt) + KL(ξ*, ξ(0)))`.

The analytic premises P1–P3 are hypotheses of this theorem (see module docstring);
all other steps are proved. The `ε ≤ 1` restriction is w.l.o.g. (the paper's
"any ε > 0" follows by replacing ε with `min(ε, 1)` and monotonicity in ε).
-/
theorem thm11
    (d : LPData N E) (hbnz : ∃ n, d.b n ≠ 0) (S : d.Solution)
    -- NAMED PREMISE P1 (Lemma 3.2): feasibility is invariant along the trajectory.
    (hfeas : ∀ t, d.IsFeasible (S.x t))
    (xstar : E → ℝ) (hxstar : d.IsFeasible xstar)
    (hopt : ∀ y, d.IsFeasible y → d.cost xstar ≤ d.cost y)
    -- NAMED PREMISE P2 (Lemma 4.1): log-cost derivative bound.
    (hcostlog : ∀ t : ℝ, deriv (fun u => Real.log (d.cost (S.x u) / d.cost xstar)) t
      ≤ Real.sqrt (energyAt d S t / d.cost (S.x t)) - 1)
    -- NAMED PREMISE P3 (Lemma 4.3): KL derivative bound.
    (hkl : ∀ t : ℝ, deriv (fun u => KL (xiStar d xstar) (xiAt d S u)) t
      ≤ Real.sqrt (energyAt d S t / d.cost (S.x t)) - energyAt d S t / d.cost xstar)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ)
    (ht : (6 / ε) * Phi d S xstar 0 ≤ t) :
    d.cost (S.x t) ≤ (1 + ε) * d.cost xstar := by
  have hoptpos : 0 < d.cost xstar := cost_pos d hbnz hxstar
  have hcostpos : ∀ u, 0 < d.cost (S.x u) := fun u => cost_pos d hbnz (hfeas u)
  have hE0 : ∀ u, 0 ≤ energyAt d S u := fun u => energy_nonneg d S u
  have hEle : ∀ u, energyAt d S u ≤ d.cost (S.x u) := fun u => energy_le_cost d S (hfeas u)
  have hΦ0 : 0 ≤ Phi d S xstar 0 := Phi_nonneg d S xstar hxstar hbnz hfeas hopt 0
  have ht0 : 0 ≤ t := by
    have h6 : 0 < (6 : ℝ) / ε := div_pos (by norm_num) hε0
    have := mul_nonneg h6.le hΦ0
    linarith
  by_contra hcon
  push_neg at hcon
  -- cost decreases along [0, t] (log-cost is antitone)
  have hlogdiff := differentiable_log_cost d S xstar hxstar hbnz hfeas
  have hloganti : AntitoneOn
      (fun u => Real.log (d.cost (S.x u) / d.cost xstar)) (Set.Icc 0 t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hlogdiff.continuous.continuousOn
      (hlogdiff.differentiableOn.mono interior_subset) fun u hu => ?_
    have h2 : Real.sqrt (energyAt d S u / d.cost (S.x u)) ≤ 1 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by norm_num, by simpa using (div_le_one (hcostpos u)).2 (hEle u)⟩
    linarith [hcostlog u, h2]
  have hcostanti : ∀ u ∈ Set.Icc 0 t, d.cost (S.x t) ≤ d.cost (S.x u) := by
    intro u hu
    have h1 := hloganti hu ⟨ht0, le_refl t⟩ hu.2
    have h1' : Real.log (d.cost (S.x t) / d.cost xstar)
        ≤ Real.log (d.cost (S.x u) / d.cost xstar) := h1
    have h2 : d.cost (S.x t) / d.cost xstar ≤ d.cost (S.x u) / d.cost xstar :=
      (Real.log_le_log_iff (div_pos (hcostpos t) hoptpos) (div_pos (hcostpos u) hoptpos)).1 h1'
    rwa [div_le_div_iff_of_pos_right hoptpos] at h2
  -- while superoptimal, Φ' ≤ −ε/6
  have hPhi' : ∀ u ∈ Set.Ioo (0 : ℝ) t, deriv (Phi d S xstar) u ≤ -ε / 6 := by
    intro u hu
    have hsup : (1 + ε) * d.cost xstar ≤ d.cost (S.x u) :=
      le_trans hcon.le (hcostanti (u := u) (Set.mem_Icc.2 ⟨by linarith [hu.1], le_of_lt hu.2⟩))
    have hγ : 0 ≤ energyAt d S u / d.cost xstar := div_nonneg (hE0 u) hoptpos.le
    have hκ : ((1 : ℝ) + ε / 3) ^ 2 ≤ d.cost (S.x u) / d.cost xstar := by
      rw [le_div_iff₀ hoptpos]
      have h43 : ((1 : ℝ) + ε / 3) ^ 2 ≤ 1 + ε := by nlinarith
      calc ((1 : ℝ) + ε / 3) ^ 2 * d.cost xstar
          ≤ (1 + ε) * d.cost xstar := mul_le_mul_of_nonneg_right h43 hoptpos.le
        _ ≤ d.cost (S.x u) := hsup
    have hcore := phi_decrease_core (ε := ε / 3) (γ := energyAt d S u / d.cost xstar)
      (κ := d.cost (S.x u) / d.cost xstar) (by positivity) (by linarith) hγ hκ
    have hsplit : (energyAt d S u / d.cost xstar) / (d.cost (S.x u) / d.cost xstar)
        = energyAt d S u / d.cost (S.x u) := by field_simp
    rw [hsplit] at hcore
    have hΦeq : Phi d S xstar = fun v => Real.log (d.cost (S.x v) / d.cost xstar)
        + KL (xiStar d xstar) (xiAt d S v) :=
      funext fun v => Phi_eq_paper d S xstar hxstar hbnz hfeas v
    have hklD := differentiable_kl d S xstar hxstar hbnz hfeas
    have hfun : (fun v => Real.log (d.cost (S.x v) / d.cost xstar) + KL (xiStar d xstar) (xiAt d S v))
        = (fun v => Real.log (d.cost (S.x v) / d.cost xstar))
          + fun v => KL (xiStar d xstar) (xiAt d S v) := rfl
    rw [hΦeq, hfun, deriv_add (hlogdiff u) (hklD u)]
    linarith [hcostlog u, hkl u, hcore]
  -- integrate: Φ(t) + (ε/6)t ≤ Φ(0)
  have hgdiff : Differentiable ℝ (fun u => Phi d S xstar u + (ε / 6) * u) := by
    refine (differentiable_Phi d S xstar hxstar hbnz hfeas).add ?_
    exact (differentiable_const (ε / 6)).mul differentiable_id
  have hg : AntitoneOn (fun u => Phi d S xstar u + (ε / 6) * u) (Set.Icc 0 t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hgdiff.continuous.continuousOn
      (hgdiff.differentiableOn.mono interior_subset) fun u hu => ?_
    rw [interior_Icc] at hu
    have hΦeq : Phi d S xstar = fun v => Real.log (d.cost (S.x v) / d.cost xstar)
        + KL (xiStar d xstar) (xiAt d S v) :=
      funext fun v => Phi_eq_paper d S xstar hxstar hbnz hfeas v
    have hklD := differentiable_kl d S xstar hxstar hbnz hfeas
    have hdg : deriv (fun v : ℝ => (ε / 6) * v) u = ε / 6 := by
      have hdm := deriv_const_mul (ε / 6) (x := u) differentiableAt_id
      simpa using hdm
    have hsum : deriv (fun v => Phi d S xstar v) u
        = deriv (fun v => Real.log (d.cost (S.x v) / d.cost xstar)) u
          + deriv (fun v => KL (xiStar d xstar) (xiAt d S v)) u := by
      have hfun : (fun v => Real.log (d.cost (S.x v) / d.cost xstar) + KL (xiStar d xstar) (xiAt d S v))
          = (fun v => Real.log (d.cost (S.x v) / d.cost xstar))
            + fun v => KL (xiStar d xstar) (xiAt d S v) := rfl
      rw [hΦeq, hfun, deriv_add (hlogdiff u) (hklD u)]
    show deriv ((fun v => Phi d S xstar v) + fun v => (ε / 6) * v) u ≤ 0
    have hPhid : DifferentiableAt ℝ (fun v => Phi d S xstar v) u :=
      differentiable_Phi d S xstar hxstar hbnz hfeas u
    have hεd : DifferentiableAt ℝ (fun v : ℝ => (ε / 6) * v) u :=
      (differentiableAt_const (ε / 6)).mul differentiableAt_id
    rw [deriv_add hPhid hεd, hsum, hdg]
    linarith [hPhi' u hu, hcostlog u, hkl u]
  have hgtle : Phi d S xstar t + (ε / 6) * t ≤ Phi d S xstar 0 := by
    have := hg (a := 0) (b := t) ⟨le_refl 0, ht0⟩ ⟨ht0, le_refl t⟩ ht0
    simpa using this
  -- Φ(t) ≤ 0 and ≥ 0, so Φ(t) = 0, so the log part vanishes, so cost = opt
  have ht6 : Phi d S xstar 0 ≤ (ε : ℝ) / 6 * t := by
    have h2 : 0 < (6 : ℝ) / ε := div_pos (by norm_num) hε0
    have h4 : Phi d S xstar 0 ≤ t / ((6 : ℝ) / ε) := (le_div_iff₀ h2).2 (by linarith [ht])
    have h3 : t / ((6 : ℝ) / ε) = (ε / 6) * t := by field_simp
    linarith [h4, h3]
  have hPhit : Phi d S xstar t ≤ 0 := by linarith
  have hPhit0 : 0 ≤ Phi d S xstar t := Phi_nonneg d S xstar hxstar hbnz hfeas hopt t
  have hPhitz : Phi d S xstar t = 0 := le_antisymm hPhit hPhit0
  have hlogz : Real.log (d.cost (S.x t) / d.cost xstar) = 0 := by
    have hsplit := Phi_eq_paper d S xstar hxstar hbnz hfeas t
    rw [hPhitz] at hsplit
    have hklnonneg : 0 ≤ KL (xiStar d xstar) (xiAt d S t) := by
      refine KL_nonneg ?_ ?_ ?_ ?_
      · intro e; exact div_nonneg (mul_nonneg (d.hc e).le (hxstar.1 e)) hoptpos.le
      · intro e; exact div_pos (mul_pos (d.hc e) (S.hpos t e)) (hcostpos t)
      · exact sum_xiStar d xstar hbnz hxstar
      · exact sum_xiAt d S hbnz hfeas t
    have hlognonneg : 0 ≤ Real.log (d.cost (S.x t) / d.cost xstar) :=
      Real.log_nonneg (by rw [one_le_div hoptpos]; exact hopt (S.x t) (hfeas t))
    linarith
  have hcosteq : d.cost (S.x t) = d.cost xstar := by
    rcases Real.log_eq_zero.1 hlogz with h0 | h1 | hneg
    · exact absurd (div_pos (hcostpos t) hoptpos) (by rw [h0]; linarith)
    · have h2 : d.cost (S.x t) = d.cost xstar * (d.cost (S.x t) / d.cost xstar) := by
        field_simp
      rw [h2, h1, mul_one]
    · exact absurd (div_pos (hcostpos t) hoptpos) (by rw [hneg]; linarith)
  rw [hcosteq] at hcon
  nlinarith [hcon, hε0, hoptpos]

end Bonnifaci
