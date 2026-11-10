/- Copyright (c) 2026 MultiAgency bonifaci-lane. -/
import Bonnifaci.Thm11
import Bonnifaci.Duality

noncomputable section

/-!
# Lemma 4.1 (P2): the log-cost derivative bound

`d/dt ln(cost(x(t))/opt) ≤ √(ℰ(t)/cost(x(t))) − 1`

Route (all real arithmetic, campaign constraint (a)):

1. `cost_deriv`: `d/dt cost(x(t)) = Σ_e c_e (q_e − x_e)` — chain rule along the ODE.
2. `log_cost_deriv`: hence `d/dt ln(cost/opt) = (Σ_e c_e q_e − cost)/cost`.
3. `sum_cq_le`: `Σ_e c_e q_e ≤ √ℰ · √cost` — this is `cs_step` with `r_e = c_e/x_e`,
   since `Σ r x² = cost` and `Σ r q² = ℰ`.
4. `cost_log_deriv_le`: divide by `cost > 0` and identify `√ℰ/√cost = √(ℰ/cost)`.

Step 3 is the paper's Cauchy–Schwarz step (Lemma 4.1's `(∗∗)` line), already proved as
`Bonnifaci.cs_step`; this file instantiates it at `r = c/x`.
-/

open Finset Real

namespace Bonnifaci

variable {N E : Type*} [Fintype N] [Fintype E]

/-- Chain rule along the trajectory: `d/dt cost(x(t)) = Σ_e c_e (q_e(t) − x_e(t))`. -/
theorem cost_deriv (d : LPData N E) (S : d.Solution) (t : ℝ) :
    deriv (fun u => d.cost (S.x u)) t = ∑ e, d.c e * (S.q t e - S.x t e) := by
  show deriv (fun u => ∑ e, d.c e * S.x u e) t = ∑ e, d.c e * (S.q t e - S.x t e)
  rw [deriv_finset_sum (f := fun e u => d.c e * S.x u e)
    (fun e => (differentiableAt_const (d.c e)).mul (S.hdiff t e))]
  exact Finset.sum_congr rfl fun e _ => by
    rw [deriv_const_mul (d.c e) (S.hdiff t e), S.hode t e]

/-- `d/dt ln(cost(x(t))/opt) = (Σ_e c_e q_e − cost)/cost`. -/
theorem log_cost_deriv (d : LPData N E) (S : d.Solution) (xstar : E → ℝ) (t : ℝ)
    (hcost : 0 < d.cost (S.x t)) (hopt : 0 < d.cost xstar) :
    deriv (fun u => Real.log (d.cost (S.x u) / d.cost xstar)) t
      = (∑ e, d.c e * S.q t e - d.cost (S.x t)) / d.cost (S.x t) := by
  have h1 : HasDerivAt (fun u => d.cost (S.x u)) (∑ e, d.c e * (S.q t e - S.x t e)) t := by
    have hd := (differentiable_cost d S t).hasDerivAt
    rwa [cost_deriv] at hd
  have h2 : HasDerivAt (fun u => d.cost (S.x u) / d.cost xstar)
      ((∑ e, d.c e * (S.q t e - S.x t e)) / d.cost xstar) t := h1.div_const _
  have hne : d.cost (S.x t) / d.cost xstar ≠ 0 :=
    div_ne_zero (ne_of_gt hcost) (ne_of_gt hopt)
  have h3 := h2.log hne
  rw [h3.deriv]
  have hc : d.cost (S.x t) ≠ 0 := ne_of_gt hcost
  have ho : d.cost xstar ≠ 0 := ne_of_gt hopt
  field_simp
  have hms : ∑ x, d.c x * (S.q t x - S.x t x)
      = ∑ x, (d.c x * S.q t x - d.c x * S.x t x) :=
    Finset.sum_congr rfl fun e _ => mul_sub (d.c e) (S.q t e) (S.x t e)
  rw [hms, Finset.sum_sub_distrib]
  simp [LPData.cost]

/-- The Cauchy–Schwarz step at `r = c/x`: `Σ_e c_e q_e ≤ √ℰ · √cost`. -/
theorem sum_cq_le (d : LPData N E) (S : d.Solution) (t : ℝ) :
    ∑ e, d.c e * S.q t e
      ≤ Real.sqrt (energyAt d S t) * Real.sqrt (d.cost (S.x t)) := by
  have hr : ∀ e, 0 ≤ d.c e / S.x t e := fun e =>
    div_nonneg (d.hc e).le (S.hpos t e).le
  have h := cs_step (fun e => d.c e / S.x t e) (fun e => S.q t e) (fun e => S.x t e) hr
  have hL : ∑ e, d.c e / S.x t e * S.q t e * S.x t e = ∑ e, d.c e * S.q t e := by
    refine Finset.sum_congr rfl fun e _ => ?_
    have hx : S.x t e ≠ 0 := (S.hpos t e).ne'
    calc d.c e / S.x t e * S.q t e * S.x t e
        = d.c e / S.x t e * S.x t e * S.q t e := by ring
      _ = d.c e * S.q t e := by rw [div_mul_cancel₀ _ hx]
  have hR1 : ∑ e, d.c e / S.x t e * S.q t e ^ 2 = energyAt d S t := rfl
  have hR2 : ∑ e, d.c e / S.x t e * S.x t e ^ 2 = d.cost (S.x t) := by
    show ∑ e, d.c e / S.x t e * S.x t e ^ 2 = ∑ e, d.c e * S.x t e
    refine Finset.sum_congr rfl fun e _ => ?_
    have hx : S.x t e ≠ 0 := (S.hpos t e).ne'
    calc d.c e / S.x t e * S.x t e ^ 2
        = d.c e / S.x t e * S.x t e * S.x t e := by ring
      _ = d.c e * S.x t e := by rw [div_mul_cancel₀ _ hx]
  rw [hL, hR1, hR2] at h
  exact h

/-- **Lemma 4.1 (P2), the bound itself**: along the trajectory,
`d/dt ln(cost(x(t))/opt) ≤ √(ℰ(t)/cost(x(t))) − 1`. -/
theorem cost_log_deriv_le (d : LPData N E) (S : d.Solution) (xstar : E → ℝ) (t : ℝ)
    (hcost : 0 < d.cost (S.x t)) (hopt : 0 < d.cost xstar) :
    deriv (fun u => Real.log (d.cost (S.x u) / d.cost xstar)) t
      ≤ Real.sqrt (energyAt d S t / d.cost (S.x t)) - 1 := by
  rw [log_cost_deriv d S xstar t hcost hopt]
  have hcq := sum_cq_le d S t
  have hE := energyAt_nonneg d S t
  have hsc : 0 < Real.sqrt (d.cost (S.x t)) := Real.sqrt_pos.2 hcost
  have h1 : (∑ e, d.c e * S.q t e - d.cost (S.x t)) / d.cost (S.x t)
      = (∑ e, d.c e * S.q t e) / d.cost (S.x t) - 1 := by
    rw [sub_div]
    congr 1
    exact div_self (ne_of_gt hcost)
  rw [h1]
  have h3 : (Real.sqrt (energyAt d S t) * Real.sqrt (d.cost (S.x t))) / d.cost (S.x t)
      = Real.sqrt (energyAt d S t) / Real.sqrt (d.cost (S.x t)) := by
    field_simp
    rw [Real.sq_sqrt hcost.le]
  have h2 : (∑ e, d.c e * S.q t e) / d.cost (S.x t)
      ≤ Real.sqrt (energyAt d S t) / Real.sqrt (d.cost (S.x t)) := by
    rw [← h3]
    exact (div_le_div_iff_of_pos_right hcost).2 hcq
  have h4 : Real.sqrt (energyAt d S t) / Real.sqrt (d.cost (S.x t))
      = Real.sqrt (energyAt d S t / d.cost (S.x t)) := by
    rw [Real.sqrt_div]
  rw [h4] at h2
  linarith

end Bonnifaci

