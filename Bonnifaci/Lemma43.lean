/- Copyright (c) 2026 MultiAgency bonifaci-lane. -/
import Bonnifaci.Feasibility
import Bonnifaci.Lemma41
import Bonnifaci.Duality

noncomputable section

/-!
# Lemma 4.3 (P3): the KL derivative bound

`d/dt KL(ξ*, ξ(t)) ≤ √(ℰ(t)/cost(x(t))) − ℰ(t)/opt`

Assembly (all real arithmetic; campaign constraint (a) holds):
* `kl_deriv_sum` — differentiating the split form termwise gives
  `d/dt Σ_e ξ*_e ln(x*_e/x_e(t)) = Σ_e ξ*_e (1 − q_e/x_e)`;
* Lemma 4.2 (`lem42_core`) turns that sum into `1 − ℰ/opt`;
* Lemma 4.1 (`cost_log_deriv_le`) bounds the cost term;
* `sum_cq_le` converts `(Σ c_e q_e)/cost` into `√(ℰ/cost)`.

**Fidelity subtlety, handled explicitly.** The *per-term* identity
`d/dt ln(x*_e/x_e(t)) = 1 − q_e/x_e` is FALSE when `x*_e = 0`: Lean's `log 0 = 0`
makes the left side `0` while the right side stays `1 − q/x`. The *weighted* identity
survives because `ξ*_e = c_e x*_e/opt = 0` kills that summand. Hence the case split
belongs inside the sum, not in a standalone per-term lemma.
-/

open Finset Real

namespace Bonnifaci

variable {N E : Type*} [Fintype N] [Fintype E]

/-- `d/dt Σ_e ξ*_e ln(x*_e/x_e(t)) = Σ_e ξ*_e (1 − q_e/x_e)`, with the `x*_e = 0`
summands dying on both sides. -/
theorem kl_deriv_sum (d : LPData N E) (S : d.Solution) (xstar : E → ℝ)
    (hxstar : d.IsFeasible xstar) (t : ℝ) :
    deriv (fun u => ∑ e, xiStar d xstar e * Real.log (xstar e / S.x u e)) t
      = ∑ e, xiStar d xstar e * (1 - S.q t e / S.x t e) := by
  have hterm : ∀ e, DifferentiableAt ℝ
      (fun u => xiStar d xstar e * Real.log (xstar e / S.x u e)) t := by
    intro e
    by_cases hxe : xstar e = 0
    · have hzero : (fun u => xiStar d xstar e * Real.log (xstar e / S.x u e)) = fun _ => 0 := by
        funext u
        simp [xiStar, hxe]
      rw [hzero]
      exact differentiableAt_const 0
    · have hq : DifferentiableAt ℝ (fun u => xstar e / S.x u e) t :=
        (differentiableAt_const (xstar e)).div (S.hdiff t e) (ne_of_gt (S.hpos t e))
      have hqne : xstar e / S.x t e ≠ 0 := div_ne_zero hxe (ne_of_gt (S.hpos t e))
      exact (differentiableAt_const (xiStar d xstar e)).mul (hq.log hqne)
  rw [deriv_finset_sum (f := fun e u => xiStar d xstar e * Real.log (xstar e / S.x u e)) hterm]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hxe : xstar e = 0
  · -- the summand is identically zero, and so is its weight
    have hzero : (fun u => xiStar d xstar e * Real.log (xstar e / S.x u e)) = fun _ => 0 := by
      funext u
      simp [xiStar, hxe]
    rw [hzero, deriv_const]
    simp [xiStar, hxe]
  · -- x*_e > 0: differentiate `ln(x*/x_e)` as `ln x* − ln x_e`
    have hxpos : 0 < xstar e := lt_of_le_of_ne (hxstar.1 e) (Ne.symm hxe)
    have hxd : DifferentiableAt ℝ (fun u => S.x u e) t := S.hdiff t e
    have hxne : S.x t e ≠ 0 := ne_of_gt (S.hpos t e)
    have hlogx : deriv (fun u => Real.log (S.x u e)) t = (S.q t e - S.x t e) / S.x t e := by
      have h := (hxd.hasDerivAt.log hxne).deriv
      rw [h, S.hode t e]
    have hsplit : (fun u => Real.log (xstar e / S.x u e))
        = fun u => Real.log (xstar e) - Real.log (S.x u e) := by
      funext u
      rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt (S.hpos u e))]
    have hratio : deriv (fun u => Real.log (xstar e / S.x u e)) t
        = 1 - S.q t e / S.x t e := by
      have hfun : (fun u => Real.log (xstar e) - Real.log (S.x u e))
          = (fun _ => Real.log (xstar e)) - fun u => Real.log (S.x u e) := rfl
      rw [hsplit, hfun, deriv_sub (differentiableAt_const (Real.log (xstar e)))
        (hxd.log hxne), deriv_const, hlogx]
      field_simp
      ring
    have hq : DifferentiableAt ℝ (fun u => Real.log (xstar e / S.x u e)) t :=
      ((differentiableAt_const (xstar e)).div (S.hdiff t e) hxne).log
        (div_ne_zero hxe hxne)
    rw [deriv_const_mul (xiStar d xstar e) hq, hratio]

/-- Differentiability of the KL sum piece (shared with the assembly below). -/
theorem differentiable_kl_sum (d : LPData N E) (S : d.Solution) (xstar : E → ℝ)
    (hxstar : d.IsFeasible xstar) :
    Differentiable ℝ (fun u => ∑ e, xiStar d xstar e * Real.log (xstar e / S.x u e)) := by
  intro t
  refine differentiableAt_finset_sum fun e => ?_
  by_cases hxe : xstar e = 0
  · have hzero : (fun u => xiStar d xstar e * Real.log (xstar e / S.x u e)) = fun _ => 0 := by
      funext u
      simp [xiStar, hxe]
    rw [hzero]
    exact differentiableAt_const 0
  · have hq : DifferentiableAt ℝ (fun u => xstar e / S.x u e) t :=
      (differentiableAt_const (xstar e)).div (S.hdiff t e) (ne_of_gt (S.hpos t e))
    have hqne : xstar e / S.x t e ≠ 0 := div_ne_zero hxe (ne_of_gt (S.hpos t e))
    exact (differentiableAt_const (xiStar d xstar e)).mul (hq.log hqne)

/-- **Lemma 4.3 (P3)**: along the trajectory,
`d/dt KL(ξ*, ξ(t)) ≤ √(ℰ(t)/cost(x(t))) − ℰ(t)/opt`.

Assembled from `kl_deriv_sum` + Lemma 4.2 (`lem42_core`) for the entropy sum and
Lemma 4.1 (`cost_log_deriv_le`) for the cost term. The feasible start hypothesis is
P1, already discharged by `feasibility_invariant`. -/
theorem kl_deriv_le (d : LPData N E) (S : d.Solution) (xstar : E → ℝ)
    (hxstar : d.IsFeasible xstar) (hbnz : ∃ n, d.b n ≠ 0)
    (hstart : d.IsFeasible (S.x 0)) (t : ℝ) (hopt : 0 < d.cost xstar) :
    deriv (fun u => KL (xiStar d xstar) (xiAt d S u)) t
      ≤ Real.sqrt (energyAt d S t / d.cost (S.x t)) - energyAt d S t / d.cost xstar := by
  have hfeas : ∀ u, d.IsFeasible (S.x u) := fun u => feasibility_invariant d S hstart u
  have hcost : 0 < d.cost (S.x t) := cost_pos d hbnz (hfeas t)
  have hKL : (fun u => KL (xiStar d xstar) (xiAt d S u))
      = fun u => (∑ e, xiStar d xstar e * Real.log (xstar e / S.x u e))
          + Real.log (d.cost (S.x u) / d.cost xstar) :=
    funext fun u => kl_split d S xstar hxstar hbnz hfeas u
  have hbridge : (fun u => (∑ e, xiStar d xstar e * Real.log (xstar e / S.x u e))
          + Real.log (d.cost (S.x u) / d.cost xstar))
      = (fun u => ∑ e, xiStar d xstar e * Real.log (xstar e / S.x u e))
        + fun u => Real.log (d.cost (S.x u) / d.cost xstar) := rfl
  rw [hKL, hbridge, deriv_add (differentiable_kl_sum d S xstar hxstar t)
    (differentiable_log_cost d S xstar hxstar hbnz hfeas t),
    kl_deriv_sum d S xstar hxstar t]
  have hsum_eq : (∑ e, xiStar d xstar e * (1 - S.q t e / S.x t e))
      = 1 - energyAt d S t / d.cost xstar := by
    have h42 := lem42_core d S xstar hxstar hbnz t
    have hneg : (∑ e, xiStar d xstar e * (1 - S.q t e / S.x t e))
        = - (∑ e, xiStar d xstar e * (S.q t e / S.x t e - 1)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      ring
    rw [hneg, h42]
    ring
  have hlogbound := cost_log_deriv_le d S xstar t hcost hopt
  rw [hsum_eq]
  linarith [hlogbound]

/-- **Theorem 1.1 with every premise discharged.** The only hypothesis left is the
paper's own feasible starting condition; P1 is applied (`feasibility_invariant`), P2 is
`cost_log_deriv_le`, P3 is `kl_deriv_le`. -/
theorem thm11_final (d : LPData N E) (hbnz : ∃ n, d.b n ≠ 0) (S : d.Solution)
    (hstart : d.IsFeasible (S.x 0))
    (xstar : E → ℝ) (hxstar : d.IsFeasible xstar)
    (hopt : ∀ y, d.IsFeasible y → d.cost xstar ≤ d.cost y)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ)
    (ht : (6 / ε) * Phi d S xstar 0 ≤ t) :
    d.cost (S.x t) ≤ (1 + ε) * d.cost xstar :=
  thm11 d hbnz S
    (fun u => feasibility_invariant d S hstart u)
    xstar hxstar hopt
    (fun u => cost_log_deriv_le d S xstar u
      (cost_pos d hbnz (feasibility_invariant d S hstart u)) (cost_pos d hbnz hxstar))
    (fun u => kl_deriv_le d S xstar hxstar hbnz hstart u (cost_pos d hbnz hxstar))
    hε0 hε1 t ht

end Bonnifaci
