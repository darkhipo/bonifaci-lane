/- Copyright (c) 2026 MultiAgency bonifaci-lane. -/
import Bonnifaci.Lemma43

noncomputable section

/-!
# M5: the mu-corollary (second half of Theorem 1.1)

KL(xi*, xi(0)) <= ln mu + ln(cost(x(0))/opt),   mu = max_j x*_j/x_j(0)

**Statement shape.** Rather than plumb Finset.sup (and its nonempty-index edge case),
mu enters as *any* upper bound on the ratios x*_e/x_e(0) - exactly the property the max
is used for. Discharging this into the literal max_j is bookkeeping, not mathematics.

The bound is evaluated at time 0, which is what makes it true without any monotonicity
of the tubes: at t = 0 we have x_e(0)/x_e(0) = 1 <= mu by construction.
-/

open Finset Real

namespace Bonnifaci

variable {N E : Type*} [Fintype N] [Fintype E]

/- Every summand of the entropy term is at most xi*_e * ln mu (the x*_e = 0 summand
vanishes on both sides). -/
theorem entropy_summand_le (d : LPData N E) (S : d.Solution) {xstar : E → ℝ}
    (hxstar : d.IsFeasible xstar) (hoptpos : 0 < d.cost xstar)
    {mu : ℝ} (hmu : ∀ e, xstar e / S.x 0 e ≤ mu) (e : E) :
    xiStar d xstar e * Real.log (xstar e / S.x 0 e)
      ≤ xiStar d xstar e * Real.log mu := by
  by_cases hxe : xstar e = 0
  · simp [xiStar, hxe]
  · have hxpos : 0 < xstar e := lt_of_le_of_ne (hxstar.1 e) (Ne.symm hxe)
    have hrpos : 0 < xstar e / S.x 0 e := div_pos hxpos (S.hpos 0 e)
    have hw : 0 ≤ xiStar d xstar e :=
      div_nonneg (mul_nonneg (d.hc e).le (hxstar.1 e)) hoptpos.le
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hrpos (hmu e)) hw

/- **The mu-corollary**: KL(xi*, xi(0)) <= ln mu + ln(cost(x(0))/opt). -/
theorem kl_bound_mu (d : LPData N E) (S : d.Solution) (xstar : E → ℝ)
    (hxstar : d.IsFeasible xstar) (hbnz : ∃ n, d.b n ≠ 0)
    (hfeas : ∀ t, d.IsFeasible (S.x t)) {mu : ℝ}
    (hmu : ∀ e, xstar e / S.x 0 e ≤ mu) :
    KL (xiStar d xstar) (xiAt d S 0)
      ≤ Real.log mu + Real.log (d.cost (S.x 0) / d.cost xstar) := by
  have hoptpos : 0 < d.cost xstar := cost_pos d hbnz hxstar
  have hsumstar := sum_xiStar d xstar hbnz hxstar
  rw [kl_split d S xstar hxstar hbnz hfeas 0]
  have hstep : (∑ e, xiStar d xstar e * Real.log (xstar e / S.x 0 e))
      ≤ ∑ e, xiStar d xstar e * Real.log mu :=
    Finset.sum_le_sum fun e _ => entropy_summand_le d S hxstar hoptpos hmu e
  have hpull : (∑ e, xiStar d xstar e * Real.log mu) = Real.log mu := by
    rw [← Finset.sum_mul, hsumstar, one_mul]
  linarith [hstep, hpull]

end Bonnifaci
