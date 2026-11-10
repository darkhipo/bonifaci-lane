/- Copyright (c) 2026 MultiAgency bonifaci-lane. -/
import Bonnifaci.Model
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

/-!
# Structural features of the Physarum trajectory

**Edges never retire** (campaign constraint (b), stated as a theorem): along a solution
trajectory with nonnegative electrical flow — automatically true in the network case,
where `q` is the flow magnitude — every tube diameter stays above its initial value
times `e^{-t}`:

`x_e(t) ≥ x_e(0) · e^{-t}`.

Consequence: the frozen-lock pathology (tubes dying in a locked configuration) is
*structurally excluded* in this model; the sibling widgets lane's frozen-lock widget
formalizes the complementary pathology for a different dynamics.

Proof: the comparison function `u ↦ x_e(u)·e^u` has derivative `q_e(u)·e^u ≥ 0`,
hence is monotone; monotonicity between `0` and `t` gives the claim. This uses only
the ODE + nonnegativity of `q` + differentiability — no Gronwall machinery.
-/

open Set

namespace Bonnifaci

variable {N E : Type*} [Fintype N] [Fintype E]

/-- **Edges never retire.** If the electrical flow is nonnegative along the trajectory
(network case), then `x_e(0) · e^{-t} ≤ x_e(t)` for all `t ≥ 0`. -/
theorem edge_no_retirement (d : LPData N E) (S : d.Solution) (e : E)
    (hq : ∀ t, 0 ≤ S.q t e) {t : ℝ} (ht : 0 ≤ t) : S.x 0 e * Real.exp (-t) ≤ S.x t e := by
  set f : ℝ → ℝ := fun u => S.x u e * Real.exp u with hf
  have hxdiff : Differentiable ℝ (fun u => S.x u e) := fun u => S.hdiff u e
  have hdiff : Differentiable ℝ f := hxdiff.mul Real.differentiable_exp
  have hder : ∀ u, 0 ≤ deriv f u := by
    intro u
    have h1 : deriv f u = (S.q u e - S.x u e) * Real.exp u + S.x u e * Real.exp u := by
      have hfun : (fun u : ℝ => S.x u e * Real.exp u) = (fun u => S.x u e) * Real.exp := rfl
      rw [hf, hfun, deriv_mul (S.hdiff u e) (Real.differentiable_exp u), S.hode u e, Real.deriv_exp]
    rw [h1]
    have hu : 0 < Real.exp u := Real.exp_pos u
    nlinarith [hq u, hu]
  have hmono : MonotoneOn f univ :=
    monotoneOn_of_deriv_nonneg convex_univ hdiff.continuous.continuousOn
      (by rw [interior_univ]; exact hdiff.differentiableOn) fun u _ => hder u
  have h1 : f 0 ≤ f t := hmono (Set.mem_univ 0) (Set.mem_univ t) ht
  calc S.x 0 e * Real.exp (-t)
      = f 0 * Real.exp (-t) := by rw [hf]; simp
    _ ≤ f t * Real.exp (-t) := mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg (-t))
    _ = S.x t e := by
        have hfun : (fun u : ℝ => S.x u e * Real.exp u) = (fun u => S.x u e) * Real.exp := rfl
        rw [hf, hfun]
        show S.x t e * Real.exp t * Real.exp (-t) = S.x t e
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

end Bonnifaci
