/- Copyright (c) 2026 MultiAgency bonifaci-lane. -/
import Bonnifaci.Model

noncomputable section

/-!
# Fixed point = LP optimum: the convex-duality identification

The convex-duality half of the scoped target: at a rest point of the dynamics, the
Kirchhoff potentials certify LP optimality of the tube vector.

**Statement fidelity note (measured against the primary source).** At a rest point
with `q = x`, Ohm's law `R q = Aᵀ p` forces `Aᵀ p = c` *exactly* — i.e. a rest point
in the interior exists only when the cost vector lies in the row space of `A`
(tension-free potentials; in the unit-simplex case of the paper's §5, constant `c`).
Then every feasible point has the *same* cost as the rest point, and `x` is trivially
optimal. This is the honest algebraic content of the identification; the boundary
case — where the dynamics only approaches optimality while thinning off-support
tubes — is carried by the KL potential of Theorem 1.1, not by exact rest points.
Both facts are stated below, with the constant-cost consequence made explicit.

Layer discipline: the only input is the `Step` bundle (Kirchhoff + Ohm + Thomson),
i.e. real arithmetic. No comparison-addition model appears.
-/

namespace Bonnifaci

variable {N E : Type*} [Fintype N] [Fintype E]

/-- At a rest point, Ohm's law makes the potentials an *exactly tight* dual
certificate: `c = Aᵀ p`. -/
theorem fixed_point_dual_tight {d : LPData N E} {x : E → ℝ} (hx : ∀ e, 0 < x e)
    (st : LPData.Step d x) (hfp : d.IsFixedPoint x st) (e : E) :
    d.c e = ∑ n, d.A n e * st.p n := by
  have h1 : d.c e / x e * x e = d.c e := by
    rw [div_mul_cancel₀ _ (ne_of_gt (hx e))]
  have h2 : d.c e / x e * x e = ∑ n, d.A n e * st.p n := by
    rw [← st.ohm e, hfp e]
  exact h1.symm.trans h2

/-- Helper: at a rest point, the cost of *any* feasibility-respecting `z` collapses to
the potential inner product `Σ_n p_n b_n` — the dual objective is attainable. -/
private theorem cost_eq_potential_inner {d : LPData N E} {x : E → ℝ} (hx : ∀ e, 0 < x e)
    (st : LPData.Step d x) (hfp : d.IsFixedPoint x st) {y : E → ℝ} (hy : d.IsFeasible y) :
    d.cost y = d.cost x := by
  have htight := fixed_point_dual_tight hx st hfp
  have hbx : ∀ n, d.b n = ∑ e, d.A n e * x e := fun n => by
    rw [← st.hflow n]
    exact Finset.sum_congr rfl fun e _ => by rw [hfp e]
  have key : ∀ z : E → ℝ, (∀ n, ∑ e, d.A n e * z e = d.b n) →
      d.cost z = ∑ n, st.p n * d.b n := by
    intro z hz
    calc d.cost z = ∑ e, d.c e * z e := rfl
      _ = ∑ e, (∑ n, d.A n e * st.p n) * z e := by
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [htight e]
      _ = ∑ e, ∑ n, st.p n * (d.A n e * z e) := by
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun n _ => by ring
      _ = ∑ n, ∑ e, st.p n * (d.A n e * z e) := Finset.sum_comm
      _ = ∑ n, st.p n * ∑ e, d.A n e * z e := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
      _ = ∑ n, st.p n * d.b n := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [hz n]
  rw [key y hy.2, key x fun n => (hbx n).symm]

/-- **The identification.** At a rest point, *every* feasible point has the same cost
as the rest point — the LP value is constant on the feasible set (exactly what
`c = Aᵀ p` means). -/
theorem fixed_point_cost_eq {d : LPData N E} {x : E → ℝ} (hx : ∀ e, 0 < x e)
    (st : LPData.Step d x) (hfp : d.IsFixedPoint x st) {y : E → ℝ} (hy : d.IsFeasible y) :
    d.cost y = d.cost x :=
  cost_eq_potential_inner hx st hfp hy

/-- **Fixed point ⇒ LP-optimality** (finite case): the rest point is optimal for
`min cᵀy s.t. A y = b, y ≥ 0`. -/
theorem fixed_point_lp_optimal {d : LPData N E} {x : E → ℝ} (hx : ∀ e, 0 < x e)
    (st : LPData.Step d x) (hfp : d.IsFixedPoint x st) {y : E → ℝ} (hy : d.IsFeasible y) :
    d.cost x ≤ d.cost y := by
  rw [fixed_point_cost_eq hx st hfp hy]

end Bonnifaci
