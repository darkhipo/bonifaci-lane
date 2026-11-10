/-
Copyright (c) 2026 MultiAgency bonifaci-lane.
-/
import Bonnifaci.Model

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
    (st : d.Step x) (hfp : d.IsFixedPoint x st) (e : E) :
    d.c e = ∑ n, d.A n e * st.p n := by
  have h1 : d.c e / x e * x e = d.c e := by field_simp
  have h2 : d.c e / x e * x e = ∑ n, d.A n e * st.p n := by
    rw [← st.ohm e, hfp e]
  rw [← h1, h2]

/-- Helper: at a rest point, `Σ_e c_e y_e = Σ_n p_n b_n` for every feasible `y`. -/
private theorem cost_eq_potential_inner {d : LPData N E} {x : E → ℝ} (hx : ∀ e, 0 < x e)
    (st : d.Step x) (hfp : d.IsFixedPoint x st) {y : E → ℝ} (hy : d.IsFeasible y) :
    d.cost y = ∑ n, st.p n * d.b n := by
  have htight := fixed_point_dual_tight hx st hfp
  have hbx : ∀ n, d.b n = ∑ e, d.A n e * x e := fun n => by
    rw [← st.hflow n]
    exact Finset.sum_congr rfl fun e _ => by rw [hfp e]
  have stepA : ∑ e, d.c e * y e = ∑ n, st.p n * d.b n := by
    have h1 : ∑ e, d.c e * y e = ∑ e, (∑ n, d.A n e * st.p n) * y e :=
      Finset.sum_congr rfl fun e _ => by rw [htight e]
    have h2 : ∑ e, (∑ n, d.A n e * st.p n) * y e
        = ∑ e, ∑ n, st.p n * (d.A n e * y e) := by
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [h1, h2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.mul_sum, hy.2 n]
  refine stepA.trans ?_
  have h1 : ∑ n, st.p n * d.b n = ∑ n, st.p n * ∑ e, d.A n e * x e :=
    Finset.sum_congr rfl fun n _ => by rw [hbx n]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [htight e, Finset.sum_mul]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **The identification.** At a rest point, *every* feasible point has the same cost
as the rest point — the LP value is constant on the feasible set (exactly what
`c = Aᵀ p` means). -/
theorem fixed_point_cost_eq {d : LPData N E} {x : E → ℝ} (hx : ∀ e, 0 < x e)
    (st : d.Step x) (hfp : d.IsFixedPoint x st) {y : E → ℝ} (hy : d.IsFeasible y) :
    d.cost y = d.cost x := by
  rw [cost_eq_potential_inner hx st hfp hy, cost_eq_potential_inner hx st hfp hy]

/-- **Fixed point ⇒ LP-optimality** (finite case): the rest point is optimal for
`min cᵀy s.t. A y = b, y ≥ 0`. -/
theorem fixed_point_lp_optimal {d : LPData N E} {x : E → ℝ} (hx : ∀ e, 0 < x e)
    (st : d.Step x) (hfp : d.IsFixedPoint x st) {y : E → ℝ} (hy : d.IsFeasible y) :
    d.cost x ≤ d.cost y := by
  rw [fixed_point_cost_eq hx st hfp hy]

end Bonnifaci
