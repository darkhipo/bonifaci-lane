/-
Copyright (c) 2026 MultiAgency bonifaci-lane.
-/
import Bonnifaci.Thm11

noncomputable section

/-!
# The duality sandwich (Lemmas 4.2 core, downstream of P3)

The algebraic core needed to discharge named premise **P3** (the KL derivative bound,
Lemma 4.3 of [Bonifaci 2016]): the *exact* identity behind Lemma 4.2,

`d/dt Σ_j (c_j x*_j / opt) ln(x*_j / x_j(t)) = 1 − ℰ/opt`,

reduces (after the derivative computation, which lives in the trajectory calculus) to
the two pure-algebra facts proved here:

1. `duality_inner` — `pᵀb = ℰ` (Proposition 2.2 of the paper): potentials pair with
   the demand to give the energy.
2. `xstar_Rq_eq` — `x*ᵀ R q = bᵀ p` (Proposition 2.3 + Ohm): the optimal flow pairs
   with the electrical flow through the potentials.

Together: `Σ ξ*_j (q_j/x_j − 1) = ℰ/opt − 1` (`lem42_core`). Layer discipline:
finite sums over ℝ only; the Laplacian solve is still quarantined in `Solution`.
-/

open Finset

namespace Bonnifaci

variable {N E : Type*} [Fintype N] [Fintype E]

/-- **Proposition 2.2**: `p(t)ᵀ b = ℰ(t)`. -/
theorem duality_inner (d : LPData N E) (S : d.Solution) (t : ℝ) :
    ∑ n, S.p t n * d.b n = d.energyAt S t := by
  have h1 : ∑ n, S.p t n * d.b n = ∑ n, S.p t n * ∑ e, d.A n e * S.q t e :=
    Finset.sum_congr rfl fun n _ => by rw [S.hflow t n]
  have h2 : ∑ n, S.p t n * ∑ e, d.A n e * S.q t e
      = ∑ e, S.q t e * ∑ n, S.p t n * d.A n e := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    calc ∑ n, S.p t n * (d.A n e * S.q t e)
        = ∑ n, S.q t e * (S.p t n * d.A n e) := Finset.sum_congr rfl fun n _ => by ring
      _ = S.q t e * ∑ n, S.p t n * d.A n e := (Finset.mul_sum _ _).symm
  have h3 : ∑ e, S.q t e * ∑ n, S.p t n * d.A n e
      = ∑ e, S.q t e * (d.c e / S.x t e * S.q t e) :=
    Finset.sum_congr rfl fun e _ => by rw [S.ohm t e]
  calc ∑ n, S.p t n * d.b n = ∑ n, S.p t n * ∑ e, d.A n e * S.q t e := h1
    _ = ∑ e, S.q t e * ∑ n, S.p t n * d.A n e := h2
    _ = ∑ e, S.q t e * (d.c e / S.x t e * S.q t e) := h3
    _ = d.energyAt S t := by
        refine Finset.sum_congr rfl fun e _ => ?_
        ring

/-- **Proposition 2.3 (+ Ohm)**: `x*ᵀ R(t) q(t) = p(t)ᵀ b` for feasible `x*`. -/
theorem xstar_Rq_eq (d : LPData N E) (S : d.Solution) (xstar : E → ℝ)
    (hxstar : d.IsFeasible xstar) (t : ℝ) :
    ∑ e, xstar e * (d.c e / S.x t e * S.q t e) = ∑ n, S.p t n * d.b n := by
  calc ∑ e, xstar e * (d.c e / S.x t e * S.q t e)
      = ∑ e, xstar e * ∑ n, S.p t n * d.A n e :=
        Finset.sum_congr rfl fun e _ => by rw [S.ohm t e]
    _ = ∑ n, S.p t n * ∑ e, d.A n e * xstar e := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.mul_sum, hxstar.2 n]
    _ = ∑ n, S.p t n * d.b n :=
        Finset.sum_congr rfl fun n _ => by rw [hxstar.2 n]

/-- **Lemma 4.2 core** (algebraic identity behind the KL derivative):
`Σ_e ξ*_e · (q_e/x_e − 1) = ℰ/opt − 1`.
The Lemma 4.2 statement `d/dt Σ ξ*_e ln(x*_e/x_e(t)) = 1 − ℰ/opt` follows from this
plus the chain rule along the trajectory, which is exactly the P3 discharge. -/
theorem lem42_core (d : LPData N E) (S : d.Solution) (xstar : E → ℝ)
    (hxstar : d.IsFeasible xstar) (hbnz : ∃ n, d.b n ≠ 0)
    (hfeas : ∀ t, d.IsFeasible (S.x t)) (t : ℝ) :
    ∑ e, d.xiStar xstar e * (S.q t e / S.x t e - 1)
      = d.energyAt S t / d.cost xstar - 1 := by
  have hoptpos : 0 < d.cost xstar := d.cost_pos hbnz hxstar
  have hsumstar := d.sum_xiStar xstar hbnz hxstar
  have hsplit : ∑ e, d.xiStar xstar e * (S.q t e / S.x t e - 1)
      = ∑ e, d.xiStar xstar e * (S.q t e / S.x t e)
        - ∑ e, d.xiStar xstar e := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hkey : ∑ e, d.xiStar xstar e * (S.q t e / S.x t e)
      = d.energyAt S t / d.cost xstar := by
    have hstep : ∑ e, d.xiStar xstar e * (S.q t e / S.x t e)
        = ∑ e, xstar e * (d.c e / S.x t e * S.q t e) / d.cost xstar := by
      refine Finset.sum_congr rfl fun e _ => ?_
      have hce := (d.hc e).ne'
      have hxe := (S.hpos t e).ne'
      have hco := (d.cost_pos hbnz hxstar).ne'
      unfold xiStar
      field_simp [hce, hxe, hco]
    rw [hstep, ← Finset.sum_div, xstar_Rq_eq d S xstar hxstar t, d.duality_inner S t]
  rw [hsplit, hkey, hsumstar]

end Bonnifaci
