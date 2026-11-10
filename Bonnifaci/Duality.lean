/- Copyright (c) 2026 MultiAgency bonifaci-lane. -/
import Bonnifaci.Thm11

noncomputable section

/-!
# The duality sandwich (Propositions 2.2 and 2.3, Lemma 4.2 core)

The convex-duality content that Lemma 4.3 rides on. All three statements are pure
finite algebra over `∑` and the two structural facts of the model (`hflow` =
Kirchhoff, `ohm` = Ohm), i.e. real arithmetic — no Laplacian solve, no
comparison-addition (campaign constraint (a)).

* `duality_inner` — Proposition 2.2: `p(t)ᵀ b = ℰ(t)`.
* `xstar_Rq_eq` — Proposition 2.3 + Ohm: `x*ᵀ R(t) q(t) = p(t)ᵀ b`.
* `lem42_core` — Lemma 4.2: `d/dt Σ_j (c_j x*_j/opt) ln(x*_j/x_j)` has the identity
  `Σ_j ξ*_j (q_j/x_j − 1) = ℰ/opt − 1` (the time derivative, algebraically).
-/

open Finset Real

namespace Bonnifaci

variable {N E : Type*} [Fintype N] [Fintype E]

/-- **Proposition 2.2**: `p(t)ᵀ b = ℰ(t)`. -/
theorem duality_inner (d : LPData N E) (S : d.Solution) (t : ℝ) :
    ∑ n, S.p t n * d.b n = energyAt d S t := by
  have h3 : ∀ e, ∑ n, S.p t n * d.A n e = d.c e / S.x t e * S.q t e := by
    intro e
    calc ∑ n, S.p t n * d.A n e = ∑ n, d.A n e * S.p t n :=
          Finset.sum_congr rfl fun n _ => by ring
      _ = d.c e / S.x t e * S.q t e := by rw [← S.ohm t e]
  calc ∑ n, S.p t n * d.b n
      = ∑ n, S.p t n * ∑ e, d.A n e * S.q t e := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [S.hflow t n]
    _ = ∑ n, ∑ e, S.p t n * (d.A n e * S.q t e) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ e, ∑ n, S.p t n * (d.A n e * S.q t e) := Finset.sum_comm
    _ = ∑ e, (∑ n, S.p t n * d.A n e) * S.q t e := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun n _ => by ring
    _ = energyAt d S t := by
          unfold energyAt
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [h3 e]
          ring

/-- **Proposition 2.3 (+ Ohm)**: `x*ᵀ R(t) q(t) = p(t)ᵀ b` for feasible `x*`. -/
theorem xstar_Rq_eq (d : LPData N E) (S : d.Solution) (xstar : E → ℝ)
    (hxstar : d.IsFeasible xstar) (t : ℝ) :
    ∑ e, xstar e * (d.c e / S.x t e * S.q t e) = ∑ n, S.p t n * d.b n := by
  have hterm : ∀ e, xstar e * (d.c e / S.x t e * S.q t e)
      = ∑ n, S.p t n * (d.A n e * xstar e) := by
    intro e
    calc xstar e * (d.c e / S.x t e * S.q t e)
        = xstar e * ∑ n, d.A n e * S.p t n := by rw [S.ohm t e]
      _ = ∑ n, xstar e * (d.A n e * S.p t n) := by rw [Finset.mul_sum]
      _ = ∑ n, S.p t n * (d.A n e * xstar e) :=
          Finset.sum_congr rfl fun n _ => by ring
  calc ∑ e, xstar e * (d.c e / S.x t e * S.q t e)
      = ∑ e, ∑ n, S.p t n * (d.A n e * xstar e) :=
          Finset.sum_congr rfl fun e _ => hterm e
    _ = ∑ n, ∑ e, S.p t n * (d.A n e * xstar e) := Finset.sum_comm
    _ = ∑ n, S.p t n * ∑ e, d.A n e * xstar e := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ n, S.p t n * d.b n := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hxstar.2 n]

/-- **Lemma 4.2, algebraic core**: the derivative side of
`d/dt Σ_j (c_j x*_j/opt) ln(x*_j/x_j) = 1 − ℰ/opt` reads, on the trajectory,
`Σ_j ξ*_j (q_j/x_j − 1) = ℰ/opt − 1`. -/
theorem lem42_core (d : LPData N E) (S : d.Solution) (xstar : E → ℝ)
    (hxstar : d.IsFeasible xstar) (hbnz : ∃ n, d.b n ≠ 0) (t : ℝ) :
    ∑ e, xiStar d xstar e * (S.q t e / S.x t e - 1)
      = energyAt d S t / d.cost xstar - 1 := by
  have hoptpos : 0 < d.cost xstar := cost_pos d hbnz hxstar
  have hsumstar := sum_xiStar d xstar hbnz hxstar
  have hsplit : ∑ e, xiStar d xstar e * (S.q t e / S.x t e - 1)
      = ∑ e, xiStar d xstar e * (S.q t e / S.x t e) - ∑ e, xiStar d xstar e := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hstep : ∑ e, xiStar d xstar e * (S.q t e / S.x t e)
      = ∑ e, xstar e * (d.c e / S.x t e * S.q t e) / d.cost xstar := by
    refine Finset.sum_congr rfl fun e _ => ?_
    have hce := (d.hc e).ne'
    have hxe := (S.hpos t e).ne'
    have hco := hoptpos.ne'
    unfold xiStar
    field_simp
  have hstep2 : ∑ e, xstar e * (d.c e / S.x t e * S.q t e) / d.cost xstar
      = (∑ e, xstar e * (d.c e / S.x t e * S.q t e)) / d.cost xstar := by
    have hterm : ∀ e, xstar e * (d.c e / S.x t e * S.q t e) / d.cost xstar
        = xstar e * (d.c e / S.x t e * S.q t e) * (d.cost xstar)⁻¹ :=
      fun e => div_eq_mul_inv _ _
    rw [Finset.sum_congr rfl fun e _ => hterm e, ← Finset.sum_mul, div_eq_mul_inv]
  have hkey : ∑ e, xiStar d xstar e * (S.q t e / S.x t e)
      = energyAt d S t / d.cost xstar := by
    rw [hstep, hstep2, xstar_Rq_eq d S xstar hxstar t, duality_inner d S t]
  rw [hsplit, hkey, hsumstar]

end Bonnifaci
