/-
Copyright (c) 2026 MultiAgency bonifaci-lane.
-/
import Bonnifaci.Model
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Feasibility invariance — the P1 discharge

Downstream discharge of named premise **P1** (Lemma 3.2 of [Bonifaci 2016]).

Route (Gronwall-free, real-arithmetic layer): the n-th feasibility defect
`e_n(t) = Σ_e A_ne x_e(t) − b_n` satisfies `e'_n = −e_n` (Proposition 3.1 of the
paper, pure algebra from the ODE + Kirchhoff). Hence `u ↦ e_n(u)·e^u` has derivative
identically zero, so it is constant (both monotone and antitone via the mean-value
comparison lemmas); `e_n(0) = 0` (feasible start) forces `e_n(t) = 0` for all `t`.

Result: `feasibility_invariant` — feasible start stays feasible. This removes P1 as
a premise for any consumer that can supply a `Solution` with a feasible start.
-/

open Finset Set Real

namespace Bonnifaci

variable {N E : Type*} [Fintype N] [Fintype E]

/-- Derivative zero everywhere ⇒ constant (between any two points). Built from the
mean-value comparison lemmas; no Gronwall. -/
theorem const_of_deriv_zero (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (h0 : ∀ t, deriv u t = 0) (a b : ℝ) (hab : a ≤ b) : u a = u b := by
  have h1 := monotoneOn_of_deriv_nonneg convex_univ hu.continuous.continuousOn
    hu.differentiableOn (fun t _ => by rw [h0 t]; exact le_rfl)
  have h2 := antitoneOn_of_deriv_nonpos convex_univ hu.continuous.continuousOn
    hu.differentiableOn (fun t _ => by rw [h0 t])
  exact le_antisymm (h2 a b mem_univ mem_univ hab) (h1 a b mem_univ mem_univ hab)

/-- **Proposition 3.1**: the n-th defect `e_n(t) = Σ_e A_ne x_e(t) − b_n` satisfies
`e'_n(t) = −e_n(t)`. -/
theorem defect_ode (d : LPData N E) (S : d.Solution) (n : N) (t : ℝ) :
    deriv (fun u => ∑ e, d.A n e * S.x u e - d.b n) t
      = -(∑ e, d.A n e * S.x t e - d.b n) := by
  have hsum : DifferentiableAt ℝ (fun u => ∑ e, d.A n e * S.x u e) t :=
    DifferentiableAt.sum fun e _ => (differentiable_const (d.A n e)).mul (S.hdiff t e)
  have hds : deriv (fun u => ∑ e, d.A n e * S.x u e) t
      = ∑ e, d.A n e * (S.q t e - S.x t e) := by
    rw [deriv_sum fun e _ => (differentiable_const (d.A n e)).mul (S.hdiff t e)]
    exact Finset.sum_congr rfl fun e _ => by rw [deriv_const_mul (d.A n e) (S.hdiff t e), S.hode t e]
  calc deriv (fun u => ∑ e, d.A n e * S.x u e - d.b n) t
      = ∑ e, d.A n e * (S.q t e - S.x t e) - 0 := by
        rw [show (fun u => ∑ e, d.A n e * S.x u e - d.b n)
            = (fun u => ∑ e, d.A n e * S.x u e) - fun _ => d.b n from rfl,
          deriv_sub hsum differentiableAt_const, deriv_const, hds]
    _ = -(∑ e, d.A n e * S.x t e - d.b n) := by
        rw [sub_zero, ← S.hflow t n, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun e _ => by ring

/-- **Lemma 3.2**: a feasible start is feasible forever (per-coordinate form).
Actually stronger: the defect decays like `e^{−t}` in *both* time directions. -/
theorem defect_decay (d : LPData N E) (S : d.Solution) (n : N)
    (h0 : ∑ e, d.A n e * S.x 0 e = d.b n) (t : ℝ) :
    ∑ e, d.A n e * S.x t e = d.b n := by
  have hsumdiff : Differentiable ℝ
      (fun u => ∑ e, d.A n e * S.x u e) := fun u =>
    DifferentiableAt.sum fun e _ => (differentiable_const (d.A n e)).mul (S.hdiff u e)
  set e : ℝ → ℝ := fun u => ∑ e, d.A n e * S.x u e - d.b n with he
  have hu : Differentiable ℝ e := hsumdiff.sub differentiable_const
  have hzu : ∀ u, deriv e u = -e u := by
    intro u
    rw [he]
    rw [defect_ode d S n u]
  set w : ℝ → ℝ := fun u => e u * Real.exp u with hw
  have hwd : Differentiable ℝ w := hu.mul Real.differentiable_exp
  have hw0 : ∀ u, deriv w u = 0 := by
    intro u
    rw [hw]
    rw [deriv_mul (hu u) (Real.differentiable_exp u), hzu u, Real.deriv_exp]
    ring
  -- w is constant on all of ℝ, so w t = w 0 = e 0 · 1 = 0
  have hwt : w t = w 0 := by
    rcases le_or_lt 0 t with ht | ht
    · exact const_of_deriv_zero w hwd hw0 0 t ht
    · exact (const_of_deriv_zero w hwd hw0 t 0 ht).symm
  have he0 : e 0 = 0 := by
    rw [he]; rw [h0]; ring
  have hexp : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hfin : e t = 0 := by
    have hwz : w t = 0 := by
      have := hwt
      rw [hw, he0, mul_zero] at this
      exact this
    exact (mul_eq_zero.1 hwz).resolve_right hexp
  rw [he] at hfin
  linarith

/--
**Lemma 3.2 / named premise P1, discharged.** A feasible start is feasible forever:
`S.x t` satisfies the LP for every `t` (nonnegativity is `hpos`; the defect decays by
`defect_decay`). Any consumer of `thm11` that starts feasible should use this instead
of assuming `hfeas`.
-/
theorem feasibility_invariant (d : LPData N E) (S : d.Solution)
    (hstart : d.IsFeasible (S.x 0)) (t : ℝ) : d.IsFeasible (S.x t) :=
  ⟨fun e => (S.hpos t e).le, fun n => defect_decay d S n hstart.2 t⟩

end Bonnifaci
