/- Copyright (c) 2026 MultiAgency bonifaci-lane. -/
import Bonnifaci.Model
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

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

open Finset Set

namespace Bonnifaci

variable {N E : Type*} [Fintype N] [Fintype E]

/-- Derivative zero everywhere ⇒ constant (between any two points). Built from the
mean-value comparison lemmas; no Gronwall. -/
theorem const_of_deriv_zero (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (h0 : ∀ t, deriv u t = 0) (a b : ℝ) (hab : a ≤ b) : u a = u b := by
  have h1 : MonotoneOn u univ :=
    monotoneOn_of_deriv_nonneg convex_univ hu.continuous.continuousOn
      (by rw [interior_univ]; exact hu.differentiableOn) (fun t _ => by simp [h0 t])
  have h2 : AntitoneOn u univ :=
    antitoneOn_of_deriv_nonpos convex_univ hu.continuous.continuousOn
      (by rw [interior_univ]; exact hu.differentiableOn) (fun t _ => by simp [h0 t])
  exact le_antisymm (h1 (Set.mem_univ a) (Set.mem_univ b) hab)
    (h2 (Set.mem_univ a) (Set.mem_univ b) hab)

/-- **Proposition 3.1**: the n-th defect `e_n(t) = Σ_e A_ne x_e(t) − b_n` satisfies
`e'_n(t) = −e_n(t)`. -/
theorem defect_ode (d : LPData N E) (S : d.Solution) (n : N) (t : ℝ) :
    deriv (fun u => ∑ e, d.A n e * S.x u e - d.b n) t
      = -(∑ e, d.A n e * S.x t e - d.b n) := by
  have hterm : ∀ e, DifferentiableAt ℝ (fun u => d.A n e * S.x u e) t :=
    fun e => DifferentiableAt.const_mul (S.hdiff t e) (d.A n e)
  have hsum : DifferentiableAt ℝ (fun u => ∑ e, d.A n e * S.x u e) t :=
    differentiableAt_finset_sum hterm
  have hds : deriv (fun u => ∑ e, d.A n e * S.x u e) t
      = ∑ e, d.A n e * (S.q t e - S.x t e) := by
    rw [deriv_finset_sum hterm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [deriv_const_mul (d.A n e) (S.hdiff t e), S.hode t e]
  have hsub : deriv (fun u => (∑ e, d.A n e * S.x u e) - d.b n) t
      = deriv (fun u => ∑ e, d.A n e * S.x u e) t :=
    deriv_sub_const (d.b n)
  have key : ∑ e, d.A n e * (S.q t e - S.x t e)
      = -(∑ e, d.A n e * S.x t e - d.b n) := by
    rw [← S.hflow t n, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  calc deriv (fun u => ∑ e, d.A n e * S.x u e - d.b n) t
      = deriv (fun u => (∑ e, d.A n e * S.x u e) - d.b n) t := rfl
    _ = deriv (fun u => ∑ e, d.A n e * S.x u e) t := hsub
    _ = ∑ e, d.A n e * (S.q t e - S.x t e) := hds
    _ = -(∑ e, d.A n e * S.x t e - d.b n) := key

/-- **Lemma 3.2**: a feasible start is feasible forever (per-coordinate form).
Stronger than needed: the defect is `0` at every time. -/
theorem defect_decay (d : LPData N E) (S : d.Solution) (n : N)
    (h0 : ∑ e, d.A n e * S.x 0 e = d.b n) (t : ℝ) :
    ∑ e, d.A n e * S.x t e = d.b n := by
  have hterm : ∀ (u : ℝ) (e : E), DifferentiableAt ℝ (fun v => d.A n e * S.x v e) u :=
    fun u e => DifferentiableAt.const_mul (S.hdiff u e) (d.A n e)
  have hsumdiff : Differentiable ℝ (fun u => ∑ e, d.A n e * S.x u e) := fun u =>
    differentiableAt_finset_sum (hterm u)
  set e : ℝ → ℝ := fun u => ∑ e, d.A n e * S.x u e - d.b n with he
  have hu : Differentiable ℝ e := hsumdiff.sub (differentiable_const _)
  have hzu : ∀ u, deriv e u = -e u := by
    intro u
    rw [he]
    exact defect_ode d S n u
  set w : ℝ → ℝ := fun u => e u * Real.exp u with hw
  have hwd : Differentiable ℝ w := hu.mul Real.differentiable_exp
  have hw0 : ∀ u, deriv w u = 0 := by
    intro u
    have hfun : (fun v : ℝ => e v * Real.exp v) = e * Real.exp := rfl
    rw [hw, hfun, deriv_mul (hu u) (Real.differentiable_exp u), hzu u, Real.deriv_exp]
    ring
  have hwt : w t = w 0 := by
    rcases le_or_gt 0 t with ht | ht
    · exact (const_of_deriv_zero w hwd hw0 0 t ht).symm
    · exact const_of_deriv_zero w hwd hw0 t 0 ht.le
  have he0 : e 0 = 0 := by
    show (∑ e, d.A n e * S.x 0 e) - d.b n = 0
    rw [h0]; ring
  have hexp : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hfin : e t = 0 := by
    have hwz : w t = 0 := by
      have h0' : w 0 = 0 := by
        show e 0 * Real.exp 0 = 0
        rw [he0, zero_mul]
      rw [hwt, h0']
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
  ⟨fun e => (S.hpos t e).le, fun n => defect_decay d S n (hstart.2 n) t⟩

end Bonnifaci
