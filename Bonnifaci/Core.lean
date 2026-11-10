/- Copyright (c) 2026 MultiAgency bonifaci-lane. -/
import Bonnifaci.KL
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section

/-!
# The analytic core of the Lyapunov decrease

Two fully proved pointwise statements that carry the quantitative heart of
[Bonifaci 2016]:

* `cs_step` — the Cauchy–Schwarz step of Lemma 4.1 (cost of the electrical flow vs.
  the energy inner product);
* `phi_decrease_core` — the algebraic core of Lemma 4.4: while the solution is
  `(1+ε)`-factor superoptimal, the potential decreases at rate at least `ε/2`.

Both are pure real arithmetic over finite index sets: no trajectories, no premises.
-/

open Finset Real

namespace Bonnifaci

/-- **Cauchy–Schwarz step of Lemma 4.1.** With resistances `r ≥ 0`,
`Σ_e r_e q_e x_e ≤ √(Σ_e r_e q_e²) · √(Σ_e r_e x_e²)`.
In the paper this turns `cᵀq / cost(x) − 1` into `√(ℰ·cost)/cost − 1`, using
`r_e = c_e / x_e` so that `Σ r_e x_e² = cost(x)`. -/
theorem cs_step {E : Type*} [Fintype E] (r q x : E → ℝ) (hr : ∀ e, 0 ≤ r e) :
    ∑ e, r e * q e * x e ≤
      Real.sqrt (∑ e, r e * q e ^ 2) * Real.sqrt (∑ e, r e * x e ^ 2) := by
  classical
  have hP0 : 0 ≤ ∑ e, r e * q e ^ 2 := Finset.sum_nonneg fun e _ => mul_nonneg (hr e) (sq_nonneg _)
  have hsq : (∑ e, r e * q e * x e) ^ 2 ≤
      (∑ e, r e * q e ^ 2) * (∑ e, r e * x e ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset E)
      (fun e => Real.sqrt (r e) * q e) (fun e => Real.sqrt (r e) * x e)
    have h1 : ∑ e, (Real.sqrt (r e) * q e) * (Real.sqrt (r e) * x e)
        = ∑ e, r e * q e * x e := by
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [mul_mul_mul_comm, Real.mul_self_sqrt (hr e), mul_assoc]
    have h2 : ∑ e, (Real.sqrt (r e) * q e) ^ 2 = ∑ e, r e * q e ^ 2 := by
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [mul_pow, Real.sq_sqrt (hr e)]
    have h3 : ∑ e, (Real.sqrt (r e) * x e) ^ 2 = ∑ e, r e * x e ^ 2 := by
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [mul_pow, Real.sq_sqrt (hr e)]
    rw [← h2, ← h3, ← h1]
    exact h
  set S := ∑ e, r e * q e * x e with hSdef
  rcases le_or_gt S 0 with hS | hS
  · exact le_trans hS (by positivity)
  · calc S = Real.sqrt (S ^ 2) := (Real.sqrt_sq hS.le).symm
      _ ≤ Real.sqrt ((∑ e, r e * q e ^ 2) * (∑ e, r e * x e ^ 2)) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (∑ e, r e * q e ^ 2) * Real.sqrt (∑ e, r e * x e ^ 2) :=
        Real.sqrt_mul hP0 _

/--
**Algebraic core of Lemma 4.4** of [Bonifaci 2016]. Combining Lemma 4.1 and Lemma 4.3
of the paper gives `Φ̇ ≤ 2·√(γ/κ) − 1 − γ` with `γ = ℰ/opt ≥ 0` and `κ = cost/opt`;
this lemma shows that during any phase with `κ ≥ (1+ε)²` and `0 < ε ≤ 1/2` the
potential decreases at rate at least `ε/2`.

Proof (division-free): AM–GM gives `2√(γ/κ) ≤ γ + 1/κ`, so the left side is at most
`1/κ − 1 ≤ 1/(1+ε)² − 1 = −ε(2+ε)/(1+ε)² ≤ −ε/2`, the last step being `ε² ≤ 3`.
(The paper reaches the same bound by a two-case split on `(1−√γ)²`; the completed-square
form below is the same inequality with the case analysis discharged once, and it is the
version that is actually true for *all* `γ ≥ 0` — the naive case split would need
`(1−√γ)² < ε/2`, which fails for small `ε`.)

Applied with `ε' = ε/3` it yields the `−ε/6` rate of Theorem 4.7.
-/
theorem phi_decrease_core {ε γ κ : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (hγ : 0 ≤ γ)
    (hκ : (1 + ε) ^ 2 ≤ κ) : 2 * Real.sqrt (γ / κ) - 1 - γ ≤ -ε / 2 := by
  have hκ0 : (0 : ℝ) < κ := by nlinarith
  -- AM–GM: 2√(γ/κ) ≤ γ + 1/κ
  have hamgm : 2 * Real.sqrt (γ / κ) ≤ γ + 1 / κ := by
    have hsq1 : Real.sqrt γ * Real.sqrt (1 / κ) = Real.sqrt (γ / κ) := by
      rw [← Real.sqrt_mul hγ, mul_one_div]
    have h2 := sq_nonneg (Real.sqrt γ - Real.sqrt (1 / κ))
    rw [sub_sq, Real.sq_sqrt hγ, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 / κ)] at h2
    nlinarith [h2, hsq1]
  have hκle : 1 / κ ≤ 1 / (1 + ε) ^ 2 := one_div_le_one_div_of_le (by positivity) hκ
  have hstep1 : 1 / (1 + ε) ^ 2 ≤ 1 / (1 + ε) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hstep2 : 1 / (1 + ε) - 1 ≤ -ε / 2 := by
    rw [div_sub_one (by positivity : (1 + ε) ≠ 0)]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + ε)]
    nlinarith
  linarith

end Bonnifaci
