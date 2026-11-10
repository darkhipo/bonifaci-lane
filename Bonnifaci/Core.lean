/-
Copyright (c) 2026 MultiAgency bonifaci-lane.
-/
import Bonnifaci.KL
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The analytic core of the Lyapunov decrease

Two fully proved pointwise statements that carry the quantitative heart of
[Bonifaci 2016]:

* `cs_step` — the Cauchy–Schwarz step of Lemma 4.1 (cost of the electrical flow vs.
  the energy inner product);
* `phi_decrease_core` — the two-case algebraic core of Lemma 4.4: while the solution
  is `(1+ε)`-factor superoptimal, the potential decreases at rate at least `ε/6`.

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
  have hQ0 : 0 ≤ ∑ e, r e * x e ^ 2 := Finset.sum_nonneg fun e _ => mul_nonneg (hr e) (sq_nonneg _)
  have hsq : (∑ e, r e * q e * x e) ^ 2 ≤
      (∑ e, r e * q e ^ 2) * (∑ e, r e * x e ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset E)
      (fun e => Real.sqrt (r e) * q e) (fun e => Real.sqrt (r e) * x e)
    have h1 : ∑ e, (Real.sqrt (r e) * q e) * (Real.sqrt (r e) * x e)
        = ∑ e, r e * q e * x e := by
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [mul_mul_mul_comm, Real.sq_sqrt (hr e)]
    have h2 : ∑ e, (Real.sqrt (r e) * q e) ^ 2 = ∑ e, r e * q e ^ 2 := by
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [mul_pow, Real.sq_sqrt (hr e)]
    have h3 : ∑ e, (Real.sqrt (r e) * x e) ^ 2 = ∑ e, r e * x e ^ 2 := by
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [mul_pow, Real.sq_sqrt (hr e)]
    rw [← h2, ← h3, ← h1]
    exact h
  set S := ∑ e, r e * q e * x e with hSdef
  rcases le_or_lt S 0 with hS | hS
  · exact le_trans hS (by positivity)
  · calc S ≤ Real.sqrt (S ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
        exact le_abs_self S
      _ ≤ Real.sqrt ((∑ e, r e * q e ^ 2) * (∑ e, r e * x e ^ 2)) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (∑ e, r e * q e ^ 2) * Real.sqrt (∑ e, r e * x e ^ 2) :=
        Real.sqrt_mul _ hP0

/--
**Algebraic core of Lemma 4.4** of [Bonifaci 2016]: if the potential-decrease ansatz
`Φ̇ ≤ 2·√(γ/κ) − 1 − γ` holds (with `γ = ℰ/opt ≥ 0`, `κ = cost/opt`), then during any
phase with `κ ≥ (1+ε)²` and `0 < ε ≤ 1/2` the potential decreases at rate at least
`ε/2`. This is the two-case computation (`(1−√γ)² ≥ ε/2` vs `< ε/2`) that converts
Lemma 4.1 + 4.3 into a Lyapunov decrease.

Applied with `ε' = ε/3` it yields the `−ε/6` rate of Theorem 4.7.
-/
theorem phi_decrease_core {ε γ κ : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (hγ : 0 ≤ γ)
    (hκ : (1 + ε) ^ 2 ≤ κ) : 2 * Real.sqrt (γ / κ) - 1 - γ ≤ -ε / 2 := by
  have hsqrtep : 0 < (1 + ε : ℝ) := by positivity
  have hsqκ : (1 + ε) ≤ Real.sqrt κ := by
    have h := Real.sqrt_le_sqrt (a := ((1 : ℝ) + ε) ^ 2) (b := κ) hκ
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at h
  have hdiv : Real.sqrt (γ / κ) ≤ Real.sqrt γ / (1 + ε) := by
    rw [Real.sqrt_div hγ]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg γ) hsqrtep hsqκ
  have hident : 2 * (Real.sqrt γ / (1 + ε)) - 1 - γ
      = -2 * (ε / (1 + ε)) * Real.sqrt γ - (1 - Real.sqrt γ) ^ 2 := by
    field_simp
    ring
  have hv : 0 ≤ ε / (1 + ε) := div_nonneg hε0.le (by positivity)
  have hw : 0 ≤ Real.sqrt γ := Real.sqrt_nonneg γ
  have hu : 0 ≤ (1 - Real.sqrt γ) ^ 2 := sq_nonneg _
  calc 2 * Real.sqrt (γ / κ) - 1 - γ
      ≤ 2 * (Real.sqrt γ / (1 + ε)) - 1 - γ := by linarith
    _ = -2 * (ε / (1 + ε)) * Real.sqrt γ - (1 - Real.sqrt γ) ^ 2 := hident
    _ ≤ -ε / 2 := by
        rcases le_or_lt ((1 : ℝ) / 2) ((1 - Real.sqrt γ) ^ 2) with hc | hc
        · -- case 1: (1 − √γ)² ≥ 1/2 ≥ ε/2: drop the first summand
          linarith
        · -- case 2: (1 − √γ)² < 1/2, so √γ > 1/2: drop the second summand
          have h2 : 1 - Real.sqrt γ < Real.sqrt (ε / 2) := Real.lt_sqrt_of_sq_lt hc
          have h3 : Real.sqrt (ε / 2) ≤ 1 / 2 := by
            rw [Real.sqrt_le_iff]
            exact ⟨by norm_num, by linarith⟩
          have hv33 : (2 / 3) * ε ≤ ε / (1 + ε) := by
            rw [div_le_iff₀ hsqrtep]
            nlinarith
          have hw1 : (1 : ℝ) / 2 < Real.sqrt γ := by linarith
          -- the one product step, made explicit so the final step is linear
          have hprod : (2 : ℝ) / 3 * ε * ((1 : ℝ) / 2)
              ≤ ε / (1 + ε) * Real.sqrt γ :=
            mul_le_mul hv33 hw1.le (by norm_num) hv
          have he : (2 : ℝ) / 3 * ε * ((1 : ℝ) / 2) = (1 : ℝ) / 3 * ε := by ring
          rw [he] at hprod
          linarith

end Bonnifaci
