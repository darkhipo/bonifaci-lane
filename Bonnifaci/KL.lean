/-
Copyright (c) 2026 MultiAgency bonifaci-lane.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Kullback–Leibler divergence for finite support

The relative entropy used in the potential function Φ of [Bonifaci 2016, eq. (7)]:
`KL(ξ*, ξ(t)) = Σ_e ξ*_e · ln(ξ*_e / ξ_e)` over the finite edge set.

Proved here: Gibbs' inequality (`KL_nonneg`), the analytic core of the
"smooth KL" Lyapunov term.
-/

open Finset Real

variable {E : Type*} [Fintype E]

namespace Bonnifaci

/-- Gibbs' pointwise inequality: `a · ln(a/b) ≥ a − b` for `0 ≤ a`, `0 < b`. -/
theorem mul_log_div_ge_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a - b ≤ a * Real.log (a / b) := by
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · subst ha0
    simpa using hb.le
  · have h1 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha0)
    have h2 : Real.log (a / b) = -Real.log (b / a) := by
      have heq : a / b = (b / a)⁻¹ := by field_simp
      rw [heq, Real.log_inv]
    have h3 : 1 - b / a ≤ Real.log (a / b) := by linarith
    have h4 : a * (1 - b / a) ≤ a * Real.log (a / b) := mul_le_mul_of_nonneg_left h3 ha0.le
    have h5 : a * (1 - b / a) = a - b := by field_simp
    linarith

/-- Kullback–Leibler divergence of finite distributions `s` w.r.t. `x`
(`x` entrywise positive): `KL(s, x) = Σ_e s_e · ln (s_e / x_e)`.
The `s_e = 0` summands vanish by the `0 * _ = 0` convention of the product. -/
def KL (s x : E → ℝ) : ℝ := ∑ e, s e * Real.log (s e / x e)

/-- **Gibbs' inequality**: KL is nonnegative on normalized distributions. -/
theorem KL_nonneg {s x : E → ℝ} (hs : ∀ e, 0 ≤ s e) (hx : ∀ e, 0 < x e)
    (hss : ∑ e, s e = 1) (hxx : ∑ e, x e = 1) : 0 ≤ KL s x := by
  have h1 : ∑ e, (s e - x e) ≤ KL s x :=
    Finset.sum_le_sum fun e _ => mul_log_div_ge_sub (hs e) (hx e)
  have h2 : ∑ e, (s e - x e) = ∑ e, s e - ∑ e, x e := by
    rw [← Finset.sum_sub_distrib]
  rw [hss, hxx] at h2
  linarith

end Bonnifaci
