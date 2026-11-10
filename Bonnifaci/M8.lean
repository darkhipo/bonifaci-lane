/-
Copyright (c) 2026 MultiAgency bonifaci-lane.
-/
import Bonnifaci.M7
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section

/-!
# M8 — `FlowLipschitzOnOrthant` is discharged

`M7` left two named Props. This file discharges the first: the flow map
`x ↦ q(x) = C Aᵀ (A C Aᵀ)⁻¹ b` is locally Lipschitz on the positive orthant.

## Route choice (measured, and disclosed — see `STMTS.md` §9)

The M7 header proposed going through `Mathlib.Analysis.Normed.Algebra.Inverse` —
continuity of matrix inversion via operator-norm perturbation theory. Measured on the
campaign pin (`d13f23b7`) with `receipts/closure_cost.py`:

| candidate module | on this pin | unbuilt modules to compile first |
|---|---|---|
| `Mathlib.Analysis.Normed.Algebra.Inverse` | **absent** | — (the M7 plan cited a name this pin does not have) |
| `Mathlib.Analysis.Normed.Algebra.Basic` | present | **6616** |
| `Mathlib.Analysis.Normed.Module.ContinuousInverse` | present | **190** |
| `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` (adjugate/det) | present | **72** |
| `Mathlib.Algebra.Order.BigOperators.Ring.Finset` | present, **already imported by `Model`** | **0** |

So the analytic-inverse route costs 72–6616 modules and the adjugate route 72. The
route taken here costs **zero new imports**, because it never inverts a matrix.

## The route: an energy perturbation estimate

For two strictly positive points `x`, `y` with flows `q`, `q'`: both are Kirchhoff
flows for the same `b`, so `g = q − q'` is Kirchhoff-homogeneous (`A g = 0`). Ohm's
law at the two points differs only by the resistance mismatch
`s_e = q'_e (c_e/y_e − c_e/x_e)`, and multiplying the differenced Ohm law by `g_e` and
summing kills the potential term (`A g = 0`):

  `∑_e (c_e/x_e) g_e² = ∑_e s_e g_e`

This is the whole content: no matrix is inverted, no determinant appears, and no
normed-space theory is used. Bounding `|s_e|` needs only that `q'` is bounded on the
ball, which is Thomson's principle at `y` tested against the *fixed* flow `q`, plus
`y_e ∈ [x_e/2, 3x_e/2]` from the ball radius.

## What this buys, and what it does not

`FlowLipschitzOnOrthant` is Picard–Lindelöf's hypothesis. Proving it does **not** prove
existence of a global trajectory: that is `HasSolution` (seam 2), which remains named.
-/

set_option linter.unusedSectionVars false

open Finset

variable {N E : Type*} [Fintype N] [Fintype E] [DecidableEq N] [DecidableEq E]

/-! ## Elementary comparison lemmas for the resistance at the two points -/

/-- `c/y ≤ 2c/x` when `x ≤ 2y` and everything is positive. -/
private lemma div_le_two_div {c x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y)
    (h : x ≤ 2 * y) : c / y ≤ 2 * c / x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hyne : y ≠ 0 := ne_of_gt hy
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < x * y)
  calc c / y * (x * y) = c * x := by field_simp
    _ ≤ 2 * c * y := by nlinarith
    _ = (2 * c / x) * (x * y) := by field_simp

/-- `2c/(3x) ≤ c/y` when `2y ≤ 3x` and everything is positive. -/
private lemma two_div_three_le_div {c x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y)
    (h : 2 * y ≤ 3 * x) : 2 * c / (3 * x) ≤ c / y := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hyne : y ≠ 0 := ne_of_gt hy
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < x * y)
  calc 2 * c / (3 * x) * (x * y) = 2 * c * y / 3 := by field_simp
    _ ≤ c * x := by nlinarith
    _ = c / y * (x * y) := by field_simp

/-- `1/(xy) ≤ 2/x²` when `x ≤ 2y` and everything is positive. -/
private lemma one_div_mul_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x ≤ 2 * y) :
    1 / (x * y) ≤ 2 / x ^ 2 := by
  have hpos : (0 : ℝ) < x ^ 2 * y := by positivity
  have h1 : 1 / (x * y) * (x ^ 2 * y) = x := by field_simp
  have h2 : (2 / x ^ 2) * (x ^ 2 * y) = 2 * y := by field_simp
  refine le_of_mul_le_mul_right ?_ hpos
  rw [h1, h2]
  linarith

/-! ## Ohm's law, differenced -/

/-- The resistance-mismatch form of Ohm's law. At a common edge `e`, the two Ohm laws
differ by exactly the resistance mismatch between the points, not by a re-solve. -/
theorem LPData.ohm_res_sub (d : LPData N E) {x y : E → ℝ} (st : d.Step x) (st' : d.Step y)
    (e : E) :
    d.c e / x e * (st.q e - st'.q e)
      = (∑ n, d.A n e * (st.p n - st'.p n))
        + st'.q e * (d.c e / y e - d.c e / x e) := by
  have h1 := st.ohm e
  have h2 := st'.ohm e
  have hsplit : (∑ n, d.A n e * (st.p n - st'.p n))
      = (∑ n, d.A n e * st.p n) - (∑ n, d.A n e * st'.p n) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hsplit, ← h1, ← h2]
  ring

/-! ## The perturbation identity -/

/-- **The energy perturbation identity.** The resistance-weighted square of the flow
difference equals the mismatch term paired against the difference. The potential term
cancels because the difference of two Kirchhoff flows is Kirchhoff-homogeneous. -/
theorem LPData.energy_perturb (d : LPData N E) {x y : E → ℝ} (st : d.Step x)
    (st' : d.Step y) :
    ∑ e, d.c e / x e * (st.q e - st'.q e) ^ 2
      = ∑ e, (st'.q e * (d.c e / y e - d.c e / x e)) * (st.q e - st'.q e) := by
  have hzero : ∀ n, ∑ e, d.A n e * (st.q e - st'.q e) = 0 := by
    intro n
    have h : (∑ e, d.A n e * (st.q e - st'.q e))
        = (∑ e, d.A n e * st.q e) - (∑ e, d.A n e * st'.q e) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    rw [h, st.hflow n, st'.hflow n, sub_self]
  have hpot : ∑ e, (∑ n, d.A n e * (st.p n - st'.p n)) * (st.q e - st'.q e) = 0 := by
    have h1 : ∀ e, (∑ n, d.A n e * (st.p n - st'.p n)) * (st.q e - st'.q e)
        = ∑ n, (d.A n e * (st.p n - st'.p n)) * (st.q e - st'.q e) := by
      intro e
      rw [Finset.sum_mul]
    simp only [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ n, ∑ e, (d.A n e * (st.p n - st'.p n)) * (st.q e - st'.q e)
        = (st.p n - st'.p n) * ∑ e, d.A n e * (st.q e - st'.q e) := by
      intro n
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    simp only [h2, hzero, mul_zero, Finset.sum_const_zero]
  have hpt : ∀ e, d.c e / x e * (st.q e - st'.q e) ^ 2
      = ((∑ n, d.A n e * (st.p n - st'.p n))
          + st'.q e * (d.c e / y e - d.c e / x e)) * (st.q e - st'.q e) := by
    intro e
    rw [← d.ohm_res_sub st st' e]
    ring
  calc ∑ e, d.c e / x e * (st.q e - st'.q e) ^ 2
      = ∑ e, ((∑ n, d.A n e * (st.p n - st'.p n))
          + st'.q e * (d.c e / y e - d.c e / x e)) * (st.q e - st'.q e) :=
        Finset.sum_congr rfl fun e _ => hpt e
    _ = ∑ e, (∑ n, d.A n e * (st.p n - st'.p n)) * (st.q e - st'.q e)
          + ∑ e, (st'.q e * (d.c e / y e - d.c e / x e)) * (st.q e - st'.q e) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun e _ => by ring
    _ = ∑ e, (st'.q e * (d.c e / y e - d.c e / x e)) * (st.q e - st'.q e) := by
        rw [hpot, zero_add]

/-! ## Bounding the flow at the perturbed point (Thomson)

The only place the ball radius enters: on `|y − x| ≤ ε` we get `y_e ∈ [x_e/2, 3x_e/2]`,
which makes the resistance at `y` comparable to the resistance at `x` in *both*
directions. Thomson's principle at `y`, tested against the fixed flow `q`, then bounds
`q'` by data at `x` alone — no solve at `y` is ever needed. -/

/-- Thomson at `y`, tested against the fixed flow at `x`, bounds `q'` by the data at `x`. -/
theorem LPData.q'_sq_le (d : LPData N E) {x y : E → ℝ} (st : d.Step x) (st' : d.Step y)
    (hx : ∀ e, 0 < x e) (hlo : ∀ e, x e / 2 ≤ y e) (hhi : ∀ e, y e ≤ 3 * x e / 2) (e : E) :
    st'.q e ^ 2
      ≤ (∑ j, (2 * d.c j / x j) * st.q j ^ 2) * (3 * x e) / (2 * d.c e) := by
  have hy : ∀ j, 0 < y j := fun j => lt_of_lt_of_le (by linarith [hx j]) (hlo j)
  have hT : ∑ j, d.c j / y j * st'.q j ^ 2 ≤ ∑ j, d.c j / y j * st.q j ^ 2 :=
    st'.thomson st.q st.hflow
  have hcomp : ∑ j, d.c j / y j * st.q j ^ 2 ≤ ∑ j, (2 * d.c j / x j) * st.q j ^ 2 := by
    refine Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_right
      (div_le_two_div (d.hc j) (hx j) (hy j) (by linarith [hlo j])) (sq_nonneg _)
  have hlow : (2 * d.c e / (3 * x e)) * st'.q e ^ 2 ≤ d.c e / y e * st'.q e ^ 2 :=
    mul_le_mul_of_nonneg_right
      (two_div_three_le_div (d.hc e) (hx e) (hy e) (by linarith [hhi e])) (sq_nonneg _)
  have hsingle : d.c e / y e * st'.q e ^ 2 ≤ ∑ j, d.c j / y j * st'.q j ^ 2 :=
    Finset.single_le_sum
      (f := fun j => d.c j / y j * st'.q j ^ 2)
      (fun j _ => mul_nonneg (le_of_lt (div_pos (d.hc j) (hy j))) (sq_nonneg _))
      (Finset.mem_univ e)
  have hkey : (2 * d.c e / (3 * x e)) * st'.q e ^ 2
      ≤ ∑ j, (2 * d.c j / x j) * st.q j ^ 2 :=
    le_trans hlow (le_trans hsingle (le_trans hT hcomp))
  have hcoef : 0 < 3 * x e / (2 * d.c e) := by
    have h1 : 0 < d.c e := d.hc e
    have h2 : 0 < x e := hx e
    positivity
  have hcne : d.c e ≠ 0 := ne_of_gt (d.hc e)
  have hxne : x e ≠ 0 := ne_of_gt (hx e)
  calc st'.q e ^ 2
      = (2 * d.c e / (3 * x e)) * st'.q e ^ 2 * (3 * x e / (2 * d.c e)) := by
        field_simp
    _ ≤ (∑ j, (2 * d.c j / x j) * st.q j ^ 2) * (3 * x e / (2 * d.c e)) :=
        mul_le_mul_of_nonneg_right hkey (le_of_lt hcoef)
    _ = (∑ j, (2 * d.c j / x j) * st.q j ^ 2) * (3 * x e) / (2 * d.c e) := by ring

/-- **The mismatch term is linearly bounded by the displacement.** The `2|a| ≤ 1 + a²`
AM–GM step is what buys a bound with no square root. -/
theorem LPData.mis_le (d : LPData N E) {x y : E → ℝ} (st : d.Step x) (st' : d.Step y)
    (hx : ∀ e, 0 < x e) (hlo : ∀ e, x e / 2 ≤ y e)
    (hq : ∀ e, st'.q e ^ 2 ≤ (∑ j, (2 * d.c j / x j) * st.q j ^ 2) * (3 * x e) / (2 * d.c e))
    (e : E) :
    |st'.q e * (d.c e / y e - d.c e / x e)|
      ≤ ((d.c e / x e ^ 2) + 3 * (∑ j, (2 * d.c j / x j) * st.q j ^ 2) / (2 * x e))
        * |y e - x e| := by
  set E2 := ∑ j, (2 * d.c j / x j) * st.q j ^ 2 with hE2
  have hy : 0 < y e := lt_of_lt_of_le (by linarith [hx e]) (hlo e)
  have hce : 0 < d.c e := d.hc e
  have hxe : 0 < x e := hx e
  have hx2 : (0 : ℝ) < x e ^ 2 := by positivity
  have hcne : d.c e ≠ 0 := ne_of_gt hce
  have hxne : x e ≠ 0 := ne_of_gt hxe
  have hyne : y e ≠ 0 := ne_of_gt hy
  -- exact value of the mismatch, with the `|x − y|` peeled off
  have h1 : |st'.q e * (d.c e / y e - d.c e / x e)|
      = |st'.q e| * d.c e * |y e - x e| * (1 / (x e * y e)) := by
    have hsub : d.c e / y e - d.c e / x e = d.c e * (x e - y e) / (x e * y e) := by
      field_simp
      try ring
    rw [hsub, abs_mul, abs_div, abs_mul, abs_of_pos hce,
      abs_of_pos (mul_pos hxe hy), abs_sub_comm]
    ring
  -- `1/(xy) ≤ 2/x²`
  have h2 : |st'.q e| * d.c e * |y e - x e| * (1 / (x e * y e))
      ≤ |st'.q e| * d.c e * |y e - x e| * (2 / x e ^ 2) :=
    mul_le_mul_of_nonneg_left (one_div_mul_le hxe hy (by linarith [hlo e])) (by positivity)
  -- `2|q'| ≤ 1 + q'²`
  have ham : 2 * |st'.q e| ≤ 1 + st'.q e ^ 2 := by
    nlinarith [sq_abs (st'.q e), sq_nonneg (|st'.q e| - 1)]
  have h3 : |st'.q e| * d.c e * |y e - x e| * (2 / x e ^ 2)
      ≤ (d.c e / x e ^ 2) * (1 + st'.q e ^ 2) * |y e - x e| := by
    refine le_of_mul_le_mul_right ?_ hx2
    have e1 : |st'.q e| * d.c e * |y e - x e| * (2 / x e ^ 2) * x e ^ 2
        = 2 * (|st'.q e| * d.c e * |y e - x e|) := by field_simp; try ring
    have e2 : (d.c e / x e ^ 2) * (1 + st'.q e ^ 2) * |y e - x e| * x e ^ 2
        = (1 + st'.q e ^ 2) * (d.c e * |y e - x e|) := by field_simp; try ring
    rw [e1, e2]
    have hg : 0 ≤ d.c e * |y e - x e| := by positivity
    nlinarith [ham, hg]
  -- `(c/x²)·q'² ≤ 3E₂/(2x)` from the Thomson bound
  have hkey : (d.c e / x e ^ 2) * st'.q e ^ 2 ≤ 3 * E2 / (2 * x e) := by
    have hfac : (0 : ℝ) < d.c e / x e ^ 2 := by positivity
    have hstep := mul_le_mul_of_nonneg_left (hq e) (le_of_lt hfac)
    calc (d.c e / x e ^ 2) * st'.q e ^ 2
        ≤ (d.c e / x e ^ 2) * (E2 * (3 * x e) / (2 * d.c e)) := hstep
      _ = 3 * E2 / (2 * x e) := by field_simp; try ring
  have hcoef : (d.c e / x e ^ 2) * (1 + st'.q e ^ 2)
      ≤ (d.c e / x e ^ 2) + 3 * E2 / (2 * x e) := by
    have hexp : (d.c e / x e ^ 2) * (1 + st'.q e ^ 2)
        = (d.c e / x e ^ 2) + (d.c e / x e ^ 2) * st'.q e ^ 2 := by ring
    linarith [hkey, hexp]
  have h4 : (d.c e / x e ^ 2) * (1 + st'.q e ^ 2) * |y e - x e|
      ≤ ((d.c e / x e ^ 2) + 3 * E2 / (2 * x e)) * |y e - x e| :=
    mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
  calc |st'.q e * (d.c e / y e - d.c e / x e)|
      = |st'.q e| * d.c e * |y e - x e| * (1 / (x e * y e)) := h1
    _ ≤ |st'.q e| * d.c e * |y e - x e| * (2 / x e ^ 2) := h2
    _ ≤ (d.c e / x e ^ 2) * (1 + st'.q e ^ 2) * |y e - x e| := h3
    _ ≤ ((d.c e / x e ^ 2) + 3 * E2 / (2 * x e)) * |y e - x e| := h4
    _ = ((d.c e / x e ^ 2) + 3 * (∑ j, (2 * d.c j / x j) * st.q j ^ 2) / (2 * x e))
          * |y e - x e| := by rw [hE2]

/-! ## The discharge -/

/-- **`FlowLipschitzOnOrthant` is a theorem.** The flow map is locally Lipschitz on the
positive orthant: at every strictly positive `x` there is a radius and a constant `K`
with `|q(y) − q(x)| ≤ K · ∑|y − x|`.

The proof never inverts a matrix. It is the energy estimate of `energy_perturb`
combined with the Thomson bound `q'_sq_le` and the mismatch bound `mis_le`, and closes
by the elementary `|d_e| ≤ √(∑ d²) ≤ K·∑|y − x|`. -/
theorem LPData.flowLipschitzOnOrthant (d : LPData N E) : d.FlowLipschitzOnOrthant := by
  intro x hx st
  by_cases hE : Nonempty E
  · obtain ⟨e0⟩ := hE
    -- ball radius: half the smallest coordinate of `x`
    set ε := Finset.univ.inf' ⟨e0, Finset.mem_univ e0⟩ (fun e => x e / 2) with hε
    have hεpos : 0 < ε := by
      rw [hε]
      exact (Finset.lt_inf'_iff ⟨e0, Finset.mem_univ e0⟩).mpr (fun e _ => by linarith [hx e])
    have hεle : ∀ e, ε ≤ x e / 2 := by
      intro e
      rw [hε]
      exact Finset.inf'_le (fun e => x e / 2) (Finset.mem_univ e)
    -- the resistance floor
    set μ := Finset.univ.inf' ⟨e0, Finset.mem_univ e0⟩ (fun e => d.c e / x e) with hμ
    have hμpos : 0 < μ := by
      rw [hμ]
      exact (Finset.lt_inf'_iff ⟨e0, Finset.mem_univ e0⟩).mpr (fun e _ => div_pos (d.hc e) (hx e))
    have hμle : ∀ e, μ ≤ d.c e / x e := by
      intro e
      rw [hμ]
      exact Finset.inf'_le (fun e => d.c e / x e) (Finset.mem_univ e)
    -- the Thomson energy at `x`
    set E2 := ∑ j, (2 * d.c j / x j) * st.q j ^ 2 with hE2
    have hE2nn : 0 ≤ E2 := by
      rw [hE2]
      refine Finset.sum_nonneg fun j _ => ?_
      have h1 : 0 < 2 * d.c j / x j := by
        have hc := d.hc j
        have hxj := hx j
        positivity
      exact mul_nonneg (le_of_lt h1) (sq_nonneg _)
    -- the mismatch coefficient, uniform over the ball
    set W := Finset.univ.sup' ⟨e0, Finset.mem_univ e0⟩
      (fun e => d.c e / x e ^ 2 + 3 * E2 / (2 * x e)) with hW
    have hWge : ∀ e, d.c e / x e ^ 2 + 3 * E2 / (2 * x e) ≤ W := by
      intro e
      rw [hW]
      exact Finset.le_sup' (fun e => d.c e / x e ^ 2 + 3 * E2 / (2 * x e)) (Finset.mem_univ e)
    have hWnn : 0 ≤ W := by
      have h0 : 0 ≤ d.c e0 / x e0 ^ 2 + 3 * E2 / (2 * x e0) := by
        have h1 : 0 ≤ d.c e0 / x e0 ^ 2 :=
          div_nonneg (le_of_lt (d.hc e0)) (sq_nonneg (x e0))
        have h2 : 0 ≤ 3 * E2 / (2 * x e0) :=
          div_nonneg (mul_nonneg (by norm_num) hE2nn) (by linarith [hx e0])
        linarith
      exact le_trans h0 (hWge e0)
    refine ⟨ε, hεpos, W / μ, div_nonneg hWnn (le_of_lt hμpos), ?_⟩
    intro y hy st' hball
    -- the ball keeps `y` inside `[x/2, 3x/2]` coordinatewise
    have hlo : ∀ j, x j / 2 ≤ y j := by
      intro j
      have h1 : |y j - x j| ≤ x j / 2 := le_trans (hball j) (hεle j)
      have h2 := (abs_le.mp h1).1
      linarith
    have hhi : ∀ j, y j ≤ 3 * x j / 2 := by
      intro j
      have h1 : |y j - x j| ≤ x j / 2 := le_trans (hball j) (hεle j)
      have h2 := (abs_le.mp h1).2
      linarith
    have hsun : 0 ≤ ∑ j, |y j - x j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    set S := ∑ j, (st.q j - st'.q j) ^ 2 with hS
    have hSnn : 0 ≤ S := by
      rw [hS]
      exact Finset.sum_nonneg fun j _ => sq_nonneg _
    -- `|d_e| ≤ √S`
    have hd : ∀ j, |st.q j - st'.q j| ≤ Real.sqrt S := by
      intro j
      have hdj : (st.q j - st'.q j) ^ 2 ≤ S := by
        rw [hS]
        exact Finset.single_le_sum (f := fun i => (st.q i - st'.q i) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ j)
      calc |st.q j - st'.q j| = Real.sqrt ((st.q j - st'.q j) ^ 2) := by
            rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt S := Real.sqrt_le_sqrt hdj
    have hsqrtnn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
    -- μ·S ≤ ∑ (c/x)d² = ∑ s·d ≤ W·(∑|y−x|)·√S
    have hstep1 : μ * S ≤ ∑ j, d.c j / x j * (st.q j - st'.q j) ^ 2 := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hμle j) (sq_nonneg _)
    have hmis : ∀ j, |st'.q j * (d.c j / y j - d.c j / x j)| ≤ W * |y j - x j| := by
      intro j
      have h1 := d.mis_le st st' hx hlo (fun i => d.q'_sq_le st st' hx hlo hhi i) j
      have h2 : (∑ i, (2 * d.c i / x i) * st.q i ^ 2) = E2 := by rw [hE2]
      rw [h2] at h1
      exact le_trans h1 (mul_le_mul_of_nonneg_right (hWge j) (abs_nonneg _))
    have hchain : ∑ j, (st'.q j * (d.c j / y j - d.c j / x j)) * (st.q j - st'.q j)
        ≤ W * (∑ j, |y j - x j|) * Real.sqrt S := by
      calc ∑ j, (st'.q j * (d.c j / y j - d.c j / x j)) * (st.q j - st'.q j)
          ≤ ∑ j, |st'.q j * (d.c j / y j - d.c j / x j)| * |st.q j - st'.q j| := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [← abs_mul]
            exact le_abs_self _
        _ ≤ ∑ j, (W * |y j - x j|) * |st.q j - st'.q j| := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact mul_le_mul_of_nonneg_right (hmis j) (abs_nonneg _)
        _ ≤ ∑ j, (W * |y j - x j|) * Real.sqrt S := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact mul_le_mul_of_nonneg_left (hd j) (mul_nonneg hWnn (abs_nonneg _))
        _ = W * (∑ j, |y j - x j|) * Real.sqrt S := by
            rw [← Finset.sum_mul, Finset.mul_sum]
    have hSQ : μ * S ≤ W * (∑ j, |y j - x j|) * Real.sqrt S :=
      calc μ * S ≤ ∑ j, d.c j / x j * (st.q j - st'.q j) ^ 2 := hstep1
        _ = ∑ j, (st'.q j * (d.c j / y j - d.c j / x j)) * (st.q j - st'.q j) :=
            d.energy_perturb st st'
        _ ≤ W * (∑ j, |y j - x j|) * Real.sqrt S := hchain
    -- divide by √S (the zero case is trivial: both sides vanish)
    have hfin : Real.sqrt S ≤ W * (∑ j, |y j - x j|) / μ := by
      rcases eq_or_lt_of_le hsqrtnn with h0 | hpos
      · rw [← h0]
        exact div_nonneg (mul_nonneg hWnn hsun) (le_of_lt hμpos)
      · have hsq : Real.sqrt S * Real.sqrt S = S := by
          simpa [sq] using Real.sq_sqrt hSnn
        have hmul : μ * Real.sqrt S * Real.sqrt S
            ≤ W * (∑ j, |y j - x j|) * Real.sqrt S := by
          nlinarith [hSQ, hsq]
        have hdiv : μ * Real.sqrt S ≤ W * (∑ j, |y j - x j|) :=
          le_of_mul_le_mul_right hmul hpos
        rw [le_div_iff₀ hμpos]
        nlinarith [hdiv]
    intro e
    calc |st'.q e - st.q e| = |st.q e - st'.q e| := abs_sub_comm _ _
      _ ≤ Real.sqrt S := hd e
      _ ≤ W * (∑ j, |y j - x j|) / μ := hfin
      _ = (W / μ) * (∑ j, |y j - x j|) := by ring
  · -- no edges: the conclusion is vacuous
    have h : IsEmpty E := not_nonempty_iff.mp hE
    refine ⟨1, one_pos, 0, le_refl 0, ?_⟩
    intro y hy st' hball e
    exact (h.false e).elim

/-! ## Picard–Lindelöf's hypothesis, stated on the right-hand side

`FlowLipschitzOnOrthant` constrains the *flow*. What Picard–Lindelöf actually consumes is
Lipschitz continuity of the ODE right-hand side `x ↦ rhs x = q(x) − x`. That follows from
the flow's Lipschitz continuity plus `|y_e − x_e| ≤ ∑|y − x|`, so the ODE seam is now
discharged at the level the existence theory would use, not merely at the level of `q`. -/

/-- **Picard–Lindelöf's hypothesis on the ODE right-hand side.** -/
def LPData.RhsLipschitzOnOrthant (d : LPData N E) : Prop :=
  ∀ (x : E → ℝ) (hx : ∀ e, 0 < x e) (hrank : d.FullRowRank),
    ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (y : E → ℝ) (hy : ∀ e, 0 < y e),
        (∀ e, |y e - x e| ≤ ε) →
        ∀ e, |d.rhs y hy hrank e - d.rhs x hx hrank e| ≤ K * ∑ j, |y j - x j|

/-- **The right-hand side is locally Lipschitz on the positive orthant**, derived from
`FlowLipschitzOnOrthant`. The constant is `K + 1`: the `+1` is the `−x` term. -/
theorem LPData.rhsLipschitzOnOrthant (d : LPData N E) (h : d.FlowLipschitzOnOrthant) :
    d.RhsLipschitzOnOrthant := by
  intro x hx hrank
  obtain ⟨ε, hεpos, K, hKnn, hlip⟩ := h x hx (Classical.choice (d.exists_step x hx hrank))
  refine ⟨ε, hεpos, K + 1, by linarith, ?_⟩
  intro y hy hball e
  have hxq : (Classical.choice (d.exists_step x hx hrank)).q = d.qfun x hx hrank :=
    d.qfun_eq_steps hx hrank _
  have hyq : (Classical.choice (d.exists_step y hy hrank)).q = d.qfun y hy hrank :=
    d.qfun_eq_steps hy hrank _
  have hlip' : |(Classical.choice (d.exists_step y hy hrank)).q e
      - (Classical.choice (d.exists_step x hx hrank)).q e| ≤ K * ∑ j, |y j - x j| :=
    hlip y hy (Classical.choice (d.exists_step y hy hrank)) hball e
  have hsingle : |y e - x e| ≤ ∑ j, |y j - x j| :=
    Finset.single_le_sum (f := fun j => |y j - x j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ e)
  have hrhs : d.rhs y hy hrank e - d.rhs x hx hrank e
      = ((Classical.choice (d.exists_step y hy hrank)).q e
          - (Classical.choice (d.exists_step x hx hrank)).q e) - (y e - x e) := by
    simp only [LPData.rhs, Pi.sub_apply, hxq, hyq]
    ring
  rw [hrhs]
  set A := (Classical.choice (d.exists_step y hy hrank)).q e
    - (Classical.choice (d.exists_step x hx hrank)).q e with hA
  set C := y e - x e with hC
  have hsplit : |A - C| ≤ |A| + |C| := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [le_abs_self A, neg_abs_le A, le_abs_self C, neg_abs_le C]
  calc |A - C| ≤ |A| + |C| := hsplit
    _ ≤ K * ∑ j, |y j - x j| + ∑ j, |y j - x j| := add_le_add hlip' hsingle
    _ = (K + 1) * ∑ j, |y j - x j| := by ring
