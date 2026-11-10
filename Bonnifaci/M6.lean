/-
Copyright (c) 2026 MultiAgency bonifaci-lane.
-/
import Bonnifaci.Model
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

/-!
# M6 — the Laplacian-solve seam is discharged

`Model.lean` quarantined Physarum's electrical-network solve into the structure
`LPData.Step` (Kirchhoff + Ohm + Thomson), leaving it as a named premise. This file
removes the black box: for **every** strictly positive `x` and every `LPData` whose
constraint matrix has full row rank, `LPData.exists_step` *constructs* an inhabitant
of `d.Step x` out of pure linear algebra.

## The construction

With conductances `cond_e = x_e / c_e > 0` and the weighted Laplacian
`L = A · diag(cond) · Aᵀ`:

* `L` is positive definite on `ℝ^N`: `y ⬝ᵥ (L *ᵥ y) = ∑_e cond_e · ((Aᵀ y)_e)² ≥ 0`,
  with equality only for `Aᵀ y = 0`, which full row rank forces to `y = 0`
  (`dot_Lmat`, `Lmat_mulVec_eq_zero`, `Lmat_injective`).
* Positive definiteness makes `mulVec L` injective (`Lmat_injective`); read as the
  linear map `Matrix.mulVecLin`, injectivity is equivalent to surjectivity on the
  finite-dimensional space `N -> R` (`LinearMap.injective_iff_surjective`), so the
  Kirchhoff system `L p = b` has a solution `p` (`exists_potential`). That route
  needs rank-nullity only, not determinants: on the campaign pin the determinant
  route's import closure is 119 unbuilt modules against 49 for this one.
* Set `q = diag(cond) Aᵀ p`. Then `A q = L p = b` (Kirchhoff) and
  `(c_e/x_e) q_e = (Aᵀ p)_e` (Ohm), because `cond_e · c_e/x_e = 1`.
* Thomson is the standard energy computation: for Kirchhoff `f` put `g = f - q`.
  The cross term `∑_e (c_e/x_e) q_e g_e = ∑_n p_n (A g)_n` vanishes since `A g = 0`,
  so `∑ (c/x) f² = ∑ (c/x) q² + ∑ (c/x) g² ≥ ∑ (c/x) q²`.

## Layer discipline (campaign constraint (a))

Every step above is finite real arithmetic and finite-dimensional linear algebra over
`ℝ`. **No comparison-addition model appears anywhere**: the quarantined electrical
layer is discharged as algebra, not re-modelled.
-/

set_option linter.unusedSectionVars false

open Finset
open Matrix

open scoped Matrix

variable {N E : Type*} [Fintype N] [Fintype E] [DecidableEq N] [DecidableEq E]

/-! ## The weighted Laplacian -/

/-- Conductance of edge `e` at a strictly positive point `x`: `x_e / c_e > 0`. -/
def LPData.cond (d : LPData N E) (x : E → ℝ) (e : E) : ℝ := x e / d.c e

/-- `L = A C Aᵀ` with `C = diag (cond)`: the conductance-weighted Laplacian. -/
def LPData.Lmat (d : LPData N E) (x : E → ℝ) : Matrix N N ℝ :=
  Matrix.of d.A * Matrix.diagonal (d.cond x) * (Matrix.of d.A)ᵀ

/--
The paper's rank condition (Sec. 1.1): `A` has full row rank, i.e. `Aᵀ` is injective.
This is the *only* extra ingredient the Laplacian solve needs beyond `LPData`; it is
carried as a hypothesis of `exists_step`, not as a structure field, because the
dynamics layer of the formalization does not use it.
-/
def LPData.FullRowRank (d : LPData N E) : Prop :=
  ∀ p : N → ℝ, (∀ e, ∑ n, d.A n e * p n = 0) → p = 0

lemma LPData.cond_pos (d : LPData N E) {x : E → ℝ} (hx : ∀ e, 0 < x e) (e : E) :
    0 < d.cond x e := by
  rw [LPData.cond]
  exact div_pos (hx e) (d.hc e)

/-- The resistance/conductance cancellation `(c_e/x_e) · (x_e/c_e) = 1`. -/
lemma LPData.res_mul_cond (d : LPData N E) {x : E → ℝ} (hx : ∀ e, 0 < x e) (e : E) :
    d.res x e * d.cond x e = 1 := by
  rw [LPData.res, LPData.cond, div_mul_div_comm]
  have h : d.c e * x e = x e * d.c e := by ring
  rw [h, div_self (mul_ne_zero (ne_of_gt (hx e)) (ne_of_gt (d.hc e)))]

/-- `(Aᵀ p)_e = ∑_n A_{ne} p_n`. -/
lemma LPData.dualVec_apply (d : LPData N E) (p : N → ℝ) (e : E) :
    ((Matrix.of d.A)ᵀ *ᵥ p) e = ∑ n, d.A n e * p n := by
  simp [Matrix.mulVec, dotProduct, of_apply, transpose_apply]

/-! ## Positive definiteness of `L` -/

/--
The quadratic form of `L` is the conductance-weighted squared `Aᵀ y`:
`y ⬝ᵥ (L *ᵥ y) = ∑_e cond_e · ((Aᵀ y)_e)²`.
-/
lemma LPData.dot_Lmat (d : LPData N E) (x : E → ℝ) (y : N → ℝ) :
    y ⬝ᵥ (d.Lmat x *ᵥ y) = ∑ e, d.cond x e * (∑ n, d.A n e * y n) ^ 2 := by
  have hL : d.Lmat x *ᵥ y
      = Matrix.of d.A *ᵥ (Matrix.diagonal (d.cond x) *ᵥ ((Matrix.of d.A)ᵀ *ᵥ y)) := by
    rw [LPData.Lmat, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hL, Matrix.dot_mulVec_eq_sum_sum]
  have hw : ∀ e, (Matrix.diagonal (d.cond x) *ᵥ ((Matrix.of d.A)ᵀ *ᵥ y)) e
      = d.cond x e * (∑ n, d.A n e * y n) := by
    intro e
    rw [Matrix.mulVec_diagonal]
    simp [Matrix.mulVec, dotProduct, of_apply, transpose_apply]
  simp only [hw, of_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_mul]
  have hs : (∑ n, y n * d.A n e) = ∑ n, d.A n e * y n :=
    Finset.sum_congr rfl fun n _ => by ring
  rw [hs]
  ring

/-- `L` has trivial kernel: full row rank kills the residual `Aᵀ y = 0`. -/
lemma LPData.Lmat_mulVec_eq_zero (d : LPData N E) {x : E → ℝ} (hx : ∀ e, 0 < x e)
    (hrank : d.FullRowRank) {y : N → ℝ} (hy : d.Lmat x *ᵥ y = 0) : y = 0 := by
  have h0 : y ⬝ᵥ (d.Lmat x *ᵥ y) = 0 := by
    rw [hy]
    simp
  rw [LPData.dot_Lmat] at h0
  have hnn : ∀ e ∈ (univ : Finset E), 0 ≤ d.cond x e * (∑ n, d.A n e * y n) ^ 2 :=
    fun e _ => mul_nonneg (le_of_lt (d.cond_pos hx e)) (sq_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0
  apply hrank
  intro e
  have he : d.cond x e * (∑ n, d.A n e * y n) ^ 2 = 0 := hzero e (Finset.mem_univ e)
  have hc := d.cond_pos hx e
  rcases mul_eq_zero.mp he with h | h
  · rw [h] at hc
    exact absurd hc (lt_irrefl 0)
  · exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp h

/-- Positive definiteness of `L` makes its `mulVec` injective. -/
theorem LPData.Lmat_injective (d : LPData N E) {x : E → ℝ} (hx : ∀ e, 0 < x e)
    (hrank : d.FullRowRank) : Function.Injective (d.Lmat x).mulVec := by
  intro y z hyz
  have h0 : d.Lmat x *ᵥ (y - z) = 0 := by
    rw [Matrix.mulVec_sub, hyz, sub_self]
  exact sub_eq_zero.mp (d.Lmat_mulVec_eq_zero hx hrank h0)

/-! ## The Kirchhoff system is solvable -/

/-- The solve itself: `L p = b` has a solution for every right-hand side `b`. -/
theorem LPData.exists_potential (d : LPData N E) {x : E → ℝ} (hx : ∀ e, 0 < x e)
    (hrank : d.FullRowRank) : ∃ p : N → ℝ, d.Lmat x *ᵥ p = d.b := by
  have hinj : Function.Injective (d.Lmat x).mulVecLin := by
    intro y z hyz
    refine d.Lmat_injective hx hrank ?_
    simpa [Matrix.mulVecLin_apply] using hyz
  have hsurj : Function.Surjective (d.Lmat x).mulVecLin :=
    LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨p, hp⟩ := hsurj d.b
  exact ⟨p, by simpa [Matrix.mulVecLin_apply] using hp⟩

/-! ## The discharge of the `Step` seam -/

/--
**M6: the electrical-network seam is discharged.** For every strictly positive `x`
and every full-row-rank `LPData`, the bundle `d.Step x` — flow, potentials,
Kirchhoff, Ohm, and Thomson's principle — is inhabited by construction.
-/
theorem LPData.exists_step (d : LPData N E) (x : E → ℝ) (hx : ∀ e, 0 < x e)
    (hrank : d.FullRowRank) : Nonempty (d.Step x) := by
  obtain ⟨p, hp⟩ := d.exists_potential hx hrank
  -- the flow `q = C Aᵀ p`, written as a diagonal `mulVec`
  obtain ⟨q, hq⟩ : ∃ q : E → ℝ,
      q = Matrix.diagonal (d.cond x) *ᵥ ((Matrix.of d.A)ᵀ *ᵥ p) := ⟨_, rfl⟩
  have hqapply : ∀ e, q e = d.cond x e * ((Matrix.of d.A)ᵀ *ᵥ p) e := by
    intro e
    rw [hq, Matrix.mulVec_diagonal]
  have hcanon : ∀ e, d.c e / x e * d.cond x e = 1 := by
    intro e
    rw [← LPData.res]
    exact d.res_mul_cond hx e
  -- Kirchhoff in vector form: `A q = L p = b`
  have hAq : Matrix.of d.A *ᵥ q = d.b := by
    have hL : d.Lmat x *ᵥ p = Matrix.of d.A *ᵥ q := by
      rw [hq, LPData.Lmat, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [← hL, hp]
  -- Ohm's law, pointwise
  have hohm : ∀ e, d.c e / x e * q e = ∑ n, d.A n e * p n := by
    intro e
    rw [hqapply e]
    calc d.c e / x e * (d.cond x e * ((Matrix.of d.A)ᵀ *ᵥ p) e)
        = (d.c e / x e * d.cond x e) * ((Matrix.of d.A)ᵀ *ᵥ p) e := by ring
      _ = ((Matrix.of d.A)ᵀ *ᵥ p) e := by rw [hcanon e, one_mul]
      _ = ∑ n, d.A n e * p n := d.dualVec_apply p e
  -- the cross term of Thomson's energy computation vanishes
  have hcross : ∀ f : E → ℝ, Matrix.of d.A *ᵥ f = d.b →
      ∑ e, d.c e / x e * q e * (f - q) e = 0 := by
    intro f hf
    have hAg : Matrix.of d.A *ᵥ (f - q) = 0 := by
      rw [Matrix.mulVec_sub, hf, hAq, sub_self]
    have hterm : ∀ e, d.c e / x e * q e * (f - q) e
        = ((Matrix.of d.A)ᵀ *ᵥ p) e * (f - q) e := by
      intro e
      rw [hqapply e]
      calc d.c e / x e * (d.cond x e * ((Matrix.of d.A)ᵀ *ᵥ p) e) * (f - q) e
          = (d.c e / x e * d.cond x e)
              * (((Matrix.of d.A)ᵀ *ᵥ p) e * (f - q) e) := by ring
        _ = ((Matrix.of d.A)ᵀ *ᵥ p) e * (f - q) e := by rw [hcanon e, one_mul]
    calc ∑ e, d.c e / x e * q e * (f - q) e
        = ∑ e, ((Matrix.of d.A)ᵀ *ᵥ p) e * (f - q) e :=
            Finset.sum_congr rfl fun e _ => hterm e
      _ = ∑ e, (∑ n, d.A n e * p n) * (f - q) e := by
            simp only [LPData.dualVec_apply]
      _ = ∑ e, ∑ n, (d.A n e * p n) * (f - q) e := by
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [Finset.sum_mul]
      _ = ∑ n, ∑ e, (d.A n e * p n) * (f - q) e := Finset.sum_comm
      _ = ∑ n, p n * ∑ e, d.A n e * (f - q) e := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun e _ => by ring
      _ = ∑ n, p n * (0 : ℝ) := by
            refine Finset.sum_congr rfl fun n _ => ?_
            congr 1
            have hn := congrFun hAg n
            simpa [Matrix.mulVec, dotProduct, of_apply] using hn
      _ = 0 := by simp
  refine ⟨{ q := q, p := p, hflow := ?_, ohm := hohm, thomson := ?_ }⟩
  · -- Kirchhoff's law
    intro n
    have hn := congrFun hAq n
    simpa [Matrix.mulVec, dotProduct, of_apply] using hn
  · -- Thomson's principle
    intro f hf
    have hAf : Matrix.of d.A *ᵥ f = d.b := by
      funext n
      simpa [Matrix.mulVec, dotProduct, of_apply] using hf n
    have hc := hcross f hAf
    have hkey : ∀ e, d.c e / x e * f e ^ 2
        = d.c e / x e * q e ^ 2 + d.c e / x e * (f - q) e ^ 2
          + 2 * (d.c e / x e * q e * (f - q) e) := by
      intro e
      simp only [Pi.sub_apply]
      ring
    have hnn : 0 ≤ ∑ e, d.c e / x e * (f - q) e ^ 2 := by
      refine Finset.sum_nonneg fun e _ => ?_
      have hpos : 0 < d.c e / x e := div_pos (d.hc e) (hx e)
      exact mul_nonneg (le_of_lt hpos) (sq_nonneg _)
    have hsum : ∑ e, d.c e / x e * f e ^ 2
        = ∑ e, d.c e / x e * q e ^ 2 + ∑ e, d.c e / x e * (f - q) e ^ 2
          + 2 * ∑ e, d.c e / x e * q e * (f - q) e := by
      calc ∑ e, d.c e / x e * f e ^ 2
          = ∑ e, (d.c e / x e * q e ^ 2 + d.c e / x e * (f - q) e ^ 2
              + 2 * (d.c e / x e * q e * (f - q) e)) :=
              Finset.sum_congr rfl fun e _ => hkey e
        _ = ∑ e, d.c e / x e * q e ^ 2 + ∑ e, d.c e / x e * (f - q) e ^ 2
              + 2 * ∑ e, d.c e / x e * q e * (f - q) e := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hfinal : ∑ e, d.c e / x e * f e ^ 2
        = ∑ e, d.c e / x e * q e ^ 2 + ∑ e, d.c e / x e * (f - q) e ^ 2 := by
      rw [hsum, hc]
      ring
    linarith [hnn, hfinal]

/-! ## Bridge to the trajectory layer

M6 discharges the *per-point* seam. The trajectory seam (`LPData.Solution`) carries the
same three laws at every time; this shows the two spokes are the same interface, so a
consumer may move between the static and the dynamic formulation without changing the
electrical vocabulary. Global existence of a `Solution` is M7 and is *not* claimed here.
-/

/-- The per-time electrical data of a global solution is a `Step`. -/
def LPData.Solution.step (d : LPData N E) (S : d.Solution) (t : ℝ) : d.Step (S.x t) where
  q := S.q t
  p := S.p t
  hflow := S.hflow t
  ohm := S.ohm t
  thomson := S.thomson t

/-- Conversely every global solution can be re-read pointwise through `exists_step`:
its data at any time inhabits the `Step` bundle. (Existence of `S` itself is the M7
seam; this only records that the two seams agree.) -/
theorem LPData.Solution.step_nonempty (d : LPData N E) (S : d.Solution) (t : ℝ) :
    Nonempty (d.Step (S.x t)) :=
  ⟨LPData.Solution.step d S t⟩
