/-
Copyright (c) 2026 MultiAgency bonifaci-lane.
-/
import Bonnifaci.M6
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

/-!
# M7 — the flow map `x ↦ q(x)` is well defined

`Model.lean` quarantined the electrical solve into `LPData.Step`; `M6` discharges it by
constructing an inhabitant for every strictly positive `x`. That leaves the next seam:
the ODE `ẋ = q(x) − x` is only a *relation* until the flow is shown to be unique at each
point. This file closes that gap.

## What is proved here (nothing assumed)

* `res_energy_eq_zero` — a flow that is Kirchhoff-homogeneous with a gradient resistance
  image has zero resistance energy. Same energy computation as Thomson's principle
  (M6), read as an identity rather than an inequality.
* `flow_eq_of_kirchhoff_ohm` — **at each `x > 0` the flow is unique.**
* `potential_eq_of_ohm` — with `A` of full row rank, Ohm pins the potentials too.
* `step_unique`, `step_p_unique`, `existsUnique_flow` — the electrical data at a point
  is unique, so `LPData.qfun` is a genuine function of `x`, not a choice.
* `LPData.Solution.q_eq_qfun` — any global trajectory's flow at time `t` *is*
  `qfun (x t)`: the trajectory and the flow map are the same object.

## What is named, not proved (the two remaining analytic seams)

* `LPData.FlowLipschitzOnOrthant` — local Lipschitz continuity of `qfun` on the positive
  orthant, Picard–Lindelöf's hypothesis. It is a statement about the rational map
  `x ↦ (A diag(x/c) Aᵀ)⁻¹ b`. Deliberately *not* asserted: no `axiom`, no `sorry`, no
  opaque constant — the Prop is stated and a consumer carries it as a hypothesis.
* `LPData.HasSolution` — existence of the trajectory for a strictly positive start, the
  paper's [18, Thm 1.1] (Straszak–Vishnoi), quoted not re-proved.

Because `qfun` is now provably a function, both seams are stated over the flow itself
rather than over a bundle argument — that is what well-definedness buys.
-/

set_option linter.unusedSectionVars false

open Finset

variable {N E : Type*} [Fintype N] [Fintype E] [DecidableEq N] [DecidableEq E]

/-! ## The energy identity that forces uniqueness -/

/--
A flow `g` that is Kirchhoff-homogeneous (`A g = 0`) and whose resistance image is a
gradient (`R g = Aᵀ r`) has zero resistance energy: `∑ (c/x) g² = 0`.
-/
theorem LPData.res_energy_eq_zero (d : LPData N E) (x : E → ℝ) (g : E → ℝ) (r : N → ℝ)
    (hA : ∀ n, ∑ e, d.A n e * g e = 0)
    (hR : ∀ e, d.c e / x e * g e = ∑ n, d.A n e * r n) :
    ∑ e, d.c e / x e * g e ^ 2 = 0 := by
  calc ∑ e, d.c e / x e * g e ^ 2
      = ∑ e, (d.c e / x e * g e) * g e := by
          refine Finset.sum_congr rfl fun e _ => ?_
          ring
    _ = ∑ e, (∑ n, d.A n e * r n) * g e := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [hR e]
    _ = ∑ e, ∑ n, (d.A n e * r n) * g e := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul]
    _ = ∑ n, ∑ e, (d.A n e * r n) * g e := Finset.sum_comm
    _ = ∑ n, r n * ∑ e, d.A n e * g e := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
    _ = 0 := by
          refine Finset.sum_eq_zero fun n _ => ?_
          rw [hA n, mul_zero]

/-- Ohm's law for a difference of two `Step`s: `R (q − q') = Aᵀ (p − p')`. -/
lemma LPData.ohm_sub (d : LPData N E) {x : E → ℝ} {st st' : d.Step x} (e : E) :
    d.c e / x e * (st.q e - st'.q e) = ∑ n, d.A n e * (st.p n - st'.p n) := by
  have h1 := st.ohm e
  have h2 := st'.ohm e
  calc d.c e / x e * (st.q e - st'.q e)
      = d.c e / x e * st.q e - d.c e / x e * st'.q e := by ring
    _ = (∑ n, d.A n e * st.p n) - (∑ n, d.A n e * st'.p n) := by rw [h1, h2]
    _ = ∑ n, d.A n e * (st.p n - st'.p n) := by
        simp only [mul_sub, Finset.sum_sub_distrib]

/-! ## Uniqueness of the electrical data -/

/--
**The core of M7.** Two flows satisfying Kirchhoff's law against the same `b` and Ohm's
law against *some* potentials coincide. Full row rank is not needed for the flow; it
enters only when reading off the potentials (`potential_eq_of_ohm`).
-/
theorem LPData.flow_eq_of_kirchhoff_ohm (d : LPData N E) (x : E → ℝ) (hx : ∀ e, 0 < x e)
    {q q' : E → ℝ} {p p' : N → ℝ}
    (h1 : ∀ n, ∑ e, d.A n e * q e = d.b n)
    (h2 : ∀ n, ∑ e, d.A n e * q' e = d.b n)
    (ho1 : ∀ e, d.c e / x e * q e = ∑ n, d.A n e * p n)
    (ho2 : ∀ e, d.c e / x e * q' e = ∑ n, d.A n e * p' n) : q = q' := by
  have hA : ∀ n, ∑ e, d.A n e * (q e - q' e) = 0 := by
    intro n
    simp only [mul_sub, Finset.sum_sub_distrib, h1 n, h2 n, sub_self]
  have hR : ∀ e, d.c e / x e * (q e - q' e) = ∑ n, d.A n e * (p n - p' n) := by
    intro e
    calc d.c e / x e * (q e - q' e)
        = d.c e / x e * q e - d.c e / x e * q' e := by ring
      _ = (∑ n, d.A n e * p n) - (∑ n, d.A n e * p' n) := by rw [ho1 e, ho2 e]
      _ = ∑ n, d.A n e * (p n - p' n) := by
          simp only [mul_sub, Finset.sum_sub_distrib]
  have hzero := d.res_energy_eq_zero x (fun e => q e - q' e) (fun n => p n - p' n) hA hR
  have hterm : ∀ e, d.c e / x e * (q e - q' e) ^ 2 = 0 := by
    intro e
    have hnn : ∀ e ∈ (univ : Finset E), 0 ≤ d.c e / x e * (q e - q' e) ^ 2 := by
      intro e _
      exact mul_nonneg (le_of_lt (div_pos (d.hc e) (hx e))) (sq_nonneg _)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero e (Finset.mem_univ e)
  funext e
  have hpos : 0 < d.c e / x e := div_pos (d.hc e) (hx e)
  have hsq : (q e - q' e) ^ 2 = 0 := by
    rcases mul_eq_zero.mp (hterm e) with h | h
    · rw [h] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact h
  exact sub_eq_zero.mp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp hsq)

/-- With `A` of full row rank, Ohm also pins the potentials. -/
theorem LPData.potential_eq_of_ohm (d : LPData N E) {x : E → ℝ}
    (hrank : d.FullRowRank) {q q' : E → ℝ} {p p' : N → ℝ}
    (hq : q = q')
    (ho1 : ∀ e, d.c e / x e * q e = ∑ n, d.A n e * p n)
    (ho2 : ∀ e, d.c e / x e * q' e = ∑ n, d.A n e * p' n) : p = p' := by
  subst hq
  funext n
  have hzero : ∀ e, ∑ n', d.A n' e * (p n' - p' n') = 0 := by
    intro e
    have h : (∑ n', d.A n' e * p n') = ∑ n', d.A n' e * p' n' := (ho1 e).symm.trans (ho2 e)
    calc ∑ n', d.A n' e * (p n' - p' n')
        = (∑ n', d.A n' e * p n') - (∑ n', d.A n' e * p' n') := by
            simp only [mul_sub, Finset.sum_sub_distrib]
      _ = 0 := by rw [h, sub_self]
  have hz := hrank (fun n' => p n' - p' n') hzero
  exact sub_eq_zero.mp (by simpa using congrFun hz n)

/-- Two inhabitants of `Step d x` carry the same flow. -/
theorem LPData.step_unique (d : LPData N E) {x : E → ℝ} (hx : ∀ e, 0 < x e)
    {st st' : d.Step x} : st.q = st'.q :=
  d.flow_eq_of_kirchhoff_ohm x hx st.hflow st'.hflow st.ohm st'.ohm

/-- Two inhabitants of `Step d x` carry the same potentials (needs full row rank). -/
theorem LPData.step_p_unique (d : LPData N E) {x : E → ℝ} (hx : ∀ e, 0 < x e)
    (hrank : d.FullRowRank) {st st' : d.Step x} : st.p = st'.p :=
  d.potential_eq_of_ohm hrank (d.step_unique hx) st.ohm st'.ohm

/--
The electrical data at `x` is not merely inhabited (M6) but **unique** — the pair
`(q, p)` is determined by Kirchhoff's and Ohm's laws alone.
-/
theorem LPData.existsUnique_flow (d : LPData N E) (x : E → ℝ) (hx : ∀ e, 0 < x e)
    (hrank : d.FullRowRank) :
    ∃! qp : (E → ℝ) × (N → ℝ),
      (∀ n, ∑ e, d.A n e * qp.1 e = d.b n) ∧
      (∀ e, d.c e / x e * qp.1 e = ∑ n, d.A n e * qp.2 n) := by
  obtain ⟨st⟩ := d.exists_step x hx hrank
  refine ⟨(st.q, st.p), ⟨st.hflow, st.ohm⟩, ?_⟩
  rintro ⟨q, p⟩ ⟨hflow, hohm⟩
  have hq : q = st.q :=
    d.flow_eq_of_kirchhoff_ohm x hx hflow st.hflow hohm st.ohm
  have hp : p = st.p := d.potential_eq_of_ohm hrank hq hohm st.ohm
  rw [hq, hp]

/-! ## The flow map as a function -/

/--
**The flow map `x ↦ q(x)`.** Chosen from M6's existence theorem; `qfun_eq_steps` proves
the choice does not matter, which is what makes this a function of `x`.
-/
def LPData.qfun (d : LPData N E) (x : E → ℝ) (hx : ∀ e, 0 < x e)
    (hrank : d.FullRowRank) : E → ℝ :=
  (Classical.choice (d.exists_step x hx hrank)).q

/-- `qfun` really is the flow carried by *any* `Step` at `x`. -/
theorem LPData.qfun_eq_steps (d : LPData N E) {x : E → ℝ} (hx : ∀ e, 0 < x e)
    (hrank : d.FullRowRank) (st : d.Step x) : st.q = d.qfun x hx hrank := by
  have h := d.step_unique (x := x) hx (st := st)
    (st' := Classical.choice (d.exists_step x hx hrank))
  simpa [LPData.qfun] using h

/-- The right-hand side of the Physarum ODE, `x ↦ q(x) − x`, as a function. -/
def LPData.rhs (d : LPData N E) (x : E → ℝ) (hx : ∀ e, 0 < x e)
    (hrank : d.FullRowRank) : E → ℝ :=
  d.qfun x hx hrank - x

/-- A global trajectory's flow at time `t` **is** the flow map evaluated at `x(t)`:
the trajectory and the well-defined flow speak one object. -/
theorem LPData.Solution.q_eq_qfun (d : LPData N E) (S : d.Solution) (t : ℝ)
    (hrank : d.FullRowRank) :
    S.q t = d.qfun (S.x t) (fun e => S.hpos t e) hrank :=
  d.qfun_eq_steps (fun e => S.hpos t e) hrank (LPData.Solution.step d S t)

/-! ## The two remaining seams, named

Neither is asserted. Both are Props a consumer may carry as a hypothesis, and both are
statable over the well-defined flow because of the theorems above.
-/

/--
**M7 seam 1 — local Lipschitz continuity of the flow map on the positive orthant.**

Picard–Lindelöf's hypothesis on the right-hand side `x ↦ q(x) − x`. The content is
continuity of matrix inversion composed with the rational map `x ↦ A diag(x/c) Aᵀ`,
plus a local bound. Stated over an arbitrary `Step` at each point; by `qfun_eq_steps`
that is the same as stating it over `qfun`.
-/
def LPData.FlowLipschitzOnOrthant (d : LPData N E) : Prop :=
  ∀ (x : E → ℝ) (_hx : ∀ e, 0 < x e) (st : d.Step x),
    ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (y : E → ℝ) (_hy : ∀ e, 0 < y e) (st' : d.Step y),
        (∀ e, |y e - x e| ≤ ε) →
        ∀ e, |st'.q e - st.q e| ≤ K * ∑ e, |y e - x e|

/--
**M7 seam 2 — existence of the trajectory.**

For a strictly positive feasible start the Physarum ODE has a solution: [SV16, Thm 1.1],
which the paper quotes as [18, Thm 1.1] and does *not* prove. Named, not assumed: a
consumer that needs it carries it as a hypothesis, and any object of type `Solution`
it produces is a solution by construction.
-/
def LPData.HasSolution (d : LPData N E) : Prop :=
  ∀ s : E → ℝ, (∀ e, 0 < s e) → d.FullRowRank → ∃ S : d.Solution, ∀ e, S.x 0 e = s e
