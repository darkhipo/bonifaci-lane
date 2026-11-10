/-
Copyright (c) 2026 MultiAgency bonifaci-lane.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section

/-!
# The linear-programming model of the Physarum dynamics

Finite-dimensional formalization of the LP setting of Bonifaci,
*"On the Convergence Time of a Natural Dynamics for Linear Programming"*
(arXiv:1611.06729, Algorithmica 82(2):300-315, 2020), Section 1.1.

**Layer discipline (campaign constraint (a)).** Everything in this file lives in the
real-arithmetic / optimization layer: finite index types, sums over `Finset`, real
numbers. Physarum's Laplacian-solve step is *quarantined* into the `Step` structure
(Kirchhoff + Ohm + Thomson), which downstream milestones may discharge by pure linear
algebra (positive definiteness of `L = A C Aᵀ`); no comparison-addition model is ever
formalized here.
-/

open Finset Real

variable {N E : Type*} [Fintype N] [Fintype E]

/-- The LP data of eq. (1) of [Bonifaci 2016]: constraint matrix `A ∈ ℝ^{N×E}`,
right-hand side `b`, and strictly positive costs `c`. The LP is
`min cᵀx s.t. A x = b, x ≥ 0`. -/
structure LPData (N E : Type*) [Fintype N] [Fintype E] where
  /-- Constraint matrix (full rankness is only needed for the Laplacian-solve layer,
  which enters here only through `Step`; hence not a field). -/
  A : N → E → ℝ
  /-- Right-hand side. -/
  b : N → ℝ
  /-- Strictly positive cost vector. -/
  c : E → ℝ
  /-- Cost positivity. -/
  hc : ∀ e, 0 < c e

/--
**The Laplacian-solve layer, quarantined.** `Step d x` bundles the output of the
electrical-network solve at the point `x` (Section 1.1 of [Bonifaci 2016]):
the electrical flow `q = C Aᵀ L⁻¹ b`, Kirchhoff potentials `p`, together with

* Kirchhoff's law: `A q = b`,
* Ohm's law: `R q = Aᵀ p` with `R = C⁻¹` diagonal (eq. (5) of the paper),
* Thomson's principle: `q` minimizes the dissipation `fᵀ R f` among Kirchhoff flows
  (Lemma 2.1 of the paper, proved there via a one-line energy computation).

This structure is the *named-premise seam* of the formalization: it is exactly the
content that Physarum's Laplacian solve contributes, expressed as real arithmetic.
Downstream milestones may prove that such a `Step` exists for every `x > 0` from
positive-definiteness of `L = A C Aᵀ`; no comparison-addition model appears.
-/
structure LPData.Step (d : LPData N E) (x : E → ℝ) where
  /-- Electrical flow. -/
  q : E → ℝ
  /-- Kirchhoff potentials. -/
  p : N → ℝ
  /-- Kirchhoff: `A q = b`. -/
  hflow : ∀ n, ∑ e, d.A n e * q e = d.b n
  /-- Ohm: `R q = Aᵀ p`. -/
  ohm : ∀ e, d.c e / x e * q e = ∑ n, d.A n e * p n
  /-- Thomson's principle (Lemma 2.1). -/
  thomson : ∀ f : E → ℝ, (∀ n, ∑ e, d.A n e * f e = d.b n) →
    ∑ e, d.c e / x e * q e ^ 2 ≤ ∑ e, d.c e / x e * f e ^ 2

/--
A global solution trajectory of the directed Physarum dynamics, eq. (3) of
[Bonifaci 2016]: `ẋ = q(t) − x(t)` where `q(t)` is the electrical flow at `x(t)`,
together with the per-time Laplacian-solve data (Kirchhoff, Ohm, Thomson).

**Named premise, global-solution seam.** Existence of such a trajectory for a given
strictly positive start is [Straszak–Vishnoi 2016, Thm 1.1], quoted as [18, Thm 1.1]
in the primary source. It is deliberately *not* an axiom here: any object of type
`Solution` is a solution by construction, and consumers state existence as a
hypothesis. Downstream milestone: discharge via Picard–Lindelöf on the positive
orthant (real-arithmetic layer).
-/
structure LPData.Solution (d : LPData N E) where
  /-- The tube vector `x(t)`. -/
  x : ℝ → E → ℝ
  /-- The electrical flow `q(t)`. -/
  q : ℝ → E → ℝ
  /-- Kirchhoff potentials `p(t)`. -/
  p : ℝ → N → ℝ
  /-- The trajectory lives in the positive orthant `Ω = ℝ_{>0}^E`. -/
  hpos : ∀ (t : ℝ) (e : E), 0 < x t e
  /-- Kirchhoff at each time. -/
  hflow : ∀ (t : ℝ) (n : N), ∑ e, d.A n e * q t e = d.b n
  /-- Ohm at each time: `R(t) q(t) = Aᵀ p(t)`. -/
  ohm : ∀ (t : ℝ) (e : E), d.c e / x t e * q t e = ∑ n, d.A n e * p t n
  /-- Thomson's principle at each time. -/
  thomson : ∀ (t : ℝ) (f : E → ℝ), (∀ n, ∑ e, d.A n e * f e = d.b n) →
    ∑ e, d.c e / x t e * q t e ^ 2 ≤ ∑ e, d.c e / x t e * f e ^ 2
  /-- Trajectory differentiability. -/
  hdiff : ∀ (t : ℝ) (e : E), DifferentiableAt ℝ (fun u => x u e) t
  /-- The ODE: `ẋ = q − x`. -/
  hode : ∀ (t : ℝ) (e : E), deriv (fun u => x u e) t = q t e - x t e

/- ## LP data accessors — declared at ROOT (not inside `namespace Bonnifaci`).
Dot notation `d.cost` resolves a declaration named `LPData.cost` in the root
namespace of the type head `LPData`; nesting these under `Bonnifaci` makes every
`d.cost` / `d.IsFeasible` / `d.IsFixedPoint` fail with "The environment does not
contain `LPData.cost`". -/

/-- The LP objective `cost(x) = cᵀx`. -/
def LPData.cost (d : LPData N E) (x : E → ℝ) : ℝ := ∑ e, d.c e * x e

/-- LP feasibility: `x ≥ 0` and `A x = b`. -/
def LPData.IsFeasible (d : LPData N E) (x : E → ℝ) : Prop :=
  (∀ e, 0 ≤ x e) ∧ ∀ n, ∑ e, d.A n e * x e = d.b n

/-- Edge resistance at a strictly positive point `x`: `r_j = c_j / x_j`
(the dynamically adjusted tube resistance). -/
def LPData.res (d : LPData N E) (x : E → ℝ) (e : E) : ℝ := d.c e / x e

/-- Energy dissipation `ℰ = qᵀ R q` of the electrical flow at `x`. -/
def LPData.energy (d : LPData N E) (x : E → ℝ) (st : LPData.Step d x) : ℝ :=
  ∑ e, d.c e / x e * st.q e ^ 2

/-- The dynamics is at rest: `q = x`. -/
def LPData.IsFixedPoint (d : LPData N E) (x : E → ℝ) (st : LPData.Step d x) : Prop :=
  ∀ e, st.q e = x e

namespace Bonnifaci

/-- Pointwise differentiability of a finite sum of scalar functions. -/
theorem differentiableAt_finset_sum {f : E → ℝ → ℝ} {t : ℝ}
    (h : ∀ e, DifferentiableAt ℝ (f e) t) :
    DifferentiableAt ℝ (fun u => ∑ e, f e u) t := by
  have h' : (fun u => ∑ e, f e u) = ∑ e, f e := by
    funext u; simp [Finset.sum_apply]
  rw [h']
  exact DifferentiableAt.sum (fun e _ => h e)

/-- Pointwise derivative of a finite sum of scalar functions. -/
theorem deriv_finset_sum {f : E → ℝ → ℝ} {t : ℝ}
    (h : ∀ e, DifferentiableAt ℝ (f e) t) :
    deriv (fun u => ∑ e, f e u) t = ∑ e, deriv (f e) t := by
  have h' : (fun u => ∑ e, f e u) = ∑ e, f e := by
    funext u; simp [Finset.sum_apply]
  rw [h']
  exact deriv_sum (fun e _ => h e)

end Bonnifaci
