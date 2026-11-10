/- Copyright (c) 2026 MultiAgency bonifaci-lane. -/
import Bonnifaci.Model
import Bonnifaci.Optimality

noncomputable section

/-!
# The network case (§2.2) — signed incidence, unit `s`–`t` demand, shortest paths

This file instantiates the LP of eq. (1) of [Bonifaci 2016] with the data the paper's
§2.2 singles out as the intuitive one: `A` is the **signed node–edge incidence matrix of a
directed graph**, `c` is a vector of strictly positive **edge lengths**, and `b` is the
**unit `s`–`t` demand** `δ_t − δ_s`. That LP is the shortest-path LP, so the paper's own
example is closed here rather than left as another named seam.

**Grounding (footnote 1 of §2.2).** The paper omits one node's row from `A` — "this
corresponds to grounding the potential value of this node to zero" — because the full
incidence matrix is rank-deficient. We keep the ground **row** in `A` (the identities and
the duality argument below never need full rank) and prove the two facts that make the
omission legitimate:

* `Network.feasible_sum_b_eq_zero` — feasibility forces `∑_v b_v = 0`, i.e. the `|V|`
  equations are never independent: at least one is implied by the others;
* `Network.groundRow_implied` — *which* one, explicitly: the equation at a chosen ground
  node `g` follows from the equations at every other node plus `∑_v b_v = 0`.

Grounding also fixes the gauge of the potentials, and that is where it is used: the
shortest-path statements are about `p t − p s`, and the source-anchored reading
`Network.distance_from_grounded_source` uses `p ground = 0` to turn that difference into
`p t` itself.

**What is actually proved (the identification).** In the network case the potentials of a
`Step` are the LP's dual variables, and the dual of the shortest-path LP is the classical
"feasible potential" system `p(head e) − p(tail e) ≤ len e`. The chain is:

| declaration | content |
|---|---|
| `Network.A_mul_potential` | the one structural identity: `∑_v A v e · P v = P(head e) − P(tail e)` |
| `Network.potential_inner_eq_edge_sum` | `∑_v P v · b v = ∑_e x_e · (P(head e) − P(tail e))` for any flow `x` |
| `Network.demand_inner` | for the unit `s`–`t` demand: `∑_v P v · b v = P t − P s` |
| `Network.dual_feasible_le_cost` | **weak duality**: a dual-feasible `P` bounds every feasible flow's cost from below |
| `Network.dual_feasible_bound` | hence `P t − P s ≤ L` for every dual-feasible `P`: feasible potentials *underestimate* the shortest-path value |
| `Network.cost_eq_potential_diff_of_tight` | tightness on the support atones for every inequality: the cost *equals* `P t − P s` |
| `Network.isShortestPathLength_of_tight` | **complementary slackness**: a dual-feasible `P` tight on the support of a feasible flow certifies that flow as shortest and `P t − p s` as the value |
| `Network.fixed_point_potentials_tight` | at a rest point Ohm's law makes `p` tight on *every* edge |
| `Network.fixed_point_potentials_are_distances` | **the identification**: at a rest point, `p t − p s` **is** the shortest-path value |
| `Network.distance_from_grounded_source` | with the ground node anchored at `0`, the potential `p t` **is** the distance from the grounded source |

**Honest scope note (same one `Optimality.lean` makes, now in the network case).** A rest
point with `q = x` forces `p(head e) − p(tail e) = len e` on *every* edge simultaneously, so
in the interior a rest point exists only when the lengths are conservative — on a graph with
a positive-length cycle it does not. The non-degenerate content is therefore
`isShortestPathLength_of_tight` (no rest point needed: any dual-feasible potential tight on
a feasible flow's support) plus `dual_feasible_bound` (every dual-feasible potential is a
lower bound). Together they say the shortest-path value is the **maximum** of `P t − P s`
over feasible potentials, and the rest-point theorems identify *which* potentials realise it.
The approach to optimality with thinning support is the KL potential's job — Theorem 1.1,
unchanged.

Layer discipline (campaign constraint (a)): everything here is finite real arithmetic over
`∑`; no Laplacian solve, no comparison-addition model. The import closure is
`Bonnifaci.Model` + `Bonnifaci.Optimality`, both already built on this pin — **zero new
unbuilt modules**.
-/

open Finset

namespace Bonnifaci

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- A directed graph with strictly positive edge lengths: the "network case" data of §2.2.
`head` and `tail` name the two ends of each edge; `len` is the edge cost `c` of eq. (1). -/
structure Network (V E : Type*) [Fintype V] [Fintype E] [DecidableEq V] where
  /-- The tail (`−1` end) of each edge. -/
  tail : E → V
  /-- The head (`+1` end) of each edge. -/
  head : E → V
  /-- Edge length; this is the LP cost vector `c`. -/
  len : E → ℝ
  /-- Costs are strictly positive (the LP's `c > 0` hypothesis). -/
  hlen : ∀ e, 0 < len e

/-- The unit `s`–`t` demand of §2.2: one unit leaving `s`, one unit arriving at `t`.
On the grounded node set this is the shortest-path right-hand side `b`. -/
def unitDemand {V : Type*} [Fintype V] [DecidableEq V] (s t : V) : V → ℝ :=
  fun v => (if v = t then (1 : ℝ) else 0) - (if v = s then (1 : ℝ) else 0)

/-- The unit demand has no net mass — this *is* the rank deficiency that licence the
ground row's omission (see `Network.groundRow_implied`). -/
theorem sum_unitDemand {V : Type*} [Fintype V] [DecidableEq V] (s t : V) :
    ∑ v, unitDemand s t v = 0 := by
  simp [unitDemand, Finset.sum_sub_distrib]

/-- The demand's inner product with a potential vector is the potential *difference*
between sink and source — the dual objective of the shortest-path LP. -/
theorem demand_inner {V : Type*} [Fintype V] [DecidableEq V] (s t : V) (P : V → ℝ) :
    ∑ v, P v * unitDemand s t v = P t - P s := by
  simp [unitDemand, Finset.sum_sub_distrib, mul_sub]

namespace Network

variable (G : Network V E)

/-- The signed node–edge incidence entry of edge `e` at node `v`: `+1` at the head, `−1` at
the tail, `0` elsewhere. This is the paper's constraint matrix `A` in the network case. -/
def A (v : V) (e : E) : ℝ :=
  (if G.head e = v then (1 : ℝ) else 0) - (if G.tail e = v then (1 : ℝ) else 0)

/-- **The one structural identity of the network case.** Summing the incidence column
against a potential vector collapses it to the potential difference across the edge —
which is why Ohm's law reads "potential difference = resistance times flow" and why the
dual variables of the shortest-path LP are node potentials. -/
theorem A_mul_potential (P : V → ℝ) (e : E) :
    ∑ v, G.A v e * P v = P (G.head e) - P (G.tail e) := by
  simp [A, Finset.sum_sub_distrib, sub_mul]

/-- Each incidence column sums to zero: every edge has one head and one tail. -/
theorem sum_A (e : E) : ∑ v, G.A v e = 0 := by
  simpa using G.A_mul_potential (fun _ => (1 : ℝ)) e

/-- **The LP of §2.2**, as `LPData`: constraint matrix the signed incidence, right-hand
side the unit `s`–`t` demand, cost vector the edge lengths. -/
def toLPData (s t : V) : LPData V E where
  A := G.A
  b := unitDemand s t
  c := G.len
  hc := G.hlen

/-- The objective of `toLPData` is the total length of the flow — the shortest-path
objective. -/
theorem toLPData_cost (s t : V) (x : E → ℝ) :
    (G.toLPData s t).cost x = ∑ e, G.len e * x e := rfl

/-- Feasibility for `toLPData` is exactly "nonnegative edge loads satisfying the unit
`s`–`t` demand at every node". -/
theorem toLPData_feasible (s t : V) (x : E → ℝ) :
    (G.toLPData s t).IsFeasible x ↔
      (∀ e, 0 ≤ x e) ∧ ∀ v, ∑ e, G.A v e * x e = unitDemand s t v :=
  Iff.rfl

/-- **Feasibility forces the demand to balance.** `∑_v b_v = 0` for any `b` that some flow
realises, so the `|V|` node equations of the incidence system are never independent: the
incidence matrix has a kernel vector (`1⃗`) on the left. -/
theorem feasible_sum_b_eq_zero {b : V → ℝ} (x : E → ℝ)
    (hflow : ∀ v, ∑ e, G.A v e * x e = b v) : ∑ v, b v = 0 := by
  calc ∑ v, b v = ∑ v, ∑ e, G.A v e * x e :=
        Finset.sum_congr rfl fun v _ => (hflow v).symm
    _ = ∑ e, ∑ v, G.A v e * x e := Finset.sum_comm
    _ = ∑ e, (∑ v, G.A v e) * x e := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul]
    _ = 0 := by simp [G.sum_A]

/-- **The ground row is implied.** Fix a ground node `g`. If a vector `x` satisfies the
node equations at every node except `g`, and the demand balances, then the equation at `g`
holds too. This is the licence for footnote 1 of §2.2: one row may be dropped, and the
remaining system has the same solution set. -/
theorem groundRow_implied (g : V) {b : V → ℝ} (x : E → ℝ)
    (hother : ∀ v, v ≠ g → ∑ e, G.A v e * x e = b v) (hsum : ∑ v, b v = 0) :
    ∑ e, G.A g e * x e = b g := by
  set f : V → ℝ := fun v => ∑ e, G.A v e * x e with hf
  have hfzero : ∑ v, f v = 0 := by
    rw [hf]
    exact G.feasible_sum_b_eq_zero x (fun _ => rfl)
  have key : ∑ v, (f v - b v) = 0 := by
    rw [Finset.sum_sub_distrib, hfzero, hsum, sub_self]
  have hsingle : ∑ v, (f v - b v) = f g - b g := by
    refine Finset.sum_eq_single g ?_ ?_
    · intro v _ hv
      show (∑ e, G.A v e * x e) - b v = 0
      rw [hother v hv, sub_self]
    · intro hg
      exact absurd (Finset.mem_univ g) hg
  rw [hsingle] at key
  exact sub_eq_zero.mp key

/-- **Duality in the network case, first half.** For any flow `x` realising `b`, the
demand's inner product with a potential vector equals the flow's sum of *potential drops*
across its edges. Everything below is this identity plus one inequality. -/
theorem potential_inner_eq_edge_sum {b : V → ℝ} (x : E → ℝ) (P : V → ℝ)
    (hflow : ∀ v, ∑ e, G.A v e * x e = b v) :
    ∑ v, P v * b v = ∑ e, x e * (P (G.head e) - P (G.tail e)) := by
  calc ∑ v, P v * b v
      = ∑ v, P v * (∑ e, G.A v e * x e) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [hflow v]
    _ = ∑ v, ∑ e, P v * (G.A v e * x e) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ e, ∑ v, P v * (G.A v e * x e) := Finset.sum_comm
    _ = ∑ e, x e * (∑ v, G.A v e * P v) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring
    _ = ∑ e, x e * (P (G.head e) - P (G.tail e)) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [G.A_mul_potential]

/-- **Weak duality (the shortest-path lower bound).** A *feasible potential* — one that
does not claim a drop larger than the edge length — bounds every feasible flow's total
length from below by `P t − P s`. This is the classical dual of the shortest-path LP, and
it is where the dynamics' potentials will be shown to live. -/
theorem dual_feasible_le_cost {s t : V} {x : E → ℝ} (P : V → ℝ)
    (hx : ∀ e, 0 ≤ x e)
    (hflow : ∀ v, ∑ e, G.A v e * x e = unitDemand s t v)
    (hdual : ∀ e, P (G.head e) - P (G.tail e) ≤ G.len e) :
    P t - P s ≤ ∑ e, G.len e * x e := by
  have hinner := G.potential_inner_eq_edge_sum x P hflow
  have hdemand : ∑ v, P v * unitDemand s t v = P t - P s := demand_inner s t P
  have hbound : ∑ e, x e * (P (G.head e) - P (G.tail e)) ≤ ∑ e, x e * G.len e :=
    Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hdual e) (hx e)
  calc P t - P s = ∑ v, P v * unitDemand s t v := hdemand.symm
    _ = ∑ e, x e * (P (G.head e) - P (G.tail e)) := hinner
    _ ≤ ∑ e, x e * G.len e := hbound
    _ = ∑ e, G.len e * x e := by
        refine Finset.sum_congr rfl fun e _ => by ring

/-- **Tightness atones for every inequality.** If the potential drop equals the edge length
on every edge the flow actually uses, the weak-duality inequality is an equality: the flow
costs exactly `P t − P s`. -/
theorem cost_eq_potential_diff_of_tight {s t : V} {x : E → ℝ} (P : V → ℝ)
    (hflow : ∀ v, ∑ e, G.A v e * x e = unitDemand s t v)
    (htight : ∀ e, x e ≠ 0 → P (G.head e) - P (G.tail e) = G.len e) :
    ∑ e, G.len e * x e = P t - P s := by
  have hinner := G.potential_inner_eq_edge_sum x P hflow
  have hdemand : ∑ v, P v * unitDemand s t v = P t - P s := demand_inner s t P
  have hpoint : ∀ e, x e * (P (G.head e) - P (G.tail e)) = x e * G.len e := by
    intro e
    by_cases h : x e = 0
    · rw [h, zero_mul, zero_mul]
    · rw [htight e h]
  have heq : ∑ e, x e * (P (G.head e) - P (G.tail e)) = ∑ e, x e * G.len e :=
    Finset.sum_congr rfl fun e _ => hpoint e
  calc ∑ e, G.len e * x e = ∑ e, x e * G.len e := by
        refine Finset.sum_congr rfl fun e _ => by ring
    _ = ∑ e, x e * (P (G.head e) - P (G.tail e)) := heq.symm
    _ = ∑ v, P v * unitDemand s t v := hinner.symm
    _ = P t - P s := hdemand

/-- `L` is the value of the §2.2 shortest-path LP: the minimum total length over flows
satisfying the unit `s`–`t` demand. Stated as an optimality predicate (a witness plus a
lower bound) rather than via `sInf`, so nothing about completeness of `ℝ` is needed. -/
def IsShortestPathLength (s t : V) (L : ℝ) : Prop :=
  (∃ x : E → ℝ, (∀ e, 0 ≤ x e) ∧
      (∀ v, ∑ e, G.A v e * x e = unitDemand s t v) ∧
      ∑ e, G.len e * x e = L) ∧
    ∀ x : E → ℝ, (∀ e, 0 ≤ x e) →
      (∀ v, ∑ e, G.A v e * x e = unitDemand s t v) →
      L ≤ ∑ e, G.len e * x e

/-- **Every feasible potential underestimates the shortest-path value.** This is the
direction that makes "distance" the *maximum* over feasible potentials. -/
theorem dual_feasible_bound {s t : V} {L : ℝ} (hL : G.IsShortestPathLength s t L)
    (P : V → ℝ) (hdual : ∀ e, P (G.head e) - P (G.tail e) ≤ G.len e) :
    P t - P s ≤ L := by
  obtain ⟨⟨x, hx, hflow, hcost⟩, _⟩ := hL
  rw [← hcost]
  exact G.dual_feasible_le_cost P hx hflow hdual

/-- **Complementary slackness — the identification, non-degenerate form.** A feasible
potential that is tight on the support of a feasible flow certifies *both*: the flow is a
shortest flow, and `P t − P s` is the shortest-path value. No rest point, no convergence,
no existence of a stationary state is assumed. -/
theorem isShortestPathLength_of_tight {s t : V} {x : E → ℝ} (P : V → ℝ)
    (hx : ∀ e, 0 ≤ x e)
    (hflow : ∀ v, ∑ e, G.A v e * x e = unitDemand s t v)
    (hdual : ∀ e, P (G.head e) - P (G.tail e) ≤ G.len e)
    (htight : ∀ e, x e ≠ 0 → P (G.head e) - P (G.tail e) = G.len e) :
    G.IsShortestPathLength s t (P t - P s) := by
  refine ⟨⟨x, hx, hflow, G.cost_eq_potential_diff_of_tight P hflow htight⟩, ?_⟩
  intro y hy hfy
  exact G.dual_feasible_le_cost P hy hfy hdual

/-- **At a rest point the potentials are tight on every edge.** Ohm's law
`(c_e/x_e) q_e = p(head e) − p(tail e)` combined with `q = x` leaves exactly the edge
length on the left-hand side. -/
theorem fixed_point_potentials_tight {s t : V} {x : E → ℝ} (hx : ∀ e, 0 < x e)
    (st : (G.toLPData s t).Step x) (hfp : (G.toLPData s t).IsFixedPoint x st) (e : E) :
    st.p (G.head e) - st.p (G.tail e) = G.len e := by
  have h := st.ohm e
  simp only [toLPData] at h
  rw [hfp e] at h
  rw [div_mul_cancel₀ _ (ne_of_gt (hx e))] at h
  rw [h, G.A_mul_potential]

/-- **The shortest-path identification corollary.** At a rest point of the Physarum
dynamics on the network instance of §2.2, the Kirchhoff potentials `p` are a *shortest-path
distance function*: `p t − p s` is the minimum total length over all flows satisfying the
unit `s`–`t` demand. This is the paper's own worked example, closed. -/
theorem fixed_point_potentials_are_distances {s t : V} {x : E → ℝ} (hx : ∀ e, 0 < x e)
    (st : (G.toLPData s t).Step x) (hfp : (G.toLPData s t).IsFixedPoint x st) :
    G.IsShortestPathLength s t (st.p t - st.p s) := by
  have hflowx : ∀ v, ∑ e, G.A v e * x e = unitDemand s t v := by
    intro v
    have hh := st.hflow v
    simp only [toLPData] at hh
    rw [← hh]
    exact Finset.sum_congr rfl fun e _ => by rw [hfp e]
  exact G.isShortestPathLength_of_tight st.p (fun e => le_of_lt (hx e)) hflowx
    (fun e => by rw [G.fixed_point_potentials_tight hx st hfp])
    (fun e _ => G.fixed_point_potentials_tight hx st hfp e)

/-- **The grounded-source reading (footnote 1 of §2.2).** Anchor the ground node's potential
at `0` and take the ground node as the source: then the potential at `t` **is** the
shortest-path distance from `s` to `t`, with no difference left to take. This is exactly what
grounding buys — the elimination of the additive gauge freedom. -/
theorem distance_from_grounded_source {ground t : V} {x : E → ℝ} (hx : ∀ e, 0 < x e)
    (st : (G.toLPData ground t).Step x) (hfp : (G.toLPData ground t).IsFixedPoint x st)
    (hgauge : st.p ground = 0) :
    G.IsShortestPathLength ground t (st.p t) := by
  have h := G.fixed_point_potentials_are_distances hx st hfp
  rwa [hgauge, sub_zero] at h

end Network

/-! ## A concrete instance: the three-node path graph

The corollary above is universally quantified, so it is worth one check that it is not
vacuous: a real graph, real lengths, and the distance function written down explicitly.
Take the path `0 → 1 → 2` with edge lengths `a` on `0 → 1` and `b` on `1 → 2`. The only flow
satisfying the unit `0`–`2` demand puts one unit on each edge, so the shortest-path value is
`a + b`, and the potential function `p = (0, a, a+b)` — the distance from the grounded
source `0` — is dual-feasible and tight. `isShortestPathLength_of_tight` then *reads off*
the identification, with no solve and no fixed point needed.

(The path is a tree, which is exactly why its lengths are conservative and a rest point
exists in the interior. On a graph with a positive-length cycle no such potential exists —
the honest scope note above.) -/

/-- The path graph `0 → 1 → 2` with edge lengths `a`, `b`. -/
def path3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Network (Fin 3) (Fin 2) where
  tail := ![0, 1]
  head := ![1, 2]
  len := ![a, b]
  hlen := by
    intro e
    fin_cases e <;> assumption

/-- The distance-from-node-`0` function on the path graph: `(0, a, a+b)`. -/
def path3Dist (a b : ℝ) : Fin 3 → ℝ := ![0, a, a + b]

/-- **The identification, concretely.** On the three-node path with lengths `a`, `b`, the
shortest-path value from `0` to `2` is `a + b` — and this is witnessed by the potential
function `path3Dist a b`, the distance from the grounded source. -/
theorem path3_shortestPath (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (path3 a b ha hb).IsShortestPathLength 0 2 (a + b) := by
  have hx : ∀ e : Fin 2, (0 : ℝ) ≤ 1 := fun _ => zero_le_one
  have hflow : ∀ v : Fin 3, ∑ e, (path3 a b ha hb).A v e * (1 : ℝ) = unitDemand 0 2 v := by
    intro v
    fin_cases v <;> simp [Network.A, path3, unitDemand]
  have hdual : ∀ e : Fin 2,
      path3Dist a b ((path3 a b ha hb).head e) - path3Dist a b ((path3 a b ha hb).tail e)
        ≤ (path3 a b ha hb).len e := by
    intro e
    fin_cases e <;> simp [path3, path3Dist]
  have htight : ∀ e : Fin 2, (1 : ℝ) ≠ 0 →
      path3Dist a b ((path3 a b ha hb).head e) - path3Dist a b ((path3 a b ha hb).tail e)
        = (path3 a b ha hb).len e := by
    intro e _
    fin_cases e <;> simp [path3, path3Dist]
  have h := (path3 a b ha hb).isShortestPathLength_of_tight (path3Dist a b)
    hx hflow hdual htight
  simpa [path3Dist] using h

end Bonnifaci
