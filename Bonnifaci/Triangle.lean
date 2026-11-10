/- Copyright (c) 2026 MultiAgency bonifaci-lane. -/
import Bonnifaci.NetworkRank

noncomputable section

/-!
# The triangle: a positive-length cycle admits no tight potential, hence no rest point

`ShortestPath.lean` carries an honest scope note (`STMTS.md` §9.6.3): a rest point with `q = x`
forces Ohm's law to read `p(head e) − p(tail e) = len e` on **every** edge simultaneously
(`Network.fixed_point_potentials_tight`), so in the interior a rest point exists only when the
lengths are *conservative* — a gradient. On a graph with a positive-length cycle there is no such
potential. The note was prose. This file makes it machine-checkable at the smallest witness.

## What is proved

| declaration | content |
|---|---|
| `triangle` | the directed cycle `0 → 1 → 2 → 0` with lengths `a`, `b`, `c` |
| `triangle_connected` | it is connected (the `path3_connected` pattern, one extra edge) |
| `triangle_telescope` | **the cycle identity**: for *any* `P`, `∑_e (P(head e) − P(tail e)) = 0` |
| `triangle_no_tight_potential` | no `P` is tight on all three edges: the three equations telescope to `0 = a + b + c > 0` |
| `triangle_groundLPData_step_nonempty` | the Laplacian layer *accepts* the triangle: `Step x` exists for every `x > 0` |
| `triangle_no_fixed_point` | **the scope note, machine-checked**: no rest point at any positive tube vector, for any demand |

## Why `triangle_connected` and `triangle_no_fixed_point` belong in the same file

They are the two halves of the boundary, and stating only one would mislead. The triangle is
**connected**, so `groundLPData_fullRowRank` applies and M6's `exists_step` fires: the electrical
solve at `x` exists, with Kirchhoff potentials, Ohm's law and Thomson's principle — nothing about
the rank hypothesis or the Laplacian layer obstructs this graph. What fails is *only* the rest
condition: a fixed point would make those potentials tight on all three edges, and the cycle
identity forbids it. So the §9.6.3 caveat is not a defect of the rank bridge, the grounding, or
the `Step` bundle — it is a property of the lengths. That is the honest reading, and it is now
checked rather than asserted.

## Layer discipline (campaign constraint (a))

Finite real arithmetic over `∑` and `Fin 3` case analysis. The only import is this project's own
`Bonnifaci.NetworkRank` (already built), so the import closure adds **zero** unbuilt Mathlib
modules. No new modelling: `triangle` is a `Network`, the negation is a statement about reals.
-/

open Finset

namespace Bonnifaci

/-- **The triangle graph** `0 → 1 → 2 → 0` with strictly positive edge lengths `a`, `b`, `c`.
Edges: `0 : 0→1`, `1 : 1→2`, `2 : 2→0`. The smallest graph with a cycle, hence the smallest
witness of §9.6.3's scope note. -/
def triangle (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : Network (Fin 3) (Fin 3) where
  tail := ![0, 1, 2]
  head := ![1, 2, 0]
  len := ![a, b, c]
  hlen := by
    intro e
    fin_cases e <;> assumption

/-- **The triangle is connected.** Same reachability pattern as `path3_connected`: walk from `0`
to `1` to `2`, then re-chain backwards for an arbitrary pair. Nothing here needs the third edge
`2 → 0` for reachability (a cycle is still connected without closing it), but the witness keeps
all three edges because the *tightness* argument needs them. -/
theorem triangle_connected (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (triangle a b c ha hb hc).Connected := by
  intro v w
  have hstep01 : (triangle a b c ha hb hc).Adj 0 1 := ⟨0, Or.inl ⟨rfl, rfl⟩⟩
  have hstep12 : (triangle a b c ha hb hc).Adj 1 2 := ⟨1, Or.inl ⟨rfl, rfl⟩⟩
  have h0 : ∀ u : Fin 3, Relation.ReflTransGen (triangle a b c ha hb hc).Adj 0 u := by
    intro u
    fin_cases u
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep01
    · exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep01) hstep12
  exact ((triangle a b c ha hb hc).reflTransGen_comm (h0 v)).trans (h0 w)

/-- **The cycle identity.** For *any* potential `P`, the potential differences around the triangle
sum to zero: the heads `1, 2, 0` and the tails `0, 1, 2` are the same set of nodes in a different
order, so the two sums are equal term by term after reindexing. This is the entire content of
"telescoping"; the rest of the file is bookkeeping about lengths. -/
theorem triangle_telescope (P : Fin 3 → ℝ) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∑ e : Fin 3, (P ((triangle a b c ha hb hc).head e)
        - P ((triangle a b c ha hb hc).tail e))) = 0 := by
  simp [triangle, Fin.sum_univ_three]
  ring

/-- **No potential is tight on every edge of a positive-length cycle.** The three tightness
equations `P 1 − P 0 = a`, `P 2 − P 1 = b`, `P 0 − P 2 = c` add to `0 = a + b + c`, which positivity
refutes. Stated as non-existence, which is exactly how §9.6.3 phrased the caveat — now a theorem
about a concrete graph rather than a claim about all of them. -/
theorem triangle_no_tight_potential (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ¬ ∃ P : Fin 3 → ℝ, ∀ e : Fin 3,
      P ((triangle a b c ha hb hc).head e) - P ((triangle a b c ha hb hc).tail e)
        = (triangle a b c ha hb hc).len e := by
  rintro ⟨P, hP⟩
  have hzero := triangle_telescope P a b c ha hb hc
  have hsum : (∑ e : Fin 3, (P ((triangle a b c ha hb hc).head e)
      - P ((triangle a b c ha hb hc).tail e))) = a + b + c := by
    rw [Finset.sum_congr rfl fun e _ => hP e]
    simp [triangle, Fin.sum_univ_three]
  rw [hsum] at hzero
  linarith

/-- **The Laplacian layer accepts the triangle.** Every strictly positive tube vector on the cycle
has an electrical flow, Kirchhoff potentials, Ohm's law, and Thomson's principle — the rank
hypothesis comes from `triangle_connected`, not from anything about the lengths. Stated so the next
theorem cannot be misread as "the triangle is outside the theory": it is inside it, and *only* the
rest condition fails. -/
theorem triangle_groundLPData_step_nonempty (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (s t g : Fin 3) (x : Fin 3 → ℝ) (hx : ∀ e, 0 < x e) :
    Nonempty (((triangle a b c ha hb hc).groundLPData s t g).Step x) :=
  (triangle a b c ha hb hc).groundLPData_exists_step s t g
    (triangle_connected a b c ha hb hc) x hx

/-- **§9.6.3's scope note, machine-checked: the triangle has no rest point.** At any strictly
positive tube vector and for **any** demand `s`, `t`, if `st` is the electrical solve then `q = x`
is impossible: at a rest point Ohm's law collapses to `fixed_point_potentials_tight`, which would
supply precisely the tight potential `triangle_no_tight_potential` forbids.

The demand never enters — which is the structural point. Tightness at a rest point is a statement
about the *lengths alone*; the right-hand side only shapes which flow satisfies Kirchhoff. So the
obstruction is conservativity of the lengths, exactly as the prose said. -/
theorem triangle_no_fixed_point (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (s t : Fin 3) (x : Fin 3 → ℝ) (hx : ∀ e, 0 < x e)
    (st : ((triangle a b c ha hb hc).toLPData s t).Step x) :
    ¬ ((triangle a b c ha hb hc).toLPData s t).IsFixedPoint x st := by
  intro hfp
  exact triangle_no_tight_potential a b c ha hb hc
    ⟨st.p, fun e => (triangle a b c ha hb hc).fixed_point_potentials_tight hx st hfp e⟩

/-! ## Positive control: the tree *does* admit a tight potential

The negation above would be cheap if the tightness system were unsatisfiable for trivial reasons
(a type mismatch, a wrong vector literal). It is not: on the *path* the same system is solvable,
and the solution is the distance function `path3Dist` that `ShortestPath.lean` already uses. So the
pair is a differential — a tree has a tight potential, a positive-length cycle does not — which is
the claim §9.6.3 actually makes. -/

/-- **A tree has a tight potential** — `path3Dist` is tight on both edges of `0 → 1 → 2`. The
control arm for `triangle_no_tight_potential`: same formulation, conservative lengths, solvable. -/
theorem path3_tight_potential (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ P : Fin 3 → ℝ, ∀ e : Fin 2,
      P ((path3 a b ha hb).head e) - P ((path3 a b ha hb).tail e) = (path3 a b ha hb).len e :=
  ⟨path3Dist a b, by
    intro e
    fin_cases e <;> simp [path3, path3Dist]⟩

end Bonnifaci
