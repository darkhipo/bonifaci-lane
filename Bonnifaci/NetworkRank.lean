/- Copyright (c) 2026 MultiAgency bonifaci-lane. -/
import Bonnifaci.ShortestPath
import Bonnifaci.M6

noncomputable section

/-!
# The connectivity → `FullRowRank` bridge: the network case enters the Laplacian layer

`ShortestPath.lean` closed the §2.2 example up to one hypothesis it used and did not prove
(`STMTS.md` §9.6.2): that the **grounded reduced** incidence matrix of a connected graph has
full row rank. That is the precondition of the Laplacian solve — `LPData.FullRowRank`, the one
extra ingredient `M6`'s `exists_step` needs beyond `LPData`, and hence of the whole M6/M7 layer
(`exists_step`, `qfun`, `existsUnique_flow`) and of M8's Lipschitz discharge.

This file proves it, from connectivity alone.

## Why the *reduced* matrix, and why grounding is necessary rather than convenient

The full incidence matrix of a `Network` provably does **not** have full row rank:
`Network.toLPData_not_fullRowRank` exhibits `1⃗` as a nonzero kernel vector of `A` for *every*
network on a nonempty node set (on any node set with a node to evaluate at, in fact — the
witness `g` is the evaluation point). So the paper's footnote 1 — "we omit one node's row" — is
not a simplification of an already-full-rank matrix: it is the difference between a rank-deficient
system and a full-rank one. `Network.feasible_sum_b_eq_zero` in `ShortestPath.lean` already says
the same thing from the demand side (`∑_v b_v = 0` for any realisable `b`).

The reduction is `Network.groundLPData s t g`: the same incidence, demand and lengths, indexed by
the punctured node type `{v // v ≠ g}`. The bridge is

  `Network.groundLPData_fullRowRank` : `G.Connected → (G.groundLPData s t g).FullRowRank`.

## The proof, and why it is short

`FullRowRank` unfolds to: if `∑_v A_{ve} p_v = 0` for every edge `e`, then `p = 0`. By
`Network.A_mul_potential` the hypothesis reads `p(head e) = p(tail e)`; so the whole content is
*"a function constant across every edge of a connected graph is constant"*. Extend `p` to all of
`V` by `P g = 0`, split the `V`-sum at the ground node with
`Fintype.sum_eq_add_sum_subtype_ne` (the reduced system's equations are exactly the surviving
terms, and the ground term carries the factor `P g = 0`), and connectivity propagates `P g = 0`
to every node. Two ingredients, no induction over a search tree, no determinant.

Connectivity itself is `Network.Connected`, the standard reachability form: any two nodes are
joined by a `Relation.ReflTransGen` chain of the undirected adjacency `Network.Adj`. The induction
that consumes it is `Network.eq_of_reflTransGen` — invariant along one edge, hence along a chain.

## Layer discipline (campaign constraint (a))

Still finite real arithmetic and finite-dimensional linear algebra over `ℝ`. `M6` is imported for
one reason only: to *name the consumer* (`FullRowRank`, `exists_step`). Nothing here re-models the
electrical layer, and no new Mathlib module is pulled in: `Bonnifaci.ShortestPath` and
`Bonnifaci.M6` are both already built inside this target, so the import closure adds no unbuilt
module.
-/

open Finset

namespace Bonnifaci

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

namespace Network

variable (G : Network V E)

/-! ## Connectivity -/

/-- **Undirected adjacency.** `v` and `w` are the two ends of some edge, in either order. This is
the relation whose transitive closure is graph connectivity; `head`/`tail` are directional but
reachability is not. -/
def Adj (v w : V) : Prop :=
  ∃ e, (G.tail e = v ∧ G.head e = w) ∨ (G.head e = v ∧ G.tail e = w)

/-- Adjacency is symmetric — the reason reachability can be read in either direction. -/
theorem adj_comm {v w : V} (h : G.Adj v w) : G.Adj w v := by
  obtain ⟨e, h | h⟩ := h
  · exact ⟨e, Or.inr ⟨h.2, h.1⟩⟩
  · exact ⟨e, Or.inl ⟨h.2, h.1⟩⟩

/-- **One step.** A function whose value agrees across every edge agrees across any adjacent
pair. This is the induction step of the rank argument, isolated because it is the only place the
incidence structure is used. -/
theorem eq_of_adj {P : V → ℝ} (h : ∀ e, P (G.head e) = P (G.tail e)) {v w : V}
    (hvw : G.Adj v w) : P v = P w := by
  obtain ⟨e, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hvw
  · rw [← h1, ← h2]; exact (h e).symm
  · rw [← h1, ← h2]; exact h e

/-- **Along a chain.** The reachability induction: an edge-invariant function is constant along
any `ReflTransGen` chain of `Adj`. -/
theorem eq_of_reflTransGen {P : V → ℝ} (h : ∀ e, P (G.head e) = P (G.tail e)) {v w : V}
    (hvw : Relation.ReflTransGen G.Adj v w) : P v = P w := by
  induction hvw with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (G.eq_of_adj h hbc)

/-- **Reachability is symmetric**, because `Adj` is: a chain can be walked backwards. -/
theorem reflTransGen_comm {v w : V} (h : Relation.ReflTransGen G.Adj v w) :
    Relation.ReflTransGen G.Adj w v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (G.adj_comm hbc) ih

/-- **A connected graph**: any two nodes are joined by a chain of edges. This is the hypothesis
the rank bridge consumes, and `groundLPData_fullRowRank_iff` shows it is also *necessary* — the
bridge is an equivalence, not a sufficient condition with slack. -/
def Connected : Prop :=
  ∀ v w : V, Relation.ReflTransGen G.Adj v w

/-- Connectedness, consumed: an edge-invariant function on a connected graph is constant. -/
theorem eq_const_of_connected (hconn : G.Connected) {P : V → ℝ}
    (h : ∀ e, P (G.head e) = P (G.tail e)) (v w : V) : P v = P w :=
  G.eq_of_reflTransGen h (hconn v w)

/-! ## The grounded reduced LP data -/

/-- **The grounded reduction of footnote 1.** The network's incidence, demand and lengths with the
node `g`'s row **omitted**: the constraint matrix is `V ∖ {g} → E → ℝ`, the right-hand side the
unit `s`–`t` demand restricted to the surviving rows. This is the object the Laplacian layer sees;
`Network.toLPData` keeps the ground row, which is why it is rank-deficient. -/
def groundLPData (s t : V) (g : V) : LPData {v // v ≠ g} E where
  A := fun n e => G.A (n : V) e
  b := fun n => unitDemand s t (n : V)
  c := G.len
  hc := G.hlen

/-- The reduced matrix's rows are the network's rows, restricted. Definitional, recorded because
downstream rewrites want the bridge spelled out (cf. the `toLPData` finding, `STMTS.md` §9.6.1). -/
theorem groundLPData_A (s t g : V) (n : {v // v ≠ g}) (e : E) :
    (G.groundLPData s t g).A n e = G.A (n : V) e := rfl

/-- **The bridge, rooted form.** If every node is reachable from the ground node `g`, the grounded
reduced incidence matrix has full row rank. This is the form the proof actually establishes; the
connected version and the converse both derive from it.

This is the hypothesis `ShortestPath.lean` carried and did not prove (`STMTS.md` §9.6.2); after
this theorem, a `Network` instance can be handed to `LPData.exists_step` with nothing assumed
about its rank. -/
theorem groundLPData_fullRowRank_of_rooted (s t g : V)
    (hroot : ∀ v, Relation.ReflTransGen G.Adj g v) :
    (G.groundLPData s t g).FullRowRank := by
  intro p hp
  -- extend `p` to all of `V` by `0` at the ground node
  set P : V → ℝ := fun v => if h : v = g then 0 else p ⟨v, h⟩ with hPdef
  have hPg : P g = 0 := by
    simp only [hPdef]
    simp
  have hPn : ∀ n : {v // v ≠ g}, P (n : V) = p n := by
    intro n
    simp only [hPdef]
    simp [n.2]
  -- the extended `P` is invariant across every edge: split the `V`-sum at `g`
  have hinv : ∀ e, P (G.head e) = P (G.tail e) := by
    intro e
    have hsplit := Fintype.sum_eq_add_sum_subtype_ne (fun v => G.A v e * P v) g
    have hzero : ∑ v, G.A v e * P v = 0 := by
      rw [hsplit, hPg, mul_zero, zero_add]
      have hred : (∑ n : {v // v ≠ g}, G.A (n : V) e * P (n : V))
          = ∑ n : {v // v ≠ g}, (G.groundLPData s t g).A n e * p n :=
        Finset.sum_congr rfl fun n _ => by rw [G.groundLPData_A s t g n e, hPn n]
      rw [hred]
      exact hp e
    rw [G.A_mul_potential P e] at hzero
    exact sub_eq_zero.mp hzero
  funext n
  calc p n = P (n : V) := (hPn n).symm
    _ = P g := G.eq_of_reflTransGen hinv (G.reflTransGen_comm (hroot (n : V)))
    _ = 0 := hPg

/-- **The bridge.** A connected network's grounded reduced incidence matrix has full row rank. -/
theorem groundLPData_fullRowRank (s t g : V) (hconn : G.Connected) :
    (G.groundLPData s t g).FullRowRank :=
  G.groundLPData_fullRowRank_of_rooted s t g fun v => hconn g v

/-- **Connectivity is not merely sufficient — it is exactly the condition.** If the grounded
reduced incidence matrix has full row rank then every node is reachable from the ground node:
otherwise the indicator of the unreachable set is a nonzero kernel vector (`0` on reachable nodes,
`1` elsewhere). Reachability is closed under adjacency, so each reduced row equation holds; the
ground row that would have excluded it is precisely the one that was dropped.

Together with `groundLPData_fullRowRank_of_rooted` this says `FullRowRank` *is* graph connectivity
of the grounded network, so the hypothesis is neither vacuous nor stronger than needed. -/
theorem connected_of_groundLPData_fullRowRank (s t g : V)
    (h : (G.groundLPData s t g).FullRowRank) :
    ∀ v, Relation.ReflTransGen G.Adj g v := by
  classical
  intro w
  by_contra hw
  have hwne : w ≠ g := by
    rintro rfl
    exact hw Relation.ReflTransGen.refl
  -- the indicator of "not reachable from `g`", read on the punctured node type
  let p : {v // v ≠ g} → ℝ := fun n =>
    if Relation.ReflTransGen G.Adj g (n : V) then (0 : ℝ) else 1
  have hpzero : p = 0 := by
    refine h p ?_
    intro e
    -- the same indicator read on all of `V`; it vanishes at `g`
    set Q : V → ℝ := fun v =>
      if Relation.ReflTransGen G.Adj g v then (0 : ℝ) else 1 with hQ
    have hRg : Relation.ReflTransGen G.Adj g g := Relation.ReflTransGen.refl
    have hQg : Q g = 0 := by
      simp only [hQ]
      simp [hRg]
    have hinv : Q (G.head e) = Q (G.tail e) := by
      have hiff : Relation.ReflTransGen G.Adj g (G.head e)
          ↔ Relation.ReflTransGen G.Adj g (G.tail e) :=
        ⟨fun hr => Relation.ReflTransGen.tail hr ⟨e, Or.inr ⟨rfl, rfl⟩⟩,
         fun hr => Relation.ReflTransGen.tail hr ⟨e, Or.inl ⟨rfl, rfl⟩⟩⟩
      have hh := hiff
      simp only [hQ]
      by_cases hhd : Relation.ReflTransGen G.Adj g (G.head e)
      · have htd : Relation.ReflTransGen G.Adj g (G.tail e) := hh.mp hhd
        simp [hhd, htd]
      · have htd : ¬ Relation.ReflTransGen G.Adj g (G.tail e) := fun ht => hhd (hh.mpr ht)
        simp [hhd, htd]
    have hzero : ∑ v, G.A v e * Q v = 0 := by
      rw [G.A_mul_potential Q e, hinv, sub_self]
    have hstep : (∑ v, G.A v e * Q v)
        = ∑ n : {v // v ≠ g}, (G.groundLPData s t g).A n e * p n := by
      have hsplit := Fintype.sum_eq_add_sum_subtype_ne (fun v => G.A v e * Q v) g
      rw [hsplit, hQg, mul_zero, zero_add]
      exact Finset.sum_congr rfl fun n _ => by rw [G.groundLPData_A s t g n e]
    exact hstep ▸ hzero
  have hval : p ⟨w, hwne⟩ = 0 := by
    have := congrFun hpzero ⟨w, hwne⟩
    simpa using this
  have hone : p ⟨w, hwne⟩ = 1 := by
    have hnot : ¬ Relation.ReflTransGen G.Adj g w := hw
    dsimp only [p]
    simp [hnot]
  rw [hval] at hone
  exact one_ne_zero hone.symm

/-- **The rank bridge as an equivalence.** For a `Network`, the Laplacian layer's rank hypothesis
and graph connectivity of the grounded network are the same condition. -/
theorem groundLPData_fullRowRank_iff (s t g : V) :
    (G.groundLPData s t g).FullRowRank ↔ ∀ v, Relation.ReflTransGen G.Adj g v :=
  ⟨G.connected_of_groundLPData_fullRowRank s t g,
   G.groundLPData_fullRowRank_of_rooted s t g⟩

/-- **Grounding is necessary.** The *ungrounded* incidence system of `toLPData` never has full
row rank: `1⃗` satisfies every node equation (each edge has one head and one tail, so each column
sums to `0`, `Network.sum_A`) and is nonzero at the evaluation node `g`. So the paper's footnote 1
omits a row that *had* to go, and `groundLPData` is the honest object for the Laplacian layer. -/
theorem toLPData_not_fullRowRank (s t g : V) : ¬ (G.toLPData s t).FullRowRank := by
  intro h
  have hone : (fun _ : V => (1 : ℝ)) = (0 : V → ℝ) := by
    refine h (fun _ => 1) ?_
    intro e
    simp only [toLPData]
    simpa using G.sum_A e
  have hg := congrFun hone g
  simp at hg

/-! ## The consumer: `M6`'s `exists_step`, end to end on a network -/

/-- **A connected network instance inhabits the `Step` bundle.** This is the point of the bridge:
`LPData.exists_step` (M6) needs `FullRowRank`; for a network it is now a *theorem*, so no rank
hypothesis remains between §2.2's data and a full electrical solve — Kirchhoff, Ohm, and Thomson's
principle at every strictly positive tube vector. -/
theorem groundLPData_exists_step (s t g : V) (hconn : G.Connected) (x : E → ℝ)
    (hx : ∀ e, 0 < x e) : Nonempty ((G.groundLPData s t g).Step x) := by
  classical
  exact (G.groundLPData s t g).exists_step x hx (G.groundLPData_fullRowRank s t g hconn)

end Network

/-! ## Not vacuous: the path graph enters the Laplacian layer

`ShortestPath.lean` closed §2.2's example on the path `0 → 1 → 2` without ever constructing a
`Step` (§9.6.3 notes why: `isShortestPathLength_of_tight` needs no Laplacian solve). Now that
connectivity supplies the rank hypothesis, the same graph goes all the way through M6 — and the
*ungrounded* system on the same graph is rank-deficient, so the pair is a machine-checked
demonstration that grounding is the difference. -/

/-- **The path graph is connected.** Reachability from node `0`: `0 → 1 → 2`, walked backwards and
re-chained for an arbitrary pair. -/
theorem path3_connected (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (path3 a b ha hb).Connected := by
  intro v w
  have hstep01 : (path3 a b ha hb).Adj 0 1 := ⟨0, Or.inl ⟨rfl, rfl⟩⟩
  have hstep12 : (path3 a b ha hb).Adj 1 2 := ⟨1, Or.inl ⟨rfl, rfl⟩⟩
  have h0 : ∀ u : Fin 3, Relation.ReflTransGen (path3 a b ha hb).Adj 0 u := by
    intro u
    fin_cases u
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep01
    · exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep01) hstep12
  exact ((path3 a b ha hb).reflTransGen_comm (h0 v)).trans (h0 w)

/-- **The grounded path graph has full row rank** — the first concrete network instance the
Laplacian layer can accept with no rank hypothesis. -/
theorem path3_groundLPData_fullRowRank (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ((path3 a b ha hb).groundLPData 0 2 0).FullRowRank :=
  (path3 a b ha hb).groundLPData_fullRowRank 0 2 0 (path3_connected a b ha hb)

/-- The *same* graph, ungrounded: rank-deficient. Grounding is not cosmetic. -/
theorem path3_toLPData_not_fullRowRank (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ¬ ((path3 a b ha hb).toLPData 0 2).FullRowRank :=
  (path3 a b ha hb).toLPData_not_fullRowRank 0 2 0

/-- **The reduction really is the shortest-path right-hand side.** Grounding at the source `0`
turns the unit `0`–`2` demand into the unit vector at the sink: the surviving rows are `0` at
node `1` and `1` at node `2`, and the row that would have read `−1` (the source) is the one that
was dropped. -/
theorem path3_groundLPData_b (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (n : {v : Fin 3 // v ≠ 0}) :
    ((path3 a b ha hb).groundLPData 0 2 0).b n =
      (if (n : Fin 3) = 2 then (1 : ℝ) else 0) := by
  simp only [Network.groundLPData, unitDemand]
  simp [n.2]

/-- **End to end: the path graph inhabits M6's `Step` bundle.** Every strictly positive tube vector
on `0 → 1 → 2`, grounded at the source, has an electrical flow, Kirchhoff potentials, Kirchhoff's
law, Ohm's law, and Thomson's principle — all from M6, with the rank hypothesis supplied here by
`path3_connected`. -/
theorem path3_groundLPData_step_nonempty (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (x : Fin 2 → ℝ) (hx : ∀ e, 0 < x e) :
    Nonempty (((path3 a b ha hb).groundLPData 0 2 0).Step x) :=
  (path3 a b ha hb).groundLPData_exists_step 0 2 0 (path3_connected a b ha hb) x hx

end Bonnifaci
