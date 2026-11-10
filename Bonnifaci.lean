import Bonnifaci.Model
import Bonnifaci.KL
import Bonnifaci.Core
import Bonnifaci.Optimality
import Bonnifaci.Features
import Bonnifaci.Feasibility
import Bonnifaci.Theorem
import Bonnifaci.Thm11
import Bonnifaci.Duality
import Bonnifaci.Lemma41
import Bonnifaci.Lemma43
import Bonnifaci.Mu
import Bonnifaci.M6
import Bonnifaci.M7
import Bonnifaci.M8
import Bonnifaci.ShortestPath
import Bonnifaci.NetworkRank

/- Copyright (c) 2026 MultiAgency bonifaci-lane. -/
/-!
# bonifaci-lane — root module

Formalization of **Bonifaci 2016, Theorem 1.1** (Physarum dynamics, KL-type Lyapunov
potential, convex duality; campaign "road 2 GLOBAL POTENTIAL").

Primary source, verified against the full text on 2026-11-10 (STMTS.md §0):
  Vincenzo Bonifaci, "On the Convergence Time of a Natural Dynamics for Linear
  Programming", arXiv:1611.06729v1 (21 Nov 2016), Algorithmica 82(2):300-315, 2020,
  DOI 10.1007/s00453-019-00615-3.

## What this root target builds (all green, no sorry, no axiom)

  Model        LPData, Step (Laplacian-solve seam), Solution (ODE trajectory),
               cost / IsFeasible / res / energy / IsFixedPoint, sum-diff helpers
  KL           finite KL + Gibbs' inequality (KL_nonneg)
  Core         cs_step (Lemma 4.1 Cauchy-Schwarz step), phi_decrease_core (Lemma 4.4)
  Optimality   fixed point => exactly-tight dual certificate => LP optimality
  Features     edge_no_retirement (campaign constraint (b), as a theorem)
  Feasibility  Prop 3.1 + Lemma 3.2 => P1 DISCHARGED (feasibility_invariant)
  Theorem      the machine-checked statement of Theorem 1.1 with premises P1-P3 named
  Thm11        proof-carrying Theorem 1.1 (statement kept in sync via Theorem.lean)
  Duality      Prop 2.2 / 2.3 / Lemma 4.2 core
  Lemma41/43   the two d/dt bounds (P2, P3)
  Mu           the mu-corollary (Theorem 1.1, second half)
  M6           the Laplacian-solve seam DISCHARGED (exists_step from posDef L = A C A^T)
  M7           the flow map is well defined (existsUnique_flow, qfun, q_eq_qfun)
  M8           FlowLipschitzOnOrthant DISCHARGED (energy perturbation estimate)
  ShortestPath the network case of §2.2: signed incidence, unit s-t demand, and the
               shortest-path identification corollary (at a rest point the Kirchhoff
               potentials are a shortest-path distance function)
  NetworkRank  the connectivity -> FullRowRank bridge: a connected network's grounded
               reduced incidence matrix has full row rank (and the ungrounded one never
               does), so M6/M7's Laplacian layer accepts a network instance with no rank
               hypothesis; the path graph is carried through end to end

All seventeen modules above are green inside this target. One named Prop survives,
deliberate and documented in STMTS.md §9.3 (the earlier "two" was the pre-M8 count —
`FlowLipschitzOnOrthant` became a theorem in M8):

  `LPData.HasSolution`      — global existence of the trajectory (SV16, the paper's [18]).
                              Kept named: the ODE library it would need closes over 6616
                              unbuilt modules on this pin, and the statement asks for a
                              global two-sided solution, which Picard-Lindeloef does not
                              give. Its analytic hypothesis is no longer a gap: M8 proves
                              the flow and the ODE right-hand side are locally Lipschitz.

Anything added here must build green. A red file never hides behind a green target.
-/
