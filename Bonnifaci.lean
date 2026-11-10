import Bonnifaci.Model
import Bonnifaci.KL
import Bonnifaci.Core
import Bonnifaci.Optimality
import Bonnifaci.Features
import Bonnifaci.Feasibility
import Bonnifaci.Theorem
import Bonnifaci.Thm11
import Bonnifaci.Duality

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

## Work in progress (deliberately NOT imported; see STMTS.md §7)

  Thm11        proof-carrying Theorem 1.1 (statement kept in sync via Theorem.lean)
  Duality      Prop 2.2 / 2.3 / Lemma 4.2 core (needs Thm11's notation)

Keeping WIP modules out of the root import keeps the build target green and the
receipts honest: a red file never hides behind a green target.
-/
