import Bonnifaci

/- Axiom banner. Only propext / Classical.choice / Quot.sound may appear.
   Set covers M1 scaffold, M2 (P1), M3/M4 (P2), M5 (P3 + mu-corollary),
   M6 (Laplacian-solve discharge) and M7 (flow well-definedness).
   The two M7 *seams* (`FlowLipschitzOnOrthant`, `HasSolution`) are `def`s of type
   `Prop`, i.e. named hypotheses a consumer carries — not axioms, not sorries. -/
#print axioms Bonnifaci.thm11_final
#print axioms Bonnifaci.thm11
#print axioms Bonnifaci.kl_deriv_le
#print axioms Bonnifaci.kl_deriv_sum
#print axioms Bonnifaci.cost_log_deriv_le
#print axioms Bonnifaci.sum_cq_le
#print axioms Bonnifaci.cost_deriv
#print axioms Bonnifaci.log_cost_deriv
#print axioms Bonnifaci.differentiable_kl_sum
#print axioms Bonnifaci.lem42_core
#print axioms Bonnifaci.duality_inner
#print axioms Bonnifaci.phi_decrease_core
#print axioms Bonnifaci.feasibility_invariant
#print axioms Bonnifaci.edge_no_retirement
#print axioms Bonnifaci.kl_bound_mu
#print axioms Bonnifaci.entropy_summand_le
#print axioms LPData.Lmat_injective
#print axioms LPData.exists_potential
#print axioms LPData.exists_step
#print axioms LPData.res_energy_eq_zero
#print axioms LPData.flow_eq_of_kirchhoff_ohm
#print axioms LPData.potential_eq_of_ohm
#print axioms LPData.step_unique
#print axioms LPData.step_p_unique
#print axioms LPData.existsUnique_flow
#print axioms LPData.qfun_eq_steps
#print axioms LPData.Solution.q_eq_qfun
