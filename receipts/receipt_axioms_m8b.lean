import Bonnifaci

-- M8b: the shortest-path instantiation (§2.2 network case).
-- Every declaration added by Bonnifaci/ShortestPath.lean, with its axiom footprint.

-- plumbing: signed incidence, unit s-t demand, the LPData instance
#print axioms Bonnifaci.sum_unitDemand
#print axioms Bonnifaci.demand_inner
#print axioms Bonnifaci.Network.A_mul_potential
#print axioms Bonnifaci.Network.sum_A
#print axioms Bonnifaci.Network.toLPData_cost
#print axioms Bonnifaci.Network.toLPData_feasible
#print axioms Bonnifaci.Network.feasible_sum_b_eq_zero
#print axioms Bonnifaci.Network.groundRow_implied

-- the identification chain
#print axioms Bonnifaci.Network.potential_inner_eq_edge_sum
#print axioms Bonnifaci.Network.dual_feasible_le_cost
#print axioms Bonnifaci.Network.cost_eq_potential_diff_of_tight
#print axioms Bonnifaci.Network.dual_feasible_bound
#print axioms Bonnifaci.Network.isShortestPathLength_of_tight
#print axioms Bonnifaci.Network.fixed_point_potentials_tight
#print axioms Bonnifaci.Network.fixed_point_potentials_are_distances
#print axioms Bonnifaci.Network.distance_from_grounded_source

-- the concrete instance
#print axioms Bonnifaci.path3_shortestPath

-- the two headline statements, with full types
#check @Bonnifaci.Network.fixed_point_potentials_are_distances
#check @Bonnifaci.Network.distance_from_grounded_source
#check @Bonnifaci.path3_shortestPath
#check @Bonnifaci.Network.dual_feasible_bound
