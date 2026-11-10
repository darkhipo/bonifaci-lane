import Bonnifaci

-- NetworkRank: the connectivity -> FullRowRank bridge (§2.2 network case, STMTS §9.7).
-- Every declaration added by Bonnifaci/NetworkRank.lean, with its axiom footprint.

-- connectivity: undirected adjacency, its closure, and the invariance induction
#print axioms Bonnifaci.Network.adj_comm
#print axioms Bonnifaci.Network.eq_of_adj
#print axioms Bonnifaci.Network.eq_of_reflTransGen
#print axioms Bonnifaci.Network.reflTransGen_comm
#print axioms Bonnifaci.Network.eq_const_of_connected

-- the grounded reduction
#print axioms Bonnifaci.Network.groundLPData_A
#print axioms Bonnifaci.Network.groundLPData_fullRowRank_of_rooted
#print axioms Bonnifaci.Network.groundLPData_fullRowRank
#print axioms Bonnifaci.Network.connected_of_groundLPData_fullRowRank
#print axioms Bonnifaci.Network.groundLPData_fullRowRank_iff

-- grounding is necessary: the ungrounded incidence system is rank-deficient
#print axioms Bonnifaci.Network.toLPData_not_fullRowRank

-- the consumer: M6's exists_step, end to end
#print axioms Bonnifaci.Network.groundLPData_exists_step

-- the concrete path graph
#print axioms Bonnifaci.path3_connected
#print axioms Bonnifaci.path3_groundLPData_fullRowRank
#print axioms Bonnifaci.path3_toLPData_not_fullRowRank
#print axioms Bonnifaci.path3_groundLPData_b
#print axioms Bonnifaci.path3_groundLPData_step_nonempty

-- the headline statements, with full types
#check @Bonnifaci.Network.groundLPData_fullRowRank
#check @Bonnifaci.Network.groundLPData_fullRowRank_iff
#check @Bonnifaci.Network.toLPData_not_fullRowRank
#check @Bonnifaci.Network.groundLPData_exists_step
#check @Bonnifaci.path3_groundLPData_step_nonempty
