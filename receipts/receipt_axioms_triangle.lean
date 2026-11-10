import Bonnifaci

-- Triangle: the positive-length-cycle scope witness (STMTS §9.6.3 / §9.8).
-- Every declaration added by Bonnifaci/Triangle.lean, with its axiom footprint.

-- the graph and its connectivity
#print axioms Bonnifaci.triangle_connected

-- the cycle identity and the negation of the tightness system
#print axioms Bonnifaci.triangle_telescope
#print axioms Bonnifaci.triangle_no_tight_potential

-- the Laplacian layer accepts the triangle ...
#print axioms Bonnifaci.triangle_groundLPData_step_nonempty

-- ... but the rest condition does not
#print axioms Bonnifaci.triangle_no_fixed_point

-- positive control: the tree's tightness system IS solvable (the negation is about the cycle)
#print axioms Bonnifaci.path3_tight_potential

-- the headline statements, with full types
#check @Bonnifaci.triangle
#check @Bonnifaci.triangle_no_tight_potential
#check @Bonnifaci.triangle_no_fixed_point
