import proofs.attempts.«angela-weiss-2011-peqnp».refutation.lean.WeissRefutation

-- The witness formerly used for every coefficient and degree fails here.
example : ¬ (2 ^ (1 + 10 + 2) > 1 * (1 + 10 + 2) ^ 10) := by decide

-- These four claims must depend on proved arithmetic, not sorryAx.
#print axioms WeissRefutation2011.numAssignments_exponential
#print axioms WeissRefutation2011.enumerating_all_assignments_is_exponential
#print axioms WeissRefutation2011.full_ke_cut_tree_exponential
#print axioms WeissRefutation2011.counting_facts_for_weiss
