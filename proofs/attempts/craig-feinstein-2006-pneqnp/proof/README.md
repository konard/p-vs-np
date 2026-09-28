# Forward Proof Formalization

This directory formalizes the claimed structure of Feinstein's 2006 argument.

The Lean and Rocq files intentionally use axioms for the unproved lower-bound
premises. This mirrors the paper's logical shape: if the missing premises were
true, a `P != NP` conclusion would follow. The refutation directory explains
why those premises are not justified by the counting argument.

