# Forward Proof Analysis

The forward proof is not formalizable as a proof of P != NP.

The central obstruction is that the paper tries to separate two facts that are
linked by the definition of NP-completeness:

1. SAT polynomial-time many-one reduces to every NP-complete language `L`.
2. If such an `L` has a polynomial-time decider, then SAT has a polynomial-time
   decider by composition.

No constructive recovery of an "underlying K-SAT" instance from the target
algorithm is required. The reduction already supplies the transformed instance,
and the target decider supplies the answer.

The Lean and Rocq files in this directory are therefore marker formalizations:
they encode the assumptions that would be needed for Meek's proof and record why
the proof does not produce the claimed theorem.
