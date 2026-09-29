# Vega (2015): forward proof sketch

The [Lean](lean/VegaProof.lean) and [Rocq](rocq/VegaProof.v) files outline
Definition 3.1, the pair-language e-reduction, and the proposed route
through one-in-three 3SAT and HORNSAT. The files contain axioms and
unfinished proofs. Their successful compilation does not verify the
axiomatized reductions or the conclusion P=NP.

The step from membership of the two complete problems in equivalent-P
to class equality needs compatible encodings and both class inclusions.
See the [refutation audit](../refutation/README.md) for a finite logical
countermodel to an inclusion-to-equality inference. Its shared-certificate
construction also shows that an earlier failed certificate-ignoring
proof of diagonal HORNSAT was not a refutation of Theorem 6.1.
