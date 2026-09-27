# Common Errors in P vs NP Proof Attempts

This document groups the proof attempts cataloged in this directory by recurring
errors. It is meant to be read next to [ATTEMPTS.md](ATTEMPTS.md): that file is
the chronological/catalog view, while this file is the "what not to repeat" view.

The groupings below are based on local attempt READMEs, refutation notes,
and error analyses. They are hypotheses about failure modes, not themselves
proofs that a historical argument is false. An attempt may appear in more than
one group. The coverage index assigns each folder a primary family and an
evidence level. A theorem about a simplified model, an admitted claim, or an
arithmetic illustration does not automatically refute the paper.

Evidence levels in the index are:

- **Concrete refutation:** a verified witness falsifies a stated proposition
  under the original input conditions.
- **Conditional result:** a verified result depends on an explicitly stated
  interpretation or additional premise; the paper's full claim remains open.
- **Identified gap:** a specific missing implication or proof obligation has
  been isolated, without a full counterexample to the algorithm.
- **Informal/unverified analysis:** the local notes suggest an error, but this
  index has not audited a source-level proposition and matching witness.

The levels describe the evidence linked here, not the truth of P versus NP.

## Error Families

### 1. Assuming a lower bound instead of proving it

The proof argues that an algorithm must perform exhaustive search, must inspect
all candidates, or cannot use a shortcut, but never proves that every possible
algorithm has super-polynomial running time. This is the central obstacle in
P != NP proofs.

Similar works:

- [alan-feinstein-2005-pneqnp](alan-feinstein-2005-pneqnp/)
- [alan-feinstein-2011-pneqnp](alan-feinstein-2011-pneqnp/)
- [author13-2004-pneqnp](author13-2004-pneqnp/)
- [bangyan-wen-yi-lin-2010-pneqnp](bangyan-wen-yi-lin-2010-pneqnp/)
- [chingizovich-valeyev-2013-pneqnp](chingizovich-valeyev-2013-pneqnp/)
- [daniel-uribe-2016-pneqnp](daniel-uribe-2016-pneqnp/)
- [jerrald-meek-2008-pneqnp](jerrald-meek-2008-pneqnp/)
- [jorma-jormakka-2008-pneqnp](jorma-jormakka-2008-pneqnp/)
- [ki-bong-nam-sh-wang-and-yang-gon-kim-published-2004-pneqnp](ki-bong-nam-sh-wang-and-yang-gon-kim-published-2004-pneqnp/)
- [mathias-hauptmann-2016-pneqnp](mathias-hauptmann-2016-pneqnp/)
- [rodrigo-diduch-2012-pneqnp](rodrigo-diduch-2012-pneqnp/)
- [roman-yampolskiy-2011-pneqnp](roman-yampolskiy-2011-pneqnp/)
- [satoshi-tazawa-2012-pneqnp](satoshi-tazawa-2012-pneqnp/)

### 2. Hiding exponential work in a claimed polynomial algorithm

The algorithm is described with polynomial-looking loops, but it constructs an
exponential object, recursively explores exponentially many cases, calls an
expensive subroutine, or uses a parameter that can be exponential in the input
length.

Similar works:

- [amar-mukherjee-2011-peqnp](amar-mukherjee-2011-peqnp/)
- [angela-weiss-2011-peqnp](angela-weiss-2011-peqnp/)
- [author2-1996-peqnp](author2-1996-peqnp/)
- [guohun-zhu-2007-peqnp](guohun-zhu-2007-peqnp/)
- [hamelin-2011-peqnp](hamelin-2011-peqnp/)
- [javaid-aslam-2008-peqnp](javaid-aslam-2008-peqnp/)
- [luigi-salemi-2009-peqnp](luigi-salemi-2009-peqnp/)
- [matt-groff-2011-peqnp](matt-groff-2011-peqnp/)
- [mohamed-mimouni-2006-peqnp](mohamed-mimouni-2006-peqnp/)
- [sanchez-guinea-2015-peqnp](sanchez-guinea-2015-peqnp/)
- [sergey-kardash-2011-peqnp](sergey-kardash-2011-peqnp/)
- [sergey_v_yakhontov_2012_peqnp](sergey_v_yakhontov_2012_peqnp/)
- [zohreh-akbari-2008-peqnp](zohreh-akbari-2008-peqnp/)

### 3. Confusing LP/SDP relaxations with exact integer solutions

The work encodes an NP-complete problem as an integer program, drops the
integrality constraint, and assumes the relaxed LP/SDP solution can be rounded or
interpreted as a valid exact solution. The missing step is an integrality theorem
or a proven sound recovery procedure.

Similar works:

- [anatoly-panyukov-2014-peqnp](anatoly-panyukov-2014-peqnp/)
- [antano-maknickas-2011-peqnp](antano-maknickas-2011-peqnp/)
- [author7-2003-peqnp](author7-2003-peqnp/)
- [author93-2013-peqnp](author93-2013-peqnp/)
- [dr-joachim-mertz-2005-peqnp](dr-joachim-mertz-2005-peqnp/)
- [mikhail-katkov-2010-peqnp](mikhail-katkov-2010-peqnp/)
- [moustapha-diaby-2004-peqnp](moustapha-diaby-2004-peqnp/)
- [sergey-gubin-2006-peqnp](sergey-gubin-2006-peqnp/)
- [sergey-gubin-2010-peqnp](sergey-gubin-2010-peqnp/)
- [yann-dujardin-2009-peqnp](yann-dujardin-2009-peqnp/)

### 4. Using an invalid reduction or non-preserving transformation

The proof maps one problem to another but does not preserve satisfiability,
optimality, certificates, instance size, or the needed direction of implication.
Sometimes the transformed problem is easier because it is no longer equivalent
to the original NP-complete target.

Similar works:

- [andrea-bianchini-2005-peqnp](andrea-bianchini-2005-peqnp/)
- [author104-2015-peqnp](author104-2015-peqnp/)
- [dhami-2014-peqnp](dhami-2014-peqnp/)
- [frank-vega-delgado-2010-pneqnp](frank-vega-delgado-2010-pneqnp/)
- [lizhi-du-2010-peqnp](lizhi-du-2010-peqnp/)
- [narendra-chaudhari-2009-peqnp](narendra-chaudhari-2009-peqnp/)
- [sergey-gubin-2006-peqnp](sergey-gubin-2006-peqnp/)
- [tang-pushan-1997-peqnp](tang-pushan-1997-peqnp/)
- [yubin-huang-2015-peqnp](yubin-huang-2015-peqnp/)
- [zeilberger-2009-peqnp](zeilberger-2009-peqnp/)

### 5. Solving an easier, special, approximate, or different problem

The method may solve shortest path instead of Hamiltonian cycle, approximation
instead of exact decision, an optimization variant instead of a decision
language, special graph families instead of all inputs, or a related problem
whose complexity does not transfer to P vs NP.

Similar works:

- [carlos-barron-romero-2010-euclidean-tsp-gap-pneqnp](carlos-barron-romero-2010-euclidean-tsp-gap-pneqnp/)
- [carlos-barron-romero-2010-pneqnp](carlos-barron-romero-2010-pneqnp/)
- [delacorte-czerwinski-2007-peqnppspace](delacorte-czerwinski-2007-peqnppspace/)
- [dmitriy-nuriyev-2013-peqnp](dmitriy-nuriyev-2013-peqnp/)
- [howard-kleiman-2006-peqnp](howard-kleiman-2006-peqnp/)
- [krieger-jones-2008-peqnp](krieger-jones-2008-peqnp/)
- [michael-laplante-2015-peqnp](michael-laplante-2015-peqnp/)
- [mohamed-mimouni-2006-peqnp](mohamed-mimouni-2006-peqnp/)
- [peng-cui-2014-peqnp](peng-cui-2014-peqnp/)
- [rafael-valls-hidalgo-gato-2009-peqnp](rafael-valls-hidalgo-gato-2009-peqnp/)
- [zohreh-akbari-2008-peqnp](zohreh-akbari-2008-peqnp/)

### 6. Replacing global consistency with local or greedy consistency

The argument checks pairwise constraints, local compatibility, greedy insertions,
or a partial consistency condition, then treats that as enough to solve a global
NP-complete problem. The missing part is a proof that local choices always extend
to a global witness.

Similar works:

- [charles-sauerbier-2002-peqnp](charles-sauerbier-2002-peqnp/)
- [lizhi-du-2010-peqnp](lizhi-du-2010-peqnp/)
- [louis-coder-2012-peqnp](louis-coder-2012-peqnp/)
- [qi-duan-2012-peqnp](qi-duan-2012-peqnp/)
- [riaz-khiyal-2006-peqnp](riaz-khiyal-2006-peqnp/)
- [sanchez-guinea-2015-peqnp](sanchez-guinea-2015-peqnp/)
- [sergey-kardash-2011-peqnp](sergey-kardash-2011-peqnp/)
- [zohreh-akbari-2008-peqnp](zohreh-akbari-2008-peqnp/)

### 7. Counting, compression, or enumeration mistakes

The proof assumes exponentially many witnesses, matchings, paths, cliques, truth
assignments, or polynomial coefficients can be counted or compressed without
losing the information needed for an exact decision.

Similar works:

- [angela-weiss-2011-peqnp](angela-weiss-2011-peqnp/)
- [guohun-zhu-2007-peqnp](guohun-zhu-2007-peqnp/)
- [javaid-aslam-2008-peqnp](javaid-aslam-2008-peqnp/)
- [matt-groff-2011-peqnp](matt-groff-2011-peqnp/)
- [sergey-gubin-2006-peqnp](sergey-gubin-2006-peqnp/)
- [sergey_v_yakhontov_2012_peqnp](sergey_v_yakhontov_2012_peqnp/)
- [zohreh-akbari-2008-peqnp](zohreh-akbari-2008-peqnp/)

### 8. Treating heuristics, experiments, or probability as proof

The work relies on empirical behavior, practical hardness, a heuristic that works
on tested inputs, a probabilistic claim where a deterministic proof is needed, or
cryptographic/randomness intuition rather than a worst-case mathematical proof.

Similar works:

- [arto-annila-2009-pneqnp](arto-annila-2009-pneqnp/)
- [author8-2003-pneqnp](author8-2003-pneqnp/)
- [douglas-youvan-2012-peqnp](douglas-youvan-2012-peqnp/)
- [figueroa-2016-pneqnp](figueroa-2016-pneqnp/)
- [francesco-capasso-2005-peqnp](francesco-capasso-2005-peqnp/)
- [matt-groff-2011-peqnp](matt-groff-2011-peqnp/)
- [mikhail-katkov-2010-peqnp](mikhail-katkov-2010-peqnp/)
- [roman-yampolskiy-2011-pneqnp](roman-yampolskiy-2011-pneqnp/)
- [xinwen-jiang-2009-peqnp](xinwen-jiang-2009-peqnp/)

### 9. Confusing nondeterminism, randomness, quantum choice, or physical process

The proof treats observer choice, quantum states, randomness, physical
parallelism, or a nonstandard machine feature as if it directly separated or
collapsed deterministic and nondeterministic polynomial time.

Similar works:

- [author11-2004-peqnp](author11-2004-peqnp/)
- [daegene-song-2014-pneqnp](daegene-song-2014-pneqnp/)
- [han-xiao-wen-2010-peqnp](han-xiao-wen-2010-peqnp/)
- [jeffrey-w-holcomb-2011-pneqnp](jeffrey-w-holcomb-2011-pneqnp/)
- [ron-cohen-2005-pneqnp](ron-cohen-2005-pneqnp/)
- [rubens-ramos-viana-2006-pneqnp](rubens-ramos-viana-2006-pneqnp/)
- [steven-meyer-2016-peqnp](steven-meyer-2016-peqnp/)

### 10. Confusing provability, computability, decidability, and complexity

The argument imports a theorem about formal provability, undecidability,
incompleteness, or computability and treats it as a polynomial-time lower bound.
P and NP are about asymptotic resource bounds for decision languages, not about
truth, proof existence, or computability alone.

Similar works:

- [author12-2004-pneqnp](author12-2004-pneqnp/)
- [bhupinder-singh-anand-2008-pneqnp](bhupinder-singh-anand-2008-pneqnp/)
- [changlin-wan-2010-peqnp](changlin-wan-2010-peqnp/)
- [frank-vega-delgado-2010-pneqnp](frank-vega-delgado-2010-pneqnp/)
- [natalia-malinina-2012-unprovable](natalia-malinina-2012-unprovable/)
- [ncada-costa-fa-doria-2003-unprovable](ncada-costa-fa-doria-2003-unprovable/)
- [nicholas-argall-2003-undecidable](nicholas-argall-2003-undecidable/)
- [radoslaw-hofman-2006-pneqnp](radoslaw-hofman-2006-pneqnp/)
- [rafee-ebrahim-kamouna-2008-peqnp](rafee-ebrahim-kamouna-2008-peqnp/)
- [singh-anand-2005-pneqnp](singh-anand-2005-pneqnp/)
- [singh-anand-2006-pneqnp](singh-anand-2006-pneqnp/)
- [sten-ake-tarnlund-2008-pneqnp](sten-ake-tarnlund-2008-pneqnp/)

### 11. Using undefined, nonstandard, or incompatible formal definitions

The proof introduces a new model, invariant, machine feature, language, or
problem definition without proving that it is equivalent to the standard P vs NP
framework. The result may be true in the invented setting while saying nothing
about standard Turing-machine complexity classes.

Similar works:

- [author15-2004-pneqnp](author15-2004-pneqnp/)
- [author4-2000-peqnp](author4-2000-peqnp/)
- [daegene-song-2014-pneqnp](daegene-song-2014-pneqnp/)
- [han-xiao-wen-2010-peqnp](han-xiao-wen-2010-peqnp/)
- [jeffrey-w-holcomb-2011-pneqnp](jeffrey-w-holcomb-2011-pneqnp/)
- [ron-cohen-2005-pneqnp](ron-cohen-2005-pneqnp/)
- [stefan-jaeger-2011-both](stefan-jaeger-2011-both/)
- [xinwen-jiang-2009-peqnp](xinwen-jiang-2009-peqnp/)

### 12. Circular reasoning or smuggling the conclusion into an axiom

The proof assumes a hardness claim, completeness claim, separation, recovery
property, or resource bound that is equivalent to the desired conclusion or is
nearly as hard as the original P vs NP problem.

Similar works:

- [ari-blinder-2009-pneqnp](ari-blinder-2009-pneqnp/)
- [author13-2004-pneqnp](author13-2004-pneqnp/)
- [author15-2004-pneqnp](author15-2004-pneqnp/)
- [deolalikar-2010-pneqnp](deolalikar-2010-pneqnp/)
- [jorma-jormakka-2008-pneqnp](jorma-jormakka-2008-pneqnp/)
- [luigi-salemi-2009-peqnp](luigi-salemi-2009-peqnp/)
- [rafael-valls-hidalgo-gato-2009-peqnp](rafael-valls-hidalgo-gato-2009-peqnp/)
- [riaz-khiyal-2006-peqnp](riaz-khiyal-2006-peqnp/)
- [ron-cohen-2005-pneqnp](ron-cohen-2005-pneqnp/)
- [sergey-kardash-2011-peqnp](sergey-kardash-2011-peqnp/)
- [stefan-rass-2016-pneqnp](stefan-rass-2016-pneqnp/)

### 13. Misusing diagonalization, self-reference, or independence arguments

The proof adapts a diagonal, self-referential, or independence construction but
does not handle uniformity, representation, relativization, absoluteness, or the
gap between a syntactic construction and an actual complexity lower bound.

Similar works:

- [anatoly-plotnikov-2011-pneqnp](anatoly-plotnikov-2011-pneqnp/)
- [author8-2003-pneqnp](author8-2003-pneqnp/)
- [daegene-song-2014-pneqnp](daegene-song-2014-pneqnp/)
- [natalia-malinina-2012-unprovable](natalia-malinina-2012-unprovable/)
- [ncada-costa-fa-doria-2003-unprovable](ncada-costa-fa-doria-2003-unprovable/)
- [nicholas-argall-2003-undecidable](nicholas-argall-2003-undecidable/)
- [ruijia-liao-2011-pneqnp](ruijia-liao-2011-pneqnp/)
- [singh-anand-2006-pneqnp](singh-anand-2006-pneqnp/)

### 14. Ignoring known barriers or using a barrier-limited technique

The argument appears to relativize, naturalize, or otherwise fall into known
classes of techniques that cannot by themselves resolve P vs NP. This does not
automatically refute a proof, but it identifies a gap that the proof must
explicitly overcome.

Similar works:

- [anatoly-plotnikov-2011-pneqnp](anatoly-plotnikov-2011-pneqnp/)
- [ari-blinder-2009-pneqnp](ari-blinder-2009-pneqnp/)
- [author13-2004-pneqnp](author13-2004-pneqnp/)
- [chingizovich-valeyev-2013-pneqnp](chingizovich-valeyev-2013-pneqnp/)
- [deolalikar-2010-pneqnp](deolalikar-2010-pneqnp/)
- [jeffrey-w-holcomb-2011-pneqnp](jeffrey-w-holcomb-2011-pneqnp/)
- [jerrald-meek-2008-pneqnp](jerrald-meek-2008-pneqnp/)
- [jorma-jormakka-2008-pneqnp](jorma-jormakka-2008-pneqnp/)
- [radoslaw-hofman-2006-pneqnp](radoslaw-hofman-2006-pneqnp/)
- [roman-yampolskiy-2011-pneqnp](roman-yampolskiy-2011-pneqnp/)
- [ruijia-liao-2011-pneqnp](ruijia-liao-2011-pneqnp/)
- [satoshi-tazawa-2012-pneqnp](satoshi-tazawa-2012-pneqnp/)

### 15. Confusing verification, search, construction, and certificates

The proof uses polynomial-time verification of a candidate, existence of a
witness, or an efficient checker as if it provided an efficient method to find
the witness or construct the algorithm.

Similar works:

- [carlos-barron-romero-2010-pneqnp](carlos-barron-romero-2010-pneqnp/)
- [javaid-aslam-2008-peqnp](javaid-aslam-2008-peqnp/)
- [matt-groff-2011-peqnp](matt-groff-2011-peqnp/)
- [michel-feldmann-2012-peqnp](michel-feldmann-2012-peqnp/)
- [mikhail-katkov-2010-peqnp](mikhail-katkov-2010-peqnp/)
- [renjit-2006-conpeqnp](renjit-2006-conpeqnp/)
- [riaz-khiyal-2006-peqnp](riaz-khiyal-2006-peqnp/)

### 16. Uniformity, non-uniformity, and circuit-family mismatches

The proof may show something about a non-uniform family, a finite-size argument,
a special circuit model, or an algorithm-dependent construction, then treat it
as a uniform Turing-machine separation for all input lengths.

Similar works:

- [daniel-uribe-2016-pneqnp](daniel-uribe-2016-pneqnp/)
- [jorma-jormakka-2008-pneqnp](jorma-jormakka-2008-pneqnp/)
- [lev-gordeev-2005-pneqnp](lev-gordeev-2005-pneqnp/)
- [luiz-barbosa-2009-pneqnp](luiz-barbosa-2009-pneqnp/)
- [stefan-rass-2016-pneqnp](stefan-rass-2016-pneqnp/)

### 17. Encoding-size, bit-complexity, or parameter mistakes

The proof measures runtime in the wrong parameter, ignores bit lengths, assumes
an exponentially large encoding is polynomial, or changes the representation in
a way that moves rather than removes the hard part.

Similar works:

- [andrea-bianchini-2005-peqnp](andrea-bianchini-2005-peqnp/)
- [koji-kobayashi-2012-pneqnp](koji-kobayashi-2012-pneqnp/)
- [rafael-valls-hidalgo-gato-2009-peqnp](rafael-valls-hidalgo-gato-2009-peqnp/)
- [sergey_v_yakhontov_2012_peqnp](sergey_v_yakhontov_2012_peqnp/)
- [stefan-rass-2016-pneqnp](stefan-rass-2016-pneqnp/)
- [vladimir-romanov-2010-peqnp](vladimir-romanov-2010-peqnp/)

### 18. Depending on false statements or contradictions with known results

The claimed intermediate theorem is false, contradicts hierarchy theorems, uses
an invalid implication between complexity classes, or proves a statement too
strong to be compatible with standard results.

Similar works:

- [has-also-2001-pneqnp](has-also-2001-pneqnp/)
- [mathias-hauptmann-2016-pneqnp](mathias-hauptmann-2016-pneqnp/)
- [minseong-kim-2012-pneqnp](minseong-kim-2012-pneqnp/)
- [stefan-jaeger-2011-both](stefan-jaeger-2011-both/)
- [vega-delgado-2012-pneqnp](vega-delgado-2012-pneqnp/)

### 19. Incomplete documentation, withdrawn papers, or joke claims

The repository notes indicate that the primary text is unavailable, withdrawn,
not serious, too informal, or documented only enough to identify likely failure
patterns. These entries are still useful because they mark classes of mistakes
that should not be mistaken for resolved proofs.

Similar works:

- [amar-mukherjee-2011-peqnp](amar-mukherjee-2011-peqnp/)
- [changlin-wan-2010-peqnp](changlin-wan-2010-peqnp/)
- [craig-feinstein-2006-pneqnp](craig-feinstein-2006-pneqnp/)
- [joonmo-kim-2014-pneqnp](joonmo-kim-2014-pneqnp/)
- [miron-teplitz-2005-peqnp](miron-teplitz-2005-peqnp/)
- [viktor-ivanov-2005-pneqnp](viktor-ivanov-2005-pneqnp/)
- [zeilberger-2009-peqnp](zeilberger-2009-peqnp/)

### 20. Assuming a structure theorem for all algorithms from one algorithm class

The proof studies a particular family of algorithms, formulas, postulates, or
machines, then treats optimality or failure inside that family as a lower bound
against all possible polynomial-time algorithms.

Similar works:

- [alan-feinstein-2005-pneqnp](alan-feinstein-2005-pneqnp/)
- [craig-feinstein-2003-pneqnp](craig-feinstein-2003-pneqnp/)
- [jerrald-meek-2008-karp-postulates-pneqnp](jerrald-meek-2008-karp-postulates-pneqnp/)
- [koji-kobayashi-2011-pneqnp](koji-kobayashi-2011-pneqnp/)
- [renjit-grover-2005-pneqnp](renjit-grover-2005-pneqnp/)

## Attempt Coverage Index

Each row gives the primary suspected error family and the evidence level
established by this repository. Entries without a source-to-statement audit
are conservatively marked informal/unverified; consult the individual attempt
README and original paper before treating a proposed error as established.

| Attempt | Primary suspected error or obligation | Evidence level |
| --- | --- | --- |
| [alan-feinstein-2005-pneqnp](alan-feinstein-2005-pneqnp/) | Lower bound assumed from a restricted algorithm family | Informal/unverified analysis |
| [alan-feinstein-2011-pneqnp](alan-feinstein-2011-pneqnp/) | Lower bound assumed from an exponential upper bound | Informal/unverified analysis |
| [amar-mukherjee-2011-peqnp](amar-mukherjee-2011-peqnp/) | Withdrawn/incomplete claimed 3-SAT algorithm; likely hidden exponential or correctness gap | Informal/unverified analysis |
| [anatoly-panyukov-2014-peqnp](anatoly-panyukov-2014-peqnp/) | LP relaxation assumed to have integer optimum | Informal/unverified analysis |
| [anatoly-plotnikov-2007-peqnp](anatoly-plotnikov-2007-peqnp/) | Unproved Conjecture 1 leaves the correctness claim conditional; iteration bound also needs justification | Conditional result |
| [anatoly-plotnikov-2011-pneqnp](anatoly-plotnikov-2011-pneqnp/) | Invalid diagonalization and circular construction | Informal/unverified analysis |
| [andrea-bianchini-2005-peqnp](andrea-bianchini-2005-peqnp/) | Encoding and reduction do not preserve the hard problem correctly | Informal/unverified analysis |
| [angela-weiss-2011-peqnp](angela-weiss-2011-peqnp/) | Hidden exponential tableau/macro enumeration | Informal/unverified analysis |
| [antano-maknickas-2011-peqnp](antano-maknickas-2011-peqnp/) | LP relaxation and rounding do not preserve SAT | Informal/unverified analysis |
| [ari-blinder-2009-pneqnp](ari-blinder-2009-pneqnp/) | Unproven NP vs co-NP style claim equivalent to the hard part | Informal/unverified analysis |
| [arto-annila-2009-pneqnp](arto-annila-2009-pneqnp/) | Informal physical/thermodynamic reasoning without formal lower bound | Informal/unverified analysis |
| [author104-2015-peqnp](author104-2015-peqnp/) | Class equality lacks reverse inclusion and an explicit pair/string encoding; finite logical countermodel only | Identified gap |
| [author11-2004-peqnp](author11-2004-peqnp/) | Exponential physical hardware hidden behind polynomial time | Informal/unverified analysis |
| [author12-2004-pneqnp](author12-2004-pneqnp/) | Provability and decidability confused with complexity | Informal/unverified analysis |
| [author13-2004-pneqnp](author13-2004-pneqnp/) | Unproven hardness assumption and missing NP-completeness proof | Informal/unverified analysis |
| [author15-2004-pneqnp](author15-2004-pneqnp/) | Undefined invariance principle and circular separation claim | Informal/unverified analysis |
| [author2-1996-peqnp](author2-1996-peqnp/) | Graph-to-poset conversion loses information; hidden exponential gap | Informal/unverified analysis |
| [author4-2000-peqnp](author4-2000-peqnp/) | Insufficient rigor and unsupported P=NP claim | Informal/unverified analysis |
| [author7-2003-peqnp](author7-2003-peqnp/) | Facet/linear-ordering approach lacks valid polynomial exact algorithm | Informal/unverified analysis |
| [author8-2003-pneqnp](author8-2003-pneqnp/) | Empirical/temporal fallacy and problem-class confusion | Informal/unverified analysis |
| [author93-2013-peqnp](author93-2013-peqnp/) | LP/ILP conflation | Informal/unverified analysis |
| [bangyan-wen-yi-lin-2010-pneqnp](bangyan-wen-yi-lin-2010-pneqnp/) | Logical asymmetry does not imply a complexity lower bound | Informal/unverified analysis |
| [bhupinder-singh-anand-2008-pneqnp](bhupinder-singh-anand-2008-pneqnp/) | Category confusion between computability/provability and P vs NP | Informal/unverified analysis |
| [carlos-barron-romero-2010-euclidean-tsp-gap-pneqnp](carlos-barron-romero-2010-euclidean-tsp-gap-pneqnp/) | GAP/E2DTSP variant does not yield the claimed P != NP separation | Informal/unverified analysis |
| [carlos-barron-romero-2010-pneqnp](carlos-barron-romero-2010-pneqnp/) | Verification complexity misunderstood as NP hardness separation | Informal/unverified analysis |
| [changlin-wan-2010-peqnp](changlin-wan-2010-peqnp/) | Computability confused with polynomial-time complexity | Informal/unverified analysis |
| [charles-sauerbier-2002-peqnp](charles-sauerbier-2002-peqnp/) | Local/path consistency does not imply satisfiability | Informal/unverified analysis |
| [chingizovich-valeyev-2013-pneqnp](chingizovich-valeyev-2013-pneqnp/) | Best-known algorithm treated as a lower bound | Informal/unverified analysis |
| [craig-feinstein-2003-pneqnp](craig-feinstein-2003-pneqnp/) | Invalid transfer from one machine/model to all algorithms | Informal/unverified analysis |
| [craig-feinstein-2006-pneqnp](craig-feinstein-2006-pneqnp/) | Sparse documented evidence; likely unsupported lower-bound claim | Informal/unverified analysis |
| [daegene-song-2014-pneqnp](daegene-song-2014-pneqnp/) | Observer choice and self-reference confused with computational nondeterminism | Informal/unverified analysis |
| [daniel-uribe-2016-pneqnp](daniel-uribe-2016-pneqnp/) | Decision-tree/model limitation treated as a general lower bound | Informal/unverified analysis |
| [delacorte-czerwinski-2007-peqnppspace](delacorte-czerwinski-2007-peqnppspace/) | Graph-isomorphism algorithm/cospectral reasoning does not prove P=NP/PSPACE | Informal/unverified analysis |
| [deolalikar-2010-pneqnp](deolalikar-2010-pneqnp/) | Random-instance/model-theory transfer fails for worst-case P vs NP | Informal/unverified analysis |
| [dhami-2014-peqnp](dhami-2014-peqnp/) | Invalid reduction involving clique/network interdiction | Informal/unverified analysis |
| [dmitriy-nuriyev-2013-peqnp](dmitriy-nuriyev-2013-peqnp/) | Hamiltonian-path algorithm lacks proof for all instances | Informal/unverified analysis |
| [douglas-youvan-2012-peqnp](douglas-youvan-2012-peqnp/) | Heuristic or unsupported algorithmic claim without rigorous proof | Informal/unverified analysis |
| [dr-joachim-mertz-2005-peqnp](dr-joachim-mertz-2005-peqnp/) | LP relaxation confused with integer programming | Informal/unverified analysis |
| [eli-halylaurin-2016-peqnp](eli-halylaurin-2016-peqnp/) | Gap between claimed verifier/algorithm and NP-complete solving | Informal/unverified analysis |
| [figueroa-2016-pneqnp](figueroa-2016-pneqnp/) | Probability argument and one-way-function claim do not prove P != NP | Informal/unverified analysis |
| [francesco-capasso-2005-peqnp](francesco-capasso-2005-peqnp/) | Heuristic algorithm not proven correct on all inputs | Informal/unverified analysis |
| [frank-vega-delgado-2010-pneqnp](frank-vega-delgado-2010-pneqnp/) | Missing reduction to an undecidable NP language | Informal/unverified analysis |
| [frederic-gillet-2013-peqnp](frederic-gillet-2013-peqnp/) | Cost-interference and gate construction flaws | Informal/unverified analysis |
| [guohun-zhu-2007-peqnp](guohun-zhu-2007-peqnp/) | Six-vertex projector witness contradicts Theorem 1(c3)'s C4 bound; Lemma 4 code-class challenge remains conditional | Concrete refutation |
| [hamelin-2011-peqnp](hamelin-2011-peqnp/) | Exponential dependence hidden in a claimed polynomial method | Informal/unverified analysis |
| [han-xiao-wen-2010-peqnp](han-xiao-wen-2010-peqnp/) | Undefined terminology and oracle/nondeterminism confusion | Informal/unverified analysis |
| [hanlin-liu-2014-peqnp](hanlin-liu-2014-peqnp/) | Hamiltonian-circuit algorithm contains an unproven correctness gap | Informal/unverified analysis |
| [has-also-2001-pneqnp](has-also-2001-pneqnp/) | EXP subset NP contradicts standard hierarchy consequences | Informal/unverified analysis |
| [howard-kleiman-2006-peqnp](howard-kleiman-2006-peqnp/) | Floyd-Warshall shortest-path method solves the wrong problem | Informal/unverified analysis |
| [infotechnology-center-2012-pneqnp](infotechnology-center-2012-pneqnp/) | Unsupported complexity inference from informal definitions | Informal/unverified analysis |
| [jason-w-steinmetz-2011-peqnp](jason-w-steinmetz-2011-peqnp/) | P=NP algorithm has an unproven critical correctness step | Informal/unverified analysis |
| [javaid-aslam-2008-peqnp](javaid-aslam-2008-peqnp/) | Incorrect counting of Hamiltonian circuits | Informal/unverified analysis |
| [jeffrey-w-holcomb-2011-pneqnp](jeffrey-w-holcomb-2011-pneqnp/) | Nondeterminism/randomness and witness multiplicity confused | Informal/unverified analysis |
| [jerrald-meek-2008-karp-postulates-pneqnp](jerrald-meek-2008-karp-postulates-pneqnp/) | Karp-postulate special cases treated as a general separation | Informal/unverified analysis |
| [jerrald-meek-2008-pneqnp](jerrald-meek-2008-pneqnp/) | Invalid asymptotic/lower-bound inferences | Informal/unverified analysis |
| [joonmo-kim-2014-pneqnp](joonmo-kim-2014-pneqnp/) | Sparse documented evidence; likely unsupported lower-bound proof | Informal/unverified analysis |
| [jorma-jormakka-2008-pneqnp](jorma-jormakka-2008-pneqnp/) | Circular adversarial/non-uniform lower-bound construction | Informal/unverified analysis |
| [ki-bong-nam-sh-wang-and-yang-gon-kim-published-2004-pneqnp](ki-bong-nam-sh-wang-and-yang-gon-kim-published-2004-pneqnp/) | Insufficient lower bound | Informal/unverified analysis |
| [koji-kobayashi-2011-pneqnp](koji-kobayashi-2011-pneqnp/) | Dependency-relation framework lacks a general lower-bound transfer | Informal/unverified analysis |
| [koji-kobayashi-2012-pneqnp](koji-kobayashi-2012-pneqnp/) | Representation complexity confused with decision complexity | Informal/unverified analysis |
| [krieger-jones-2008-peqnp](krieger-jones-2008-peqnp/) | Hamiltonian-circuit detector solves an underspecified/different problem | Informal/unverified analysis |
| [lev-gordeev-2005-pneqnp](lev-gordeev-2005-pneqnp/) | Circuit-complexity gap does not yield the claimed separation | Informal/unverified analysis |
| [lizhi-du-2010-peqnp](lizhi-du-2010-peqnp/) | Incorrect intersection/pruning step in 3-SAT algorithm | Informal/unverified analysis |
| [lokman-kolukisa-2005-peqnp](lokman-kolukisa-2005-peqnp/) | Tautology algorithm correctness and formal gap | Informal/unverified analysis |
| [louis-coder-2012-peqnp](louis-coder-2012-peqnp/) | Local/global consistency and insufficient encoding | Informal/unverified analysis |
| [luigi-salemi-2009-peqnp](luigi-salemi-2009-peqnp/) | Saturation complexity and constructive proof are circular/unproved | Informal/unverified analysis |
| [luiz-barbosa-2009-pneqnp](luiz-barbosa-2009-pneqnp/) | Non-uniform circuit argument does not imply P != NP | Informal/unverified analysis |
| [mathias-hauptmann-2016-pneqnp](mathias-hauptmann-2016-pneqnp/) | Claimed contradiction is not a contradiction | Informal/unverified analysis |
| [matt-groff-2011-peqnp](matt-groff-2011-peqnp/) | Actual 3-CNF inputs collide at one raw finite-field evaluation; full reconstruction algorithm unresolved | Conditional result |
| [michael-laplante-2015-peqnp](michael-laplante-2015-peqnp/) | Clique algorithm fails on counterexamples/special structure | Informal/unverified analysis |
| [michel-feldmann-2012-peqnp](michel-feldmann-2012-peqnp/) | Missing construction algorithm | Informal/unverified analysis |
| [mikhail-katkov-2010-peqnp](mikhail-katkov-2010-peqnp/) | SDP/local optimum does not yield reliable global certificate | Informal/unverified analysis |
| [mikhail-kupchik-2004-pneqnp](mikhail-kupchik-2004-pneqnp/) | Sparse documented refutation; unsupported lower-bound claim | Informal/unverified analysis |
| [minseong-kim-2012-pneqnp](minseong-kim-2012-pneqnp/) | False premise/logical fallacy | Informal/unverified analysis |
| [miron-teplitz-2005-peqnp](miron-teplitz-2005-peqnp/) | Sparse documented evidence; likely unsupported P=NP claim | Informal/unverified analysis |
| [mohamed-mimouni-2006-peqnp](mohamed-mimouni-2006-peqnp/) | Clique algorithm works only on special cases or hides exponential work | Informal/unverified analysis |
| [moustapha-diaby-2004-peqnp](moustapha-diaby-2004-peqnp/) | LP formulation lacks one-to-one correspondence with TSP tours | Informal/unverified analysis |
| [narendra-chaudhari-2009-peqnp](narendra-chaudhari-2009-peqnp/) | Representation change does not reduce 3-SAT complexity | Informal/unverified analysis |
| [natalia-malinina-2012-unprovable](natalia-malinina-2012-unprovable/) | Undecidability/independence and self-reference misapplied | Informal/unverified analysis |
| [ncada-costa-fa-doria-2003-unprovable](ncada-costa-fa-doria-2003-unprovable/) | Critical independence-proof gap and exotic definitions | Informal/unverified analysis |
| [nicholas-argall-2003-undecidable](nicholas-argall-2003-undecidable/) | Formal undecidability error | Informal/unverified analysis |
| [peng-cui-2014-peqnp](peng-cui-2014-peqnp/) | Approximation confused with exact solution | Informal/unverified analysis |
| [qi-duan-2012-peqnp](qi-duan-2012-peqnp/) | Greedy insertion fallacy | Informal/unverified analysis |
| [radoslaw-hofman-2006-pneqnp](radoslaw-hofman-2006-pneqnp/) | Provability/computability confusion and invalid restriction to FOPC transformations | Informal/unverified analysis |
| [rafael-valls-hidalgo-gato-2009-peqnp](rafael-valls-hidalgo-gato-2009-peqnp/) | Encoding-complexity barrier and parameter confusion | Informal/unverified analysis |
| [rafee-ebrahim-kamouna-2008-peqnp](rafee-ebrahim-kamouna-2008-peqnp/) | Cook theorem/paradox category confusion | Informal/unverified analysis |
| [renjit-2006-conpeqnp](renjit-2006-conpeqnp/) | Invalid generalization from one problem to NP vs co-NP | Informal/unverified analysis |
| [renjit-grover-2005-pneqnp](renjit-grover-2005-pneqnp/) | Algorithm classification approach lacks universal lower bound | Informal/unverified analysis |
| [riaz-khiyal-2006-peqnp](riaz-khiyal-2006-peqnp/) | Greedy/backtracking avoidance uses circular valid-selection conditions | Informal/unverified analysis |
| [rodrigo-diduch-2012-pneqnp](rodrigo-diduch-2012-pneqnp/) | Definitions used without lower-bound proof | Informal/unverified analysis |
| [roman-yampolskiy-2011-pneqnp](roman-yampolskiy-2011-pneqnp/) | Cryptographic intuition and no-pruning claim do not prove exponential time | Informal/unverified analysis |
| [ron-cohen-2005-pneqnp](ron-cohen-2005-pneqnp/) | Nonstandard machine/oracle feature changes the problem | Informal/unverified analysis |
| [rubens-ramos-viana-2006-pneqnp](rubens-ramos-viana-2006-pneqnp/) | Quantum/uncomputability category mistake | Informal/unverified analysis |
| [ruijia-liao-2011-pneqnp](ruijia-liao-2011-pneqnp/) | Cantor diagonalization does not apply as stated | Informal/unverified analysis |
| [sanchez-guinea-2015-peqnp](sanchez-guinea-2015-peqnp/) | Exponential recursion and hidden dependency graph | Informal/unverified analysis |
| [satoshi-tazawa-2012-pneqnp](satoshi-tazawa-2012-pneqnp/) | Automorphism-to-lower-bound connection is missing | Informal/unverified analysis |
| [sergey-gubin-2006-peqnp](sergey-gubin-2006-peqnp/) | Flawed LP formulation and SAT-to-2SAT reduction | Informal/unverified analysis |
| [sergey-gubin-2010-peqnp](sergey-gubin-2010-peqnp/) | Paper-specific LP has a feasible point for a graph without a Hamiltonian tour | Concrete refutation |
| [sergey-kardash-2011-peqnp](sergey-kardash-2011-peqnp/) | Local consistency and relationship-structure size errors | Informal/unverified analysis |
| [sergey_v_yakhontov_2012_peqnp](sergey_v_yakhontov_2012_peqnp/) | TCPE/encoding size problem | Informal/unverified analysis |
| [singh-anand-2005-pneqnp](singh-anand-2005-pneqnp/) | Provability/computability confusion | Informal/unverified analysis |
| [singh-anand-2006-pneqnp](singh-anand-2006-pneqnp/) | Nonstandard models and provability do not eliminate computation | Informal/unverified analysis |
| [stefan-jaeger-2011-both](stefan-jaeger-2011-both/) | Redefined complexity classes yield contradictory/nonstandard claims | Informal/unverified analysis |
| [stefan-rass-2016-pneqnp](stefan-rass-2016-pneqnp/) | Encoding mismatch, circular density bounds, and finite/asymptotic gap | Informal/unverified analysis |
| [sten-ake-tarnlund-2008-pneqnp](sten-ake-tarnlund-2008-pneqnp/) | Provability/truth confused with complexity | Informal/unverified analysis |
| [steven-meyer-2016-peqnp](steven-meyer-2016-peqnp/) | Simulation/model-independence confused with algorithmic content | Informal/unverified analysis |
| [tang-pushan-1997-peqnp](tang-pushan-1997-peqnp/) | Reduction preserves an easier problem, not NP-completeness | Informal/unverified analysis |
| [ted-swart-1986-87-peqnp](ted-swart-1986-87-peqnp/) | Gap in treating matrix decomposition as a polynomial exact algorithm | Informal/unverified analysis |
| [vega-delgado-2012-pneqnp](vega-delgado-2012-pneqnp/) | Invalid implication between P, UP, EXP, and NP | Informal/unverified analysis |
| [viktor-ivanov-2005-pneqnp](viktor-ivanov-2005-pneqnp/) | Sparse documented evidence; likely common P != NP proof errors | Informal/unverified analysis |
| [vladimir-romanov-2010-peqnp](vladimir-romanov-2010-peqnp/) | Compact-triplets representation hides size/consistency complexity | Informal/unverified analysis |
| [xinwen-jiang-2009-peqnp](xinwen-jiang-2009-peqnp/) | Vague MSP definition, wrong problem class, and experimental evidence | Informal/unverified analysis |
| [yann-dujardin-2009-peqnp](yann-dujardin-2009-peqnp/) | Rounding step does not preserve exact SAT solution | Informal/unverified analysis |
| [yubin-huang-2015-peqnp](yubin-huang-2015-peqnp/) | Invalid reduction and nondeterministic-move elimination gap | Informal/unverified analysis |
| [zeilberger-2009-peqnp](zeilberger-2009-peqnp/) | Joke claim; technically uses nonsensical/wrong-way reduction | Informal/unverified analysis |
| [zohreh-akbari-2008-peqnp](zohreh-akbari-2008-peqnp/) | Clique algorithm handles special cases or hides exponential gap | Informal/unverified analysis |
