# Common Errors in P vs NP Proof Attempts

This document groups the proof attempts cataloged in this directory by recurring
errors. It is meant to be read next to [ATTEMPTS.md](ATTEMPTS.md): that file is
the chronological/catalog view, while this file is the "what not to repeat" view.

The groupings below are based on the local attempt READMEs, refutation notes,
and error analyses. An attempt may appear in more than one group when its notes
identify more than one failure mode. The coverage index at the end assigns each
attempt folder to one primary error family so every documented local attempt can
be found from this file.

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

Each row gives the primary error family for the local attempt folder. Use the
individual attempt README or refutation notes for the detailed argument.

| Attempt | Primary common error |
| --- | --- |
| [alan-feinstein-2005-pneqnp](alan-feinstein-2005-pneqnp/) | Lower bound assumed from a restricted algorithm family |
| [alan-feinstein-2011-pneqnp](alan-feinstein-2011-pneqnp/) | Lower bound assumed from an exponential upper bound |
| [amar-mukherjee-2011-peqnp](amar-mukherjee-2011-peqnp/) | Withdrawn/incomplete claimed 3-SAT algorithm; likely hidden exponential or correctness gap |
| [anatoly-panyukov-2014-peqnp](anatoly-panyukov-2014-peqnp/) | LP relaxation assumed to have integer optimum |
| [anatoly-plotnikov-2007-peqnp](anatoly-plotnikov-2007-peqnp/) | Conditional theorem and nonconstructive graph/poset conversion used as algorithm |
| [anatoly-plotnikov-2011-pneqnp](anatoly-plotnikov-2011-pneqnp/) | Invalid diagonalization and circular construction |
| [andrea-bianchini-2005-peqnp](andrea-bianchini-2005-peqnp/) | Encoding and reduction do not preserve the hard problem correctly |
| [angela-weiss-2011-peqnp](angela-weiss-2011-peqnp/) | Hidden exponential tableau/macro enumeration |
| [antano-maknickas-2011-peqnp](antano-maknickas-2011-peqnp/) | LP relaxation and rounding do not preserve SAT |
| [ari-blinder-2009-pneqnp](ari-blinder-2009-pneqnp/) | Unproven NP vs co-NP style claim equivalent to the hard part |
| [arto-annila-2009-pneqnp](arto-annila-2009-pneqnp/) | Informal physical/thermodynamic reasoning without formal lower bound |
| [author104-2015-peqnp](author104-2015-peqnp/) | Type mismatch and incorrect completeness argument |
| [author11-2004-peqnp](author11-2004-peqnp/) | Exponential physical hardware hidden behind polynomial time |
| [author12-2004-pneqnp](author12-2004-pneqnp/) | Provability and decidability confused with complexity |
| [author13-2004-pneqnp](author13-2004-pneqnp/) | Unproven hardness assumption and missing NP-completeness proof |
| [author15-2004-pneqnp](author15-2004-pneqnp/) | Undefined invariance principle and circular separation claim |
| [author2-1996-peqnp](author2-1996-peqnp/) | Graph-to-poset conversion loses information; hidden exponential gap |
| [author4-2000-peqnp](author4-2000-peqnp/) | Insufficient rigor and unsupported P=NP claim |
| [author7-2003-peqnp](author7-2003-peqnp/) | Facet/linear-ordering approach lacks valid polynomial exact algorithm |
| [author8-2003-pneqnp](author8-2003-pneqnp/) | Empirical/temporal fallacy and problem-class confusion |
| [author93-2013-peqnp](author93-2013-peqnp/) | LP/ILP conflation |
| [bangyan-wen-yi-lin-2010-pneqnp](bangyan-wen-yi-lin-2010-pneqnp/) | Logical asymmetry does not imply a complexity lower bound |
| [bhupinder-singh-anand-2008-pneqnp](bhupinder-singh-anand-2008-pneqnp/) | Category confusion between computability/provability and P vs NP |
| [carlos-barron-romero-2010-euclidean-tsp-gap-pneqnp](carlos-barron-romero-2010-euclidean-tsp-gap-pneqnp/) | GAP/E2DTSP variant does not yield the claimed P != NP separation |
| [carlos-barron-romero-2010-pneqnp](carlos-barron-romero-2010-pneqnp/) | Verification complexity misunderstood as NP hardness separation |
| [changlin-wan-2010-peqnp](changlin-wan-2010-peqnp/) | Computability confused with polynomial-time complexity |
| [charles-sauerbier-2002-peqnp](charles-sauerbier-2002-peqnp/) | Local/path consistency does not imply satisfiability |
| [chingizovich-valeyev-2013-pneqnp](chingizovich-valeyev-2013-pneqnp/) | Best-known algorithm treated as a lower bound |
| [craig-feinstein-2003-pneqnp](craig-feinstein-2003-pneqnp/) | Invalid transfer from one machine/model to all algorithms |
| [craig-feinstein-2006-pneqnp](craig-feinstein-2006-pneqnp/) | Sparse documented evidence; likely unsupported lower-bound claim |
| [daegene-song-2014-pneqnp](daegene-song-2014-pneqnp/) | Observer choice and self-reference confused with computational nondeterminism |
| [daniel-uribe-2016-pneqnp](daniel-uribe-2016-pneqnp/) | Decision-tree/model limitation treated as a general lower bound |
| [delacorte-czerwinski-2007-peqnppspace](delacorte-czerwinski-2007-peqnppspace/) | Graph-isomorphism algorithm/cospectral reasoning does not prove P=NP/PSPACE |
| [deolalikar-2010-pneqnp](deolalikar-2010-pneqnp/) | Random-instance/model-theory transfer fails for worst-case P vs NP |
| [dhami-2014-peqnp](dhami-2014-peqnp/) | Invalid reduction involving clique/network interdiction |
| [dmitriy-nuriyev-2013-peqnp](dmitriy-nuriyev-2013-peqnp/) | Hamiltonian-path algorithm lacks proof for all instances |
| [douglas-youvan-2012-peqnp](douglas-youvan-2012-peqnp/) | Heuristic or unsupported algorithmic claim without rigorous proof |
| [dr-joachim-mertz-2005-peqnp](dr-joachim-mertz-2005-peqnp/) | LP relaxation confused with integer programming |
| [eli-halylaurin-2016-peqnp](eli-halylaurin-2016-peqnp/) | Gap between claimed verifier/algorithm and NP-complete solving |
| [figueroa-2016-pneqnp](figueroa-2016-pneqnp/) | Probability argument and one-way-function claim do not prove P != NP |
| [francesco-capasso-2005-peqnp](francesco-capasso-2005-peqnp/) | Heuristic algorithm not proven correct on all inputs |
| [frank-vega-delgado-2010-pneqnp](frank-vega-delgado-2010-pneqnp/) | Missing reduction to an undecidable NP language |
| [frederic-gillet-2013-peqnp](frederic-gillet-2013-peqnp/) | Cost-interference and gate construction flaws |
| [guohun-zhu-2007-peqnp](guohun-zhu-2007-peqnp/) | Incorrect counting and exponential enumeration |
| [hamelin-2011-peqnp](hamelin-2011-peqnp/) | Exponential dependence hidden in a claimed polynomial method |
| [han-xiao-wen-2010-peqnp](han-xiao-wen-2010-peqnp/) | Undefined terminology and oracle/nondeterminism confusion |
| [hanlin-liu-2014-peqnp](hanlin-liu-2014-peqnp/) | Hamiltonian-circuit algorithm contains an unproven correctness gap |
| [has-also-2001-pneqnp](has-also-2001-pneqnp/) | EXP subset NP contradicts standard hierarchy consequences |
| [howard-kleiman-2006-peqnp](howard-kleiman-2006-peqnp/) | Floyd-Warshall shortest-path method solves the wrong problem |
| [infotechnology-center-2012-pneqnp](infotechnology-center-2012-pneqnp/) | Unsupported complexity inference from informal definitions |
| [jason-w-steinmetz-2011-peqnp](jason-w-steinmetz-2011-peqnp/) | P=NP algorithm has an unproven critical correctness step |
| [javaid-aslam-2008-peqnp](javaid-aslam-2008-peqnp/) | Incorrect counting of Hamiltonian circuits |
| [jeffrey-w-holcomb-2011-pneqnp](jeffrey-w-holcomb-2011-pneqnp/) | Nondeterminism/randomness and witness multiplicity confused |
| [jerrald-meek-2008-karp-postulates-pneqnp](jerrald-meek-2008-karp-postulates-pneqnp/) | Karp-postulate special cases treated as a general separation |
| [jerrald-meek-2008-pneqnp](jerrald-meek-2008-pneqnp/) | Invalid asymptotic/lower-bound inferences |
| [joonmo-kim-2014-pneqnp](joonmo-kim-2014-pneqnp/) | Sparse documented evidence; likely unsupported lower-bound proof |
| [jorma-jormakka-2008-pneqnp](jorma-jormakka-2008-pneqnp/) | Circular adversarial/non-uniform lower-bound construction |
| [ki-bong-nam-sh-wang-and-yang-gon-kim-published-2004-pneqnp](ki-bong-nam-sh-wang-and-yang-gon-kim-published-2004-pneqnp/) | Insufficient lower bound |
| [koji-kobayashi-2011-pneqnp](koji-kobayashi-2011-pneqnp/) | Dependency-relation framework lacks a general lower-bound transfer |
| [koji-kobayashi-2012-pneqnp](koji-kobayashi-2012-pneqnp/) | Representation complexity confused with decision complexity |
| [krieger-jones-2008-peqnp](krieger-jones-2008-peqnp/) | Hamiltonian-circuit detector solves an underspecified/different problem |
| [lev-gordeev-2005-pneqnp](lev-gordeev-2005-pneqnp/) | Circuit-complexity gap does not yield the claimed separation |
| [lizhi-du-2010-peqnp](lizhi-du-2010-peqnp/) | Incorrect intersection/pruning step in 3-SAT algorithm |
| [lokman-kolukisa-2005-peqnp](lokman-kolukisa-2005-peqnp/) | Tautology algorithm correctness and formal gap |
| [louis-coder-2012-peqnp](louis-coder-2012-peqnp/) | Local/global consistency and insufficient encoding |
| [luigi-salemi-2009-peqnp](luigi-salemi-2009-peqnp/) | Saturation complexity and constructive proof are circular/unproved |
| [luiz-barbosa-2009-pneqnp](luiz-barbosa-2009-pneqnp/) | Non-uniform circuit argument does not imply P != NP |
| [mathias-hauptmann-2016-pneqnp](mathias-hauptmann-2016-pneqnp/) | Claimed contradiction is not a contradiction |
| [matt-groff-2011-peqnp](matt-groff-2011-peqnp/) | Exponential polynomial size and probabilistic confusion |
| [michael-laplante-2015-peqnp](michael-laplante-2015-peqnp/) | Clique algorithm fails on counterexamples/special structure |
| [michel-feldmann-2012-peqnp](michel-feldmann-2012-peqnp/) | Missing construction algorithm |
| [mikhail-katkov-2010-peqnp](mikhail-katkov-2010-peqnp/) | SDP/local optimum does not yield reliable global certificate |
| [mikhail-kupchik-2004-pneqnp](mikhail-kupchik-2004-pneqnp/) | Sparse documented refutation; unsupported lower-bound claim |
| [minseong-kim-2012-pneqnp](minseong-kim-2012-pneqnp/) | False premise/logical fallacy |
| [miron-teplitz-2005-peqnp](miron-teplitz-2005-peqnp/) | Sparse documented evidence; likely unsupported P=NP claim |
| [mohamed-mimouni-2006-peqnp](mohamed-mimouni-2006-peqnp/) | Clique algorithm works only on special cases or hides exponential work |
| [moustapha-diaby-2004-peqnp](moustapha-diaby-2004-peqnp/) | LP formulation lacks one-to-one correspondence with TSP tours |
| [narendra-chaudhari-2009-peqnp](narendra-chaudhari-2009-peqnp/) | Representation change does not reduce 3-SAT complexity |
| [natalia-malinina-2012-unprovable](natalia-malinina-2012-unprovable/) | Undecidability/independence and self-reference misapplied |
| [ncada-costa-fa-doria-2003-unprovable](ncada-costa-fa-doria-2003-unprovable/) | Critical independence-proof gap and exotic definitions |
| [nicholas-argall-2003-undecidable](nicholas-argall-2003-undecidable/) | Formal undecidability error |
| [peng-cui-2014-peqnp](peng-cui-2014-peqnp/) | Approximation confused with exact solution |
| [qi-duan-2012-peqnp](qi-duan-2012-peqnp/) | Greedy insertion fallacy |
| [radoslaw-hofman-2006-pneqnp](radoslaw-hofman-2006-pneqnp/) | Provability/computability confusion and invalid restriction to FOPC transformations |
| [rafael-valls-hidalgo-gato-2009-peqnp](rafael-valls-hidalgo-gato-2009-peqnp/) | Encoding-complexity barrier and parameter confusion |
| [rafee-ebrahim-kamouna-2008-peqnp](rafee-ebrahim-kamouna-2008-peqnp/) | Cook theorem/paradox category confusion |
| [renjit-2006-conpeqnp](renjit-2006-conpeqnp/) | Invalid generalization from one problem to NP vs co-NP |
| [renjit-grover-2005-pneqnp](renjit-grover-2005-pneqnp/) | Algorithm classification approach lacks universal lower bound |
| [riaz-khiyal-2006-peqnp](riaz-khiyal-2006-peqnp/) | Greedy/backtracking avoidance uses circular valid-selection conditions |
| [rodrigo-diduch-2012-pneqnp](rodrigo-diduch-2012-pneqnp/) | Definitions used without lower-bound proof |
| [roman-yampolskiy-2011-pneqnp](roman-yampolskiy-2011-pneqnp/) | Cryptographic intuition and no-pruning claim do not prove exponential time |
| [ron-cohen-2005-pneqnp](ron-cohen-2005-pneqnp/) | Nonstandard machine/oracle feature changes the problem |
| [rubens-ramos-viana-2006-pneqnp](rubens-ramos-viana-2006-pneqnp/) | Quantum/uncomputability category mistake |
| [ruijia-liao-2011-pneqnp](ruijia-liao-2011-pneqnp/) | Cantor diagonalization does not apply as stated |
| [sanchez-guinea-2015-peqnp](sanchez-guinea-2015-peqnp/) | Exponential recursion and hidden dependency graph |
| [satoshi-tazawa-2012-pneqnp](satoshi-tazawa-2012-pneqnp/) | Automorphism-to-lower-bound connection is missing |
| [sergey-gubin-2006-peqnp](sergey-gubin-2006-peqnp/) | Flawed LP formulation and SAT-to-2SAT reduction |
| [sergey-gubin-2010-peqnp](sergey-gubin-2010-peqnp/) | Missing integrality proof for ATSP polytope formulation |
| [sergey-kardash-2011-peqnp](sergey-kardash-2011-peqnp/) | Local consistency and relationship-structure size errors |
| [sergey_v_yakhontov_2012_peqnp](sergey_v_yakhontov_2012_peqnp/) | TCPE/encoding size problem |
| [singh-anand-2005-pneqnp](singh-anand-2005-pneqnp/) | Provability/computability confusion |
| [singh-anand-2006-pneqnp](singh-anand-2006-pneqnp/) | Nonstandard models and provability do not eliminate computation |
| [stefan-jaeger-2011-both](stefan-jaeger-2011-both/) | Redefined complexity classes yield contradictory/nonstandard claims |
| [stefan-rass-2016-pneqnp](stefan-rass-2016-pneqnp/) | Encoding mismatch, circular density bounds, and finite/asymptotic gap |
| [sten-ake-tarnlund-2008-pneqnp](sten-ake-tarnlund-2008-pneqnp/) | Provability/truth confused with complexity |
| [steven-meyer-2016-peqnp](steven-meyer-2016-peqnp/) | Simulation/model-independence confused with algorithmic content |
| [tang-pushan-1997-peqnp](tang-pushan-1997-peqnp/) | Reduction preserves an easier problem, not NP-completeness |
| [ted-swart-1986-87-peqnp](ted-swart-1986-87-peqnp/) | Gap in treating matrix decomposition as a polynomial exact algorithm |
| [vega-delgado-2012-pneqnp](vega-delgado-2012-pneqnp/) | Invalid implication between P, UP, EXP, and NP |
| [viktor-ivanov-2005-pneqnp](viktor-ivanov-2005-pneqnp/) | Sparse documented evidence; likely common P != NP proof errors |
| [vladimir-romanov-2010-peqnp](vladimir-romanov-2010-peqnp/) | Compact-triplets representation hides size/consistency complexity |
| [xinwen-jiang-2009-peqnp](xinwen-jiang-2009-peqnp/) | Vague MSP definition, wrong problem class, and experimental evidence |
| [yann-dujardin-2009-peqnp](yann-dujardin-2009-peqnp/) | Rounding step does not preserve exact SAT solution |
| [yubin-huang-2015-peqnp](yubin-huang-2015-peqnp/) | Invalid reduction and nondeterministic-move elimination gap |
| [zeilberger-2009-peqnp](zeilberger-2009-peqnp/) | Joke claim; technically uses nonsensical/wrong-way reduction |
| [zohreh-akbari-2008-peqnp](zohreh-akbari-2008-peqnp/) | Clique algorithm handles special cases or hides exponential gap |
