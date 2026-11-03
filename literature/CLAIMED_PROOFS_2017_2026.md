# Claimed P versus NP proofs, 2017 to 2026

Compiled 2026-11-03. Machine-readable rows: [registry.json](registry.json)
(`result_type: claimed-p-vs-np-proof`). Guide: [README.md](README.md).

The [attempts catalog](../proofs/attempts/README.md) follows Woeginger's
"P-versus-NP page" (https://wscor.win.tue.nl/woeginger/P-versus-NP.htm). That
page covers 1986 to 2016 and is no longer updated. This file lists claims made
after it, from 2017 to 2026.

The repository's goal is to formalize and refute every previous attempt. Each
row below is a candidate `proofs/attempts/<slug>/` folder, using the suggested
slug. No folder has been created for these rows yet.

Listing a claim here does not refute it, and does not endorse it. Each row
records what the author claims and the responses that are publicly documented.
A claim without a documented response is not thereby wrong. A documented
critique is not thereby a formal refutation in this repository. Adding a row
never changes a proof status (see [README.md](README.md)).

## How to read the tables

- **Claim** is the direction the author states: `peqnp` (P=NP), `pneqnp`
  (P≠NP), `unprovable` or `undecidable`, `other` (another separation or
  collapse, an equivalence, or a model-relative claim), `both`, or
  **unverified**.
- **Documented status** quotes withdrawals, arXiv comments and published
  critiques. "No documented response" means none was found in the 2026-11-03
  sweep.
- **Family (H)** is a hypothesis about the most likely failure mode, numbered
  as in [COMMON_ERRORS.md](../proofs/attempts/COMMON_ERRORS.md). It is not an
  audit result. A folder's own audit replaces it.
- **Registry id.** The registry id equals the suggested slug, except for three
  rows that were merged with existing registry entries: row 24 is
  `xu-zhou-2023-sat-exhaustive-search`, row 29 is `deng-2024-p-eq-np`, and row
  37 is `arthanari-2026-pedigree-polytope`. The slug is kept in each entry's
  `attempt_slug` field.
- Query the rows offline, for example
  `python3 -I scripts/check_literature_registry.py --type claimed-p-vs-np-proof --since 2025`.

## How this list was built, and its limits

- **arXiv**: the export API (`export.arxiv.org/api/query`) was queried for
  titles and abstracts containing "P versus NP", "P vs NP", "P=NP" or "P != NP"
  in cs.CC, cs.DS, cs.DM, cs.LO, math.CO, math.GM and quant-ph. Further queries
  covered titles with "polynomial" plus an NP-complete problem, critique papers
  in cs.CC, and individual serial authors. Every arXiv row's date, version count
  and comment field comes from the API or the abs page.
- **HAL**: the API (`api.archives-ouvertes.fr`) was queried for Frank Vega's
  records. Every Vega row comes from HAL metadata, including the abstract text.
- **Zenodo**: the API (`zenodo.org/api/records`) was queried for P-vs-NP
  titles. For Zenodo rows, **the claim direction is taken from the title only**,
  and the documents themselves were not read.
- **Attention data**: blogs (Aaronson, Fortnow/Gasarch, Lipton–Regan,
  Trevisan) and Hacker News, through the Algolia API.
- **Not swept**: viXra and ResearchGate. WebSearch returned no vixra.org or
  researchgate.net hits, and their search pages could not be fetched. Preprints.org
  returned HTTP 403 on direct fetch, so its rows rely on search-result snippets.
  cstheory.stackexchange.com could not be fetched.
- **Claims are reported as stated.** No entry is endorsed. In the "status"
  column, "no documented response" means none was found in this sweep. It does
  not mean none exists.
- **The "Family (H)" column is a hypothesis.** It is the researcher's best reading of the
  most likely failure mode, using the numbering of `COMMON_ERRORS.md`. It is
  based on the abstract and any published critique, not on a formal audit.
  Where a published critique names the flaw, the family follows that critique.

COMMON_ERRORS family key: 1 lower bound assumed · 2 hidden exponential work ·
3 LP/SDP relaxation vs integer solution · 4 invalid reduction · 5 easier or
special problem · 6 local or greedy consistency · 7 counting or compression ·
8 heuristics, experiments or probability as proof · 9 nondeterminism, quantum
or physical process · 10 provability vs computability · 11 nonstandard
definitions · 12 circular or axiom-smuggled · 13 diagonalization or
self-reference misuse · 14 known barrier ignored · 15 verification vs search ·
16 uniformity or circuit mismatch · 17 encoding or parameter size · 18 depends
on false statements · 19 incomplete, withdrawn or joke · 20 structure theorem
assumed for all algorithms.

## Claim table

Claim codes: `peqnp` (P=NP), `pneqnp` (P≠NP), `unprovable` / `undecidable`,
`other` (another class separation or collapse, an equivalence, or a
model-relative claim).

### A.1 arXiv (and arXiv-first) claims

| # | Suggested slug | Author(s) | Year | Claim | Venue + URL | Method (one line) | Documented status | Family (H) |
|---|---|---|---|---|---|---|---|---|
| 1 | `norbert-blum-2017-pneqnp` | Norbert Blum (Univ. Bonn) | 2017 | P≠NP | arXiv:1708.03486 v1, "A Solution of the P versus NP Problem", https://arxiv.org/abs/1708.03486v2 | Extends the monotone-circuit "approximation method" (CNF-DNF approximators) to general circuits to get a superpolynomial lower bound for CLIQUE. | **Withdrawn by the author** in v2 (30 Aug 2017). The Tardos function was the decisive counterexample. Replaced in v3 (2020) by a non-claim paper. Full story below. | 18 (the argument would prove a false statement about Tardos's function, which is in P), with 14 (approximation-method barrier) |
| 2 | `mark-inman-2017-peqnp` | Mark Inman | 2017 | P=NP | arXiv:1708.05714 v2 (Apr 2018), https://arxiv.org/abs/1708.05714 | A foundational/ZFC-level argument that uses a "TIME-SPACE equivalence" oracle. | No documented response | 11 |
| 3 | `keum-bae-cho-2018-pneqnp` | Keum-Bae Cho | 2018 | P≠NP | arXiv:1801.09673, "Indistinguishable binomial decision tree of 3-SAT…", https://arxiv.org/abs/1801.09673 | Argues that 3-SAT instances contain "indistinguishable binomial decision trees" that force superpolynomial time. | **Published critique**: Carleton, Chavrimootoo, Taliancich, arXiv:2104.01736 (https://arxiv.org/abs/2104.01736). It finds that a crucial step is unjustified. | 20 (a lower bound for the decision-tree model is read as one for all algorithms) |
| 4 | `angelo-raffaele-meo-2018-pneqnp` | Angelo Raffaele Meo | 2018 | P≠NP | arXiv:1802.05484, "On the P vs NP question: a proof of inequality", https://arxiv.org/abs/1802.05484 | Claims that the minimal implementation cost of a SAT-derived "core function" grows exponentially. | HN item with 4 points and 0 comments (https://news.ycombinator.com/item?id=16393730). No expert response found. | 1 |
| 5 | `tianheng-tsui-2018-unprovable` | Tianheng Tsui | 2018 | other / unprovable | arXiv:1805.01755, "Two theorems about the P versus NP problem", https://arxiv.org/abs/1805.01755 | Claims a language in P is independent of ZFC, and that no fixed polynomial-time machine can be shown to decide a given NP language. | No documented response | 10 |
| 6 | `aizhong-li-2018-peqnp` | Aizhong Li | 2018 | P=NP | arXiv:1809.04519 v4, "A Simple Elementary Proof of P=NP based on the Relational Model of E. F. Codd", https://arxiv.org/abs/1809.04519 | Recasts Turing-machine configurations as relational "shared trichoices" and claims a polynomial simulation of a "periodic" NTM. | No documented response | 2 |
| 7 | `rasoul-ramezanian-2019-unprovable` | Rasoul Ramezanian | 2019 | unprovable (P=NP not provable) | arXiv:1906.09873, https://arxiv.org/abs/1906.09873. Companion arXiv:1907.03533 claims P≠NP in a Brouwer-intuitionist model (https://arxiv.org/abs/1907.03533) | "Computer-Simulation Model Theory" builds a simulation model in which P=NP fails. | Both papers carry arXiv admin notes on text overlap with arXiv:1205.5994. No expert response found. | 11 (model-relative), with 10 |
| 8 | `konstantinos-kyritsis-2019-unknown` | Konstantinos E. Kyritsis | 2019 | **unverified** (the abstract does not state the direction) | arXiv:1902.07265 v25 (Sep 2026), "The solutions of the 3rd and 4th Clay Millennium problems", https://arxiv.org/abs/1902.07265 | Joint "solution" of P vs NP and Navier–Stokes. | arXiv admin note on text overlap with arXiv:1108.1165 by other authors. No expert response found. | 19 |
| 9 | `boyu-sima-2019-pneqnp` | Boyu Sima | 2019 | P≠NP | arXiv:1911.00722 v2, https://arxiv.org/abs/1911.00722 | Replaces NOT gates by constant 1 in a clique circuit, to transfer monotone lower bounds to general circuits. | **Published critique**: Brendon Pon, arXiv:2005.03256 (https://arxiv.org/abs/2005.03256), with a simple counterexample. | 4 (an invalid circuit transformation), with 14 |
| 10 | `vasil-penchev-2020-pneqnp` | Vasil Penchev | 2020 | P≠NP | arXiv:2005.01412, https://arxiv.org/abs/2005.01412 | Builds "examples" from quantum superposition and the Kochen–Specker theorem. | No documented response | 9 |
| 11 | `lev-gordeev-2020-pneqnp` | Lev Gordeev | 2020 | P≠NP | arXiv:2005.00809 v10 (May 2026), https://arxiv.org/abs/2005.00809 | Approximation-method lower bound for CLIQUE on De Morgan normal circuits. Later versions mention checks in a proof assistant. | v4 (Feb 2021) was posted as **withdrawn**, then revisions resumed. **Published critique** of an earlier version: Narváez & Phillips, arXiv:2104.07166 (https://arxiv.org/abs/2104.07166). It finds that Lemma 12 only approximates positive inputs, and that negated inputs are not handled. The author keeps revising, through v10 in 2026. | 14 (monotone-method extension), with 16 |
| 12 | `rupert-mccallum-2020-pneqnp` | Rupert McCallum | 2020 | P≠NP (claimed provable in PA) | arXiv:2005.10080 v15 (Feb 2026), math.LO, https://arxiv.org/abs/2005.10080 | Diagonal lemma with arithmetically definable sequences of sentences. | 15 versions. No documented response. | 13 |
| 13 | `tianrong-lin-2020-pneqnp` | Tianrong Lin | 2020 | P≠NP | arXiv:2003.09791 v15, "A 'Proof' of P≠NP", https://arxiv.org/abs/2003.09791 | Informal argument. | **Withdrawn by the author** (Oct 2021). The comment cites a flaw (ℕ is not bounded above) and points to the 2021 paper (row 19). | 19 |
| 14 | `ioannis-avramopoulos-2020-peqnp` | Ioannis Avramopoulos | 2020 | P=NP | arXiv:2008.06167 v13 (Nov 2021), "Poising on Ariadne's thread…", https://arxiv.org/abs/2008.06167 | Game-theoretic dynamical system claimed to find a maximum clique in polynomial time. | 13 versions. No documented response. | 2 (convergence time not polynomially bounded), with 6 |
| 15 | `o-v-german-2020-pneqnp` | O. V. German | 2020 | P≠NP | arXiv:2011.02868, "Postulate-based proof of the P != NP hypothesis", https://arxiv.org/abs/2011.02868 | Two postulates require that solvers treat independent conditions separately. | No documented response | 12 (the conclusion is built into the postulates) |
| 16 | `latif-salum-2020-peqnp` | Latif Salum | 2020 | P=NP (=PSPACE) | arXiv:2012.06304 v8 (Dec 2022), "The Complexity of X3SAT: P = NP = PSPACE", https://arxiv.org/abs/2012.06304 | Polynomial algorithm for exact-3SAT (X3SAT). The abstract also mentions Graph Isomorphism. | No documented response | 6 (tentative; the method is not described in the abstract) |
| 17 | `manoj-kumar-2021-peqnp` | Manoj Kumar | 2021 | P=NP | arXiv:2101.05597 v3, https://arxiv.org/abs/2101.05597 | SAT via "fully populated clauses" and "sibling clauses". | **Published critique**: Chavrimootoo & Welles, arXiv:2112.06062 (https://arxiv.org/abs/2112.06062). It finds the basis of the algorithm needs exponentially many steps on infinitely many inputs. | 2 |
| 18 | `xinwen-jiang-2021-peqnp` | Xinwen Jiang, Holden Wool | 2021 | P=NP | arXiv:2108.03877 v4 (Aug 2025), cs.DS, https://arxiv.org/abs/2108.03877 | O(\|E\|^9) algorithm for the "Multi-stage graph Simple Path" problem, claimed NP-complete. Continues Jiang's 2009–2013 Hamilton-circuit line (arXiv:1305.5976). | No documented response found | 6 |
| 19 | `tianrong-lin-2021-pneqnp` | Tianrong Lin | 2021 | P≠NP | arXiv:2110.06211 v34 (Jun 2025), https://arxiv.org/abs/2110.06211. Companion claims: NP⊊PSPACE (arXiv:2106.11886) and L⊊NL / LBA question (arXiv:2110.05942) | Diagonalizes against all polynomial-time DTMs with a universal NTM. | 34 versions, with an arXiv admin note on text overlap. No direct critique of this paper found, but see row 30. | 13 |
| 20 | `jonathan-mize-2021-pneqnp` | Jonathan J. Mize | 2021 | P≠NP | arXiv:2109.10670, "Machines as Programs: P ≠ NP", https://arxiv.org/abs/2109.10670 | "Ceiling Machines" and a state-transition graph problem (CNDS). | No documented response | 11 |
| 21 | `gao-ming-2022-pneqnp` | Gao Ming | 2022 | P≠NP | arXiv:2203.05022 v13 (Oct 2026), https://arxiv.org/abs/2203.05022 | Designs a block cipher and argues that key recovery needs brute force, citing the unsolvability of the general quintic. | No documented response | 1, with 18 |
| 22 | `petar-petrov-2022-peqnp` | Petar P. Petrov | 2022 | P=NP | arXiv:2208.07327 v4 (Aug 2024), "A polynomial-time algorithm for deciding the Hilbert Nullstellensatz over Z₂. A proof of P=NP hypothesis", https://arxiv.org/abs/2208.07327 | Polynomial-time Nullstellensatz decision over Z₂. | **Withdrawn by the author** on arXiv: v4 (2024-08-22) is marked withdrawn, and its comment says a polynomial-time algorithm does not follow from Theorem 2, so Theorem 3 is not proved. HN: 34 points, 55 comments (https://news.ycombinator.com/item?id=32483726). | 19, with 2 |
| 23 | `jian-gang-tang-2022-pneqnp` | Jian-Gang Tang | 2022 | P≠NP | arXiv:2209.15410 v7 (Mar 2024), "Exploring P versus NP", https://arxiv.org/abs/2209.15410 | Reduces an EXP-complete problem to NP ("EXP=NP"), then applies the hierarchy theorem. | No documented response | 17 (the reduction cannot be polynomial-size) |
| 24 | `ke-xu-guangyan-zhou-2023-pneqnp` | Ke Xu, Guangyan Zhou | 2023 | P≠NP ("stronger than P≠NP"; claims SAT needs exhaustive search) | arXiv:2302.09512 v9, https://arxiv.org/abs/2302.09512. **Journal**: Frontiers of Computer Science 19(12):1912405 (2025), https://doi.org/10.1007/s11704-025-50231-4 | Model RB CSP/SAT instances, plus an argument that every algorithm must recurse through size-(n−1) subinstances. | **Two published critiques.** (i) Chavrimootoo, He, Kotler-Berkowitz, Liuson, Nie, arXiv:2312.02071 (https://arxiv.org/abs/2312.02071): the paper assumes every algorithm has a particular self-reduction structure. (ii) Allender & Williams, comment to the journal (https://people.cs.rutgers.edu/~allender/papers/allender.williams.pdf): the claimed d^{cn} lower bound for k=2 contradicts Williams's 2005 O(d^{0.8n}) algorithm. They recommended retraction, and the editor-in-chief declined (guest post: https://blog.computationalcomplexity.org/2025/08/some-thoughts-on-journals-refereeing.html). | 20, with 18 |
| 25 | `bojin-zheng-2023-pneqnp` | Bojin Zheng, Weiwu Wang | 2023 | P≠NP | arXiv:2303.03958, "The Linear Correlation of P and NP", https://arxiv.org/abs/2303.03958 | Linear (in)dependence of matrices derived from instances. | No documented response | 11 |
| 26 | `jinchuan-cui-2023-peqnp` | Jinchuan Cui, Xiaoya Li | 2023 | P=NP (implicit) | arXiv:2305.12478, "The airplane refueling problem is NP-complete and is solvable in polynomial time", https://arxiv.org/abs/2305.12478 | Sequential-search algorithm for a problem the paper also claims is NP-complete. The abstract does not state P=NP. | No documented response | 17 (likely pseudo-polynomial vs. polynomial, or a flawed NP-hardness proof) |
| 27 | `yangjun-chen-2023-peqnp` | Yangjun Chen | 2023 | P=NP | arXiv:2304.12517 v27 (Oct 2026), "Solving 2-MAXSAT in Polynomial Time: a Proof of P = NP", https://arxiv.org/abs/2304.12517. An earlier conference paper is cited by the critique. | Graph-search algorithm for 2-MAXSAT, O(n²(n+m)⁴). | v18 (May 2024) was posted as **withdrawn**, then revisions resumed (v19–v27). **Published critique** of an earlier version and the conference paper: Le, Reidy, Smith, arXiv:2404.00006 (https://arxiv.org/abs/2404.00006), with counterexamples. | 6 |
| 28 | `robert-quigley-2024-peqnp` | Robert Quigley | 2024 | P=NP | arXiv:2406.08489, "A Polynomial Time Algorithm for 3SAT", submitted 2024-02-12, https://arxiv.org/abs/2406.08489 | Derives clauses from pairs that share a complementary literal until a contradiction appears. This is a restricted resolution. | **Published critique**: DeJesse, Lyudovyk, Pai, arXiv:2510.22985 (https://arxiv.org/abs/2510.22985). Several lemmas fail, and an infinite family of unsatisfiable formulas is accepted. | 6 |
| 29 | `zikang-deng-2024-peqnp` | Zikang Deng | 2024 | P=NP | arXiv:2405.08051 v3, "P=NP", https://arxiv.org/abs/2405.08051 | SDP R(G) claimed to decide 3-colourability of graphs with maximum degree 4. | **Withdrawn by the author** ("incorrect lemma"). **Published critique**: Humphreys et al., arXiv:2507.09018 (https://arxiv.org/abs/2507.09018). It finds a confusion between subgraphs and induced subgraphs. | 3, with 11 |
| 30 | `tianrong-lin-2024-other` | Tianrong Lin | 2024 | other (NP≠coNP, hence P≠NP) | arXiv:2406.10476 v30 (Oct 2026), first titled "On NP versus coNP and Frege Systems", now "Simulating Polynomial-Time Nondeterministic Turing Machines via Nondeterministic Turing Machines", https://arxiv.org/abs/2406.10476 | Diagonal language L_d is claimed to be in NP but not in coNP. Also claims a Frege lower bound. | v15 (Mar 2025) was posted as **withdrawn**, then revisions resumed. **Published critique** of an earlier version: DeJesse, Lyudovyk, Pai, Reidy, arXiv:2505.05658 (https://arxiv.org/abs/2505.05658). The machine D is flawed, and L_d is not in NP. | 13 |
| 31 | `s-gill-williamson-2024-unprovable` | S. Gill Williamson | 2024 | other ("P=NP either false or independent of ZFC") | arXiv:2404.00468, math.LO, https://arxiv.org/abs/2404.00468 | Conjectures that a statement built from Friedman's Jump Free Theorem is independent of ZFC. | The abstract itself is conjectural. No documented response. | 10 |
| 32 | `arne-hole-2024-other` | Arne Hole | 2024 | other (constructive unsolvability) | arXiv:2406.16843 v13 (Sep 2026), "Constructive solvability and the P versus NP problem", https://arxiv.org/abs/2406.16843 | Argues that no constructible, sound theory can verify a solving algorithm for a family of problems that contains an NP problem. | 13 versions. No documented response. | 10 |
| 33 | `changryeol-lee-2025-peqnp` | Changryeol Lee | 2025 | P=NP | arXiv:2508.13166 v8 (Jul 2026), "Graph-Based Deterministic Polynomial Framwork for NP Problems", https://arxiv.org/abs/2508.13166. Implementation: arXiv:2602.10991 (https://arxiv.org/abs/2602.10991) with code at https://github.com/changryeol-hub/poly-np-sim | Merges the verifier computations for all certificates into one "time-valued DAG" with "total collapse". | No expert response found. A Zenodo copy exists (https://zenodo.org/records/18664891). | 2 (the merged computation graph does not preserve per-certificate consistency), with 6 |
| 34 | `ben-goertzel-2025-pneqnp` | Ben Goertzel | 2025 | P≠NP | arXiv:2510.08814. v1 title: "P ≠ NP: A Non-Relativizing Proof via Quantale Weakness and Geometric Complexity". v2 (Apr 2026) title: "A Quantale-Weakness Route to P≠NP…", https://arxiv.org/abs/2510.08814 | If P=NP, a polytime-bounded conditional description length would be constant on a SAT ensemble. Claims a high-probability lower bound that contradicts this. | The v2 title moved from "Proof" to "Route". No expert response found. No AI-assistance disclosure on the abs page. | 1, with 14 |
| 35 | `jian-gang-tang-2025-pneqnp` | Jian-Gang Tang | 2025 | P≠NP | arXiv:2510.17829 v2, "A Homological Separation of P from NP via Computational Topology and Category Theory", https://arxiv.org/abs/2510.17829 | Homology of a category "Comp" of computational problems. Lean 4 code is claimed. | HN item 45677397: 12 points, 21 comments (https://news.ycombinator.com/item?id=45677397). Commenters, including an account named johncarlosbaez (identity unverified), report that the linked GitHub repository returns 404, that a theorem fails because Comp is not additive, and that Theorems 3.24 and 4.1 are mutually inconsistent. Commenter claims are unverified. | 11 |
| 36 | `darren-edwards-2025-pneqnp` | Darren J. Edwards | 2025 | P≠NP | arXiv:2512.11820 v5 (Jan 2026), 208 pp., https://arxiv.org/abs/2512.11820. Zenodo copies: https://zenodo.org/records/18071489 and https://zenodo.org/records/18285337 | Compiles polynomial-time computation into sum-of-squares polynomials and proves "SPDP rank" lower bounds for #3SAT. | The abstract leaves community verification and machine-checked formalization to future work. No expert response found. | 20, with 16 |
| 37 | `tiru-arthanari-2025-peqnp` | T. S. (Tiru) Arthanari | 2025–26 | P=NP | arXiv:2507.09069 (2025, https://arxiv.org/abs/2507.09069) and arXiv:2606.03194 (2026), "Lean 4 Machine-Verified Proof of P = NP via the Pedigree Polytope Membership Problem", https://arxiv.org/abs/2606.03194. Lean code: https://github.com/TiruArt/Pedigree-Polytopes-Lean4 | Claims a strongly polynomial membership test for the pedigree polytope via multicommodity flow. STSP reduces to it, giving P=NP. | No expert response found. The repository README lists the Maurras separation, GLS optimisation, Tardos, Rao, Cook and Karp results as Lean `axiom`s. It also states the **necessity** direction of the membership characterisation as an axiom ("ongoing work"), so the machine check does not cover the crucial direction. | 3 (polytope/LP route), with 12 (crucial direction axiomatised) |
| 38 | `moustapha-diaby-2016-26-peqnp` | Moustapha Diaby | 2016 / 2026 journal | P=NP | arXiv:1610.00353 v13 (Apr 2026), https://arxiv.org/abs/1610.00353. Journal version: *Logistics* 10(3):63, published 2026-03-12, DOI 10.3390/logistics10030063 (Crossref record checked 2026-11-03; journal page not opened). Related: arXiv:1902.03549 and arXiv:2304.07716 (with Karwan and Sun) argue that the extended-formulation barriers do not apply. | Θ(m⁹) ternary network-flow LP model of the assignment polytope, applied to TSP and other hard problems. | The arXiv comment lists "Results of an assessment by the Grok AI". Diaby's 2004 attempt is already catalogued (`moustapha-diaby-2004-peqnp`). The extended-formulation lower bounds (Fiorini et al.; Yannakakis) are the standard response, and Diaby disputes that they apply. | 3, with 14 |
| 39 | `fabio-buono-2026-undecidable` | Fabio F. G. Buono | 2026 | other (the v6 abstract says the framework "suggests" undecidability, then "resolves the apparent paradox") | arXiv:2607.07723 v6, https://arxiv.org/abs/2607.07723 | A "Double Bind" obstruction framework for uniform certification. | No documented response | 10 |
| 40 | `baumann-rolandi-2026-peqnp` | Veronika Baumann, Alberto Rolandi | 2026 | other / P=NP (conditional on many-worlds plus quantum suicide) | arXiv:2603.28869, quant-ph, "Quantum Suicide in Many-Worlds Implies P=NP", https://arxiv.org/abs/2603.28869 | Postselection by "quantum suicide". | The arXiv comment reads "extremely serious paper". The authors' intent is not documented. The physical model differs from P. | 9, with 19 |

### A.2 Frank Vega (serial; HAL, Zenodo, Preprints.org, EasyChair, engrXiv; one journal)

Vega's earlier works are catalogued as `frank-vega-delgado-2010-pneqnp` and
`vega-delgado-2012-pneqnp`. His arXiv:1011.2730 was withdrawn by arXiv admin
for use of a pseudonym (arXiv API comment). His 2017–2026 output has argued
both directions. HAL lists 110 records under his name.

| # | Suggested slug | Year | Claim | Venue + URL | Method (one line, from the abstract) | Status | Family (H) |
|---|---|---|---|---|---|---|---|
| 41 | `frank-vega-2017-pneqnp` | 2017 | P≠NP | HAL hal-01509423 "On P versus NP" (https://hal.science/hal-01509423v1) and hal-01533051v4 "P versus NP" (https://hal.science/hal-01533051v4) | (i) A coNP problem not in P, so P≠coNP and hence P≠NP. (ii) Claims ∀k TIME(n^{k/2})≠NTIME(n^{k/2}). | No documented response | 1 |
| 42 | `frank-vega-2017-other` | 2017 | other (UP=NP) | HAL hal-01473582 "On UP versus NP and Infinite Turing machines", https://hal.science/hal-01473582v1 | "General Quadratic Congruences" claimed NP-complete and in UP. | No documented response | 4 |
| 43 | `frank-vega-2018-pneqnp` | 2018 | P≠NP | HAL hal-01925735 "P versus NP", https://hal.science/hal-01925735v1. Also "A Solution of the P versus NP Problem", hal-02176064 (2019), https://hal.science/hal-02176064v1 | Reductio: a problem not in FP would be in FP under P=NP. A coNP problem is claimed not solvable in polynomial time. | No documented response | 1 |
| 44 | `frank-vega-2019-other` | 2019 | other (LOGSPACE=P) | HAL hal-01999029 "LOGSPACE vs P", https://hal.science/hal-01999029v1 | MAXIMUM decided in log space, then a claimed P-completeness/succinct-version argument. | No documented response | 4 |
| 45 | `frank-vega-2019-peqnp` | 2019–24 | P=NP | Zenodo 3239465 "The P versus NP Problem" (https://zenodo.org/records/3239465). Preprints.org 201908.0037, versions to v14 (https://www.preprints.org/manuscript/201908.0037). Cited inside later preprints as "Note for the P versus NP problem", *IPI Letters* 2024, 14–18, doi:10.59973/ipil.92 (journal page not opened) | MONOTONE 1-IN-3 3SAT reduced to 2SET PACKING. Later version: "Monotone Weighted Xor 2-SAT" claimed NP-complete and in P. | No documented response. Journal publication is cited but not opened. | 4 |
| 46 | `frank-vega-2020-peqnp` | 2020 | P=NP | HAL hal-02199310v14 "P versus NP", https://hal.science/hal-02199310v14 | "SELECTOR-3SAT" solved via sums of weighted densities of states. The abstract says the satisfiable formula is *assumed* to have the minimum sum. | No documented response | 12 (the key property is assumed) |
| 47 | `frank-vega-2022-pneqnp` | 2022 | P≠NP (conditional, "under the assumption of certain hypothesis") | HAL hal-03565476 "Short Note on P vs NP", https://hal.science/hal-03565476v1 (also Zenodo 6042256) | Conditional argument. | No documented response | 12 |
| 48 | `frank-vega-2023-other` | 2023 | other (NP ⊆ NSPACE(log² n)) | HAL hal-03939545v11 "NP on Logarithmic Space", https://hal.science/hal-03939545v11. Presented at the "Mediterranean International Conference of Pure & Applied Mathematics" (hal-04179036) | Log-space reductions. | No documented response | 18 (this would imply NP≠PSPACE, among other consequences) |
| 49 | `frank-vega-2023-peqnp` | 2023 | P=NP | HAL hal-04233658 "On Feasibly Solving NP-complete Problems", https://hal.science/hal-04233658v2 | Monotone ONE-IN-THREE 3SAT converted to linear constraints over the **reals**, then solved by LP. | No documented response | 3 |
| 50 | `frank-vega-2024-peqnp` | 2024–25 | P=NP | HAL hal-04420462v12 "Note for the P versus NP Problem (II)" (https://hal.science/hal-04420462v12), hal-04671513 "Solving NP-complete Problems Efficiently", hal-04841785 "On the P Versus NP Problem", hal-04853280v3 "SAT in Polynomial Time: A Proof of P = NP" (https://hal.science/hal-04853280v3). Preprints.org 202409.2053, versions v1–v21, latest title "MONOTONE-MIN-3SAT in Polynomial Time: A Proof of P = NP" (https://www.preprints.org/manuscript/202409.2053/v21). engrXiv 4189 (https://engrxiv.org/preprint/view/4189) | EXACT CLOSURE, then NAE-3SAT-style clause conditions, then MONOTONE-MIN-3SAT, each claimed both NP-complete and in P. | No documented response | 4 |
| 51 | `frank-vega-2025-peqnp` | 2025 | P=NP ("strong evidence") | HAL hal-04992249 "A Breakthrough in Graph Optimization: Solving the Minimum Vertex Cover Problem", https://hal.science/hal-04992249v1. Also hal-05108499 "Disproving the Unique Games Conjecture" (<2-approximation for vertex cover) | MVC reduced to Minimum Dominating Set on a constructed chordal graph, claimed O(\|V\|²). | No documented response | 4 |

### A.3 Zenodo and other repositories (2023–2026). The claim is read from the title only.

These rows come from the Zenodo REST API and give title, creator and date. The
PDFs were not read. Their volume grows sharply in 2025–2026. Since 2023 the
Zenodo title search returns about 1.2k records for P-vs-NP-like titles, many of
them false positives such as "PNP". These rows should be triaged before any
formalization effort.

| # | Suggested slug | Author(s) | Date | Claim (title) | URL | Family (H) |
|---|---|---|---|---|---|---|
| 52 | `mirzakhmet-syzdykov-2023-pneqnp` | Mirzakhmet Syzdykov | 2023-12 to 2025-08 | P≠NP ("P != NP", 2024-01) and "proofs of the 'P versus NP' theorem" (8+ records) | https://zenodo.org/records/10572466, https://zenodo.org/records/10370770, https://zenodo.org/records/16904483 | 19 |
| 53 | `xinyi-zhou-2024-peqnp` | Xinyi Zhou | 2024-06 | P=NP ("Proof of P = NP in the P versus NP Problem") | https://zenodo.org/records/12668531 | 19 (unread) |
| 54 | `one-polynomial-2024-peqnp` | "One Polynomial" (pseudonym) | 2024-10 | P=NP ("P=NP, proof by halting problem", V1 and V2) | https://zenodo.org/records/13943158, https://zenodo.org/records/13958908 | 10 |
| 55 | `bryn-morgan-2025-unknown` | Bryn Morgan | 2025-02 | direction **unverified** ("Definitive Proof for P Vs NP (Definitive Updated Version)", 2025-02-02) | https://zenodo.org/records/14789641 | 19 |
| 56 | `matthew-hall-2025-unknown` | Matthew Hall | 2025-03 | direction **unverified** ("An Entropy Based Solution to the P vs NP Problem") | https://zenodo.org/records/15016896 | 9 |
| 57 | `javier-munoz-de-la-cuesta-2025-pneqnp` | Javier Muñoz de la Cuesta | 2025-05 | P≠NP ("A Formal Proof of P ≠ NP: Self-Referential Complexity…") | https://zenodo.org/records/15351379 | 13 |
| 58 | `andrew-murphy-2025-pneqnp` | Andrew J. Murphy | 2025-05 | P≠NP (two records: "entropic reconstruction barriers" and "witness incompressibility") | https://zenodo.org/records/15366509, https://zenodo.org/records/15529778 | 7 |
| 59 | `luis-morato-de-dalmases-2025-both` | Luis Morató de Dalmases | 2025-05 / 2025-09 | **both**: P=NP ("A Geometric Proof of P= NP Using Temporal Complexity", May) and P≠NP ("A Spectral-Combinatorial Proof of P ≠ NP", Sep) | https://zenodo.org/records/15434257, https://zenodo.org/records/17141805 | 19 |
| 60 | `yoshinori-shimizu-2025-peqnp` | Yoshinori Shimizu | 2025-08 | P=NP ("Proof of the P=NP Problem") | https://zenodo.org/records/16974316 | 19 (unread) |
| 61 | `nigel-paltoo-2025-pneqnp` | Nigel Paltoo | 2025-12 | P≠NP ("…Analytic Necessity from the Hamiltonian Trace Formula") | https://zenodo.org/records/17958445 | 9 |
| 62 | `lorenzo-taborchia-2026-peqnp` | Lorenzo Taborchia | 2026-03 | P=NP ("P = NP: A Polynomial-Time Solution to 3-SAT") | https://zenodo.org/records/19071831 | 6 (unread) |
| 63 | `mohammad-islam-2026-pneqnp` | Mohammad F. Islam | 2026-04 to 2026-10 | P≠NP ("TRISDUCTION: GEOMETRIC DETERMINATION OF P vs NP", 2026-04-06; "P ≠ NP: Unconditional Proof of the Form by Theorem, the Value by the Act", 2026-10-21; two records opened, the count of 6+ is unverified) | https://zenodo.org/records/19440616, https://zenodo.org/records/23528399 | 11 |
| 64 | `seyed-rasoul-hamzah-2026-peqnp` | Seyed Rasoul Hamzah | 2026-06 | P=NP ("P = NP Solution") | https://zenodo.org/records/20583186 | 19 (unread) |
| 65 | `jason-moretti-2026-peqnp` | Jason Moretti | 2026-09 | P=NP ("…P = NP via Black Hole Information…") | https://zenodo.org/records/22800624 | 9 |

Other Zenodo items found but not tabulated. Their direction is unclear from
the title, or they are conditional or surveys: Bee Rosa Davis 2026 (P≠NP
"under the Davis axioms", model-relative), Richard J. Reyes 2025 (a
model-relative separation and an "ill-posed" claim), Michael S. Yang 2026
("conditional route to BQP=P=NP"), Polson & Sokolov 2026 ("P = RP: A Monte
Carlo Program for P versus NP"), Kamble 2026 and Bodhivardhan 2026 ("Solution
to P vs NP problem in Mathematics"; direction unverified).

### A.4 Other venues and incidents

| # | Suggested slug | Author(s) | Year | Claim | Venue + URL | Status | Family (H) |
|---|---|---|---|---|---|---|---|
| 66 | `toct-2021-incident-peqnp` | **author unverified** | 2021 | P=NP | ACM Transactions on Computation Theory website. The paper claimed a reduction from 3-SAT to 2-SAT. | Rejected, but a "disposition field" was mistakenly set to accept and the paper appeared online. EiC Ryan O'Donnell had ACM remove it (https://blog.computationalcomplexity.org/2021/07/technical-difficulties.html). HN: 112 points, 102 comments (https://news.ycombinator.com/item?id=27886900). | 4 |
| 67 | `craig-feinstein-2019-other` | Craig Alan Feinstein | 2019 | other (no deterministic exact permanent algorithm faster than ~2^n, which implies FP≠#P) | arXiv:cs/0305035 v27, journal ref *Progress in Physics* 15(2):75–77 (2019), https://arxiv.org/abs/cs/0305035 | The same arXiv number has carried earlier P≠NP versions (Feinstein 2003 is catalogued). No documented response to the 2019 version found. | 20 |
| 68 | `reiner-czerwinski-2021-other` | Reiner Czerwinski | 2021 | other (PSPACE≠EXP) | arXiv:2104.14316 v3, https://arxiv.org/abs/2104.14316 | **Withdrawn by the author** in v3 (2024-03-11), with the comment "There are issues. See arXiv:2304.14575". **Published critique**: Clingerman & Luu, arXiv:2304.14575 (https://arxiv.org/abs/2304.14575), with a counterexample to one theorem. | 18 |

### Borderline items excluded from the counts

These were found but do not claim a resolution, or claim one only conditionally:

- Jarek Duda, arXiv:1703.04456 v14: reformulations of P?=NP, with no claim.
- Friedland & Metere, arXiv:1712.01178: "SAT∉P ⇒ P≠NP" from a "conservation principle".
- Dutta & Mahanta, arXiv:2302.09024: a conjecture that would imply P=NP.
- Drozdowski, arXiv:2401.00947: an information-content argument, with no claim.
- Neukart, arXiv:2401.08668: a thermodynamic "perspective".
- M. Alasli, arXiv:2508.13200 and arXiv:2603.22211: a "barrier", and P=NP ⇒ #P=FP, presented as evidence.
- Philip Maymin, arXiv:2602.20415, "Markets are competitive if and only if P != NP": an equivalence, not a resolution. It drew 231 HN points and 164 comments (https://news.ycombinator.com/item?id=48776345).
- Dong et al., arXiv:2309.05689, "Large Language Model for Science: A Study on P vs. NP" (Microsoft Research and others): GPT-4 in a 97-turn "Socratic reasoning" dialogue produces a P≠NP "proof schema". It is aligned with Xu–Zhou (row 24). This is the first prominent LLM-assisted P-vs-NP paper. Count it with row 24 if desired. Family (H): 8 and 20.

## Norbert Blum 2017: full record

1. **Claim.** On 11 Aug 2017 Norbert Blum (University of Bonn) posted
   arXiv:1708.03486v1, "A Solution of the P versus NP Problem". It claimed a
   superpolynomial lower bound on the general (non-monotone) circuit complexity
   of an explicit monotone function, via CNF-DNF approximators. That bound would
   give P≠NP. Version history: https://arxiv.org/abs/1708.03486v2.
2. **Attention.** Hacker News story "A Solution of the P versus NP Problem?"
   on 2017-08-14: 662 points, 286 comments
   (https://news.ycombinator.com/item?id=15008076). Luca Trevisan's post "On
   Norbert Blum's claimed proof that P does not equal NP" appeared 2017-08-15
   (https://lucatrevisan.wordpress.com/2017/08/15/on-norbert-blums-claimed-proof-that-p-does-not-equal-np/;
   HN 139 points, https://news.ycombinator.com/item?id=15027491). The Register
   covered it (https://www.theregister.com/2017/08/31/pnp_proof_fails_yet_again/).
3. **The Tardos-function objection.** Éva Tardos (1988) gave a monotone function
   that agrees with CLIQUE on the relevant promise inputs. It is polynomial-time
   computable (it sits between clique number and chromatic number, via a
   Lovász-theta-type quantity) but needs exponential-size monotone circuits.
   Blum's argument, applied as written, would also give a superpolynomial
   general lower bound for that function, which is impossible.
   - Gödel's Lost Letter (Lipton–Regan), "On the Edge of Eclipses and P=NP",
     2017-08-17, https://rjlipton.com/2017/08/17/on-the-edge-of-eclipses-and-pnp.
     On Aug 18 a commenter ("vloodin") wrote that the "Tardos example refutes
     the proof, as has been pointed out on stackexchange". The commenter located
     the suspected flaw in Step 1 of the proof of Theorem 6. The post's update of
     22 Aug 2017 reads "This objection and the inference of error have been
     verified." Commenter Stasys Jukna asked the author
     to explain where the proof breaks on Tardos's function.
   - Scott Aaronson, "HTTPS / Kurtz / eclipse / Charlottesville / Blum / P vs.
     NP", 2017-08-25, https://scottaaronson.blog/?p=3409. He reported that "a
     clear consensus had developed among experts that Blum's P≠NP proof was
     irreparably flawed". He named Tardos's function as a counterexample "which
     Blum doesn't address". His earlier post https://scottaaronson.blog/?p=3389
     (2017-08-15) had offered to "again bet $200,000 that the paper won't
     stand".
   - Lance Fortnow, "Not So Powerful", Computational Complexity blog,
     2017-08-31, https://blog.computationalcomplexity.org/2017/08/not-so-powerful.html.
     He revisits Tardos's paper as "Exhibit A" against Blum and adds a note that
     Blum retracted.
   - A cstheory.stackexchange thread on the proof is referenced by The Register
     and by Aaronson. Its exact URL is **unverified**, because the site could not
     be fetched.
4. **Withdrawal.** arXiv v2 (30 Aug 2017) is a withdrawal notice: "The proof is
   wrong. I shall elaborate precisely what the mistake is. For doing this, I
   need some time. I shall put the explanation on my homepage."
5. **Author's explanation.** "The mistake in 'A Solution of the P versus NP
   Problem'", dated 11 Oct 2017,
   https://theory.informatik.uni-bonn.de/blum/PvsNP/mistake.pdf. It opens:
   "Because of Tardos' function [2], the proof of Theorem 6 in [1] has to be
   wrong." Blum states that Theorem 5 (the reduced DNF/CNF characterisation) is
   correct. The error is in evaluating the network on reduced DNF
   representations: at an ∧-gate, the monomials fulfilled by a test input can
   all be trivial monomials replaced by 0. So "Method 1" (gate-by-gate
   evaluation) cannot be used, and the needed property during an approximator
   switch fails.
6. **Replacement.** arXiv v3 (15 Jun 2020), "On the Approximation Method and
   the P versus NP Problem", with the comment "The paper is the replacement of
   the incorrect paper 'A Solution of the P versus NP Problem'". It makes no
   claim of a resolution. Lipton–Regan discuss it in "P<NP", 2020-06-16
   (https://rjlipton.com/2020/06/16/pnp/). Blum there says his methods cannot
   yet give even superlinear general-circuit lower bounds, and he suggests
   looking for P=NP algorithms.
7. **Repo modelling suggestion.** A good formal target is the
   meta-theorem behind the refutation: any argument that gives a superpolynomial
   *general* lower bound for every monotone function with exponential *monotone*
   complexity on these promise inputs also applies to Tardos's function, which is
   in P. This is a concrete refutation pattern for family 14/18. It is the same
   pattern as Razborov's and Tardos's monotone/non-monotone gap.

## Revisions of attempts already in the catalog (A.5)

These are not new rows. They are revisions and rebuttals that matter for the
existing folders.

| Existing folder | Post-2016 fact | URL |
|---|---|---|
| `lizhi-du-2010-peqnp` | arXiv:1004.3702 "A Polynomial time Algorithm for 3SAT" has **98 versions**, v29–v98 posted between Jan 2017 and 29 Oct 2026. **Published critique**: He, Kotler-Berkowitz, Liuson, Nie, arXiv:2404.04395. It shows that an infinite family of satisfiable 3-CNFs is rejected. | https://arxiv.org/abs/1004.3702 ; https://arxiv.org/abs/2404.04395 |
| `luiz-barbosa-2009-pneqnp` | arXiv:0907.3965 "P != NP Proof" reached v80 on 2019-06-28. **Published critique**: Abascal & Maimon, arXiv:1711.07132. | https://arxiv.org/abs/0907.3965 ; https://arxiv.org/abs/1711.07132 |
| `daniel-uribe-2016-pneqnp` | **Published critique**: Welles, arXiv:2205.01189 (2022). The proofs do not cover all algorithms. | https://arxiv.org/abs/2205.01189 |
| `javaid-aslam-2008-peqnp` | arXiv:0812.1385 reached v26 on 2017-10-30 and now claims #P=FP (counting perfect matchings in O(n^45 log n)). The response paper arXiv:0906.5112 reached v4 on 2017-10-07. | https://arxiv.org/abs/0812.1385 ; https://arxiv.org/abs/0906.5112 |
| `jorma-jormakka-2008-pneqnp` | arXiv:0809.4935 reached v4 on 2020-11-20. Comment: "The paper proves that P is not NP." | https://arxiv.org/abs/0809.4935 |
| `koji-kobayashi-2012-pneqnp` | arXiv:1211.5773 (circuit complexity in Hamming space) reached v4 on 2018-05-29. No new standalone claim was found after 2016. | https://arxiv.org/abs/1211.5773 |
| `stefan-rass-2016-pneqnp` | arXiv:1609.01575 "On the Existence of Weak One-Way Functions" reached v4 on 2023-07-18. The abstract makes no explicit P≠NP claim. | https://arxiv.org/abs/1609.01575 |
| `xinwen-jiang-2009-peqnp` | New 2021 paper with Holden Wool (row 18). | https://arxiv.org/abs/2108.03877 |
| `lev-gordeev-2005-pneqnp` | New 2020 paper with a published critique (row 11). | https://arxiv.org/abs/2005.00809 |
| `moustapha-diaby-2004-peqnp` | New LP model. The 2026 journal version is *Logistics* 10(3):63, DOI 10.3390/logistics10030063, confirmed through Crossref (row 38). | https://arxiv.org/abs/1610.00353 |
| `frank-vega-delgado-2010-pneqnp`, `vega-delgado-2012-pneqnp` | Rows 41–51. | HAL author search (see the discovery procedure below) |
| Plotnikov, Katkov, Gubin, Daegene Song, Kardash, Valls | No new arXiv P-vs-NP claim after 2016 was found in author queries. Their ResearchGate and viXra output was **not checked**. | none |

## Discovery procedure

### Machine-queryable endpoints (all tested 2026-11-03)

1. **arXiv API (Atom).** The `sortBy=submittedDate` order makes "new since last
   month" easy.
   - Titles:
     `https://export.arxiv.org/api/query?search_query=ti:%22P%20versus%20NP%22%20OR%20ti:%22P%20vs%20NP%22%20OR%20ti:%22P%3DNP%22%20OR%20ti:%22P%20%3D%20NP%22%20OR%20ti:%22P%20!%3D%20NP%22%20OR%20ti:%22P%20neq%20NP%22&sortBy=submittedDate&sortOrder=descending&max_results=100`
     (search string: `ti:"P versus NP" OR ti:"P vs NP" OR ti:"P=NP" OR ti:"P = NP" OR ti:"P != NP" OR ti:"P neq NP"`).
   - Abstracts in cs.CC:
     `search_query=cat:cs.CC AND (abs:"P=NP" OR abs:"P = NP" OR abs:"P is not equal to NP" OR abs:"P is equal to NP" OR abs:"P \neq NP")`.
     This matches many conditional "unless P=NP" papers, so filter on phrases
     such as "we prove", "implies P=NP", "proof of".
   - Algorithm claims:
     `search_query=cat:cs.CC AND ti:polynomial AND (ti:3SAT OR ti:3-SAT OR ti:SAT OR ti:Hamiltonian OR ti:clique OR ti:"NP-complete" OR ti:TSP OR ti:coloring OR ti:"subset sum")`.
     Run the same query with `cat:cs.DS`, `cat:cs.DM`, `cat:math.CO`, `cat:math.GM`, `cat:cs.LO`, `cat:quant-ph`.
   - Rebuttals (the University of Rochester "critique" series, Hemaspaandra's
     group, is the main source of published refutations):
     `search_query=ti:critique AND cat:cs.CC`. Also try `ti:"refutation"`,
     `ti:"comment on"`, `ti:"evaluating the claims"`.
   - Serial-author watch (`au:` queries): `au:Du_Lizhi`, `au:Lin_Tianrong`,
     `au:Chen_Yangjun`, `au:Gordeev_Lev`, `au:Jiang_Xinwen`, `au:Diaby`,
     `au:Arthanari`, `au:Tang_Jian_Gang`, `au:Lee_Changryeol`, `au:McCallum_Rupert`,
     `au:Barbosa_Andre`, `au:Feinstein`, `au:Kobayashi_Koji`, `au:Aslam_Javaid`,
     `au:Salum_Latif`, `au:Avramopoulos`. For known IDs, use `id_list=` to detect
     new versions: compare `<updated>` and the version suffix. Lizhi Du's
     1004.3702 gains a version every one to three months.
   - Human listing pages: `https://arxiv.org/list/cs.CC/new` (daily) and
     `https://arxiv.org/list/cs.CC/pastweek?show=500`.
     (`https://arxiv.org/a/<id>` author pages exist only for authors who
     registered an ID; `arxiv.org/a/vega_f_1` returned 404.)
2. **HAL API**:
   `https://api.archives-ouvertes.fr/search/?q=title_t:(%22P%20versus%20NP%22%20OR%20%22P%20%3D%20NP%22)&fl=title_s,authFullName_s,producedDate_tdate,uri_s,abstract_s&sort=producedDate_tdate%20desc&rows=100`.
   For a single author: `q=authFullName_t:%22Frank%20Vega%22`.
3. **Zenodo API** (anonymous page size is at most 25):
   `https://zenodo.org/api/records?q=title:"P versus NP" OR title:"P vs NP" OR title:"P = NP" OR title:"P != NP" OR title:"P=NP" OR title:"P≠NP"&sort=mostrecent&size=25&page=N`.
   Drop false positives such as "PNP" (Philippine National Police,
   Poisson–Nernst–Planck, PnP imaging).
4. **Preprints.org, engrXiv, EasyChair, ResearchGate, viXra, SSRN, TechRxiv.**
   These have no reliable anonymous API (Preprints.org returned 403, the viXra
   search 404, and ResearchGate needs a browser). Use a monthly web search
   (`"P versus NP" site:preprints.org`, `site:vixra.org "P=NP"`) or Crossref.
5. **Crossref API**, for journal papers:
   `https://api.crossref.org/works?query.title=%22P%20versus%20NP%22&filter=from-pub-date:2026-10-01&rows=100`.
   Repeat with "P = NP" and "P≠NP". This catches journal versions such as
   *Frontiers of CS* (Xu–Zhou), *Logistics* (Diaby), *IPI Letters* (Vega) and
   *Progress in Physics* (Feinstein).
6. **Attention signals.**
   - HN Algolia: `https://hn.algolia.com/api/v1/search?query=P%20vs%20NP%20proof&tags=story&numericFilters=created_at_i>EPOCH,points>20`.
   - Blogs: `https://scottaaronson.blog/?s=P%3DNP`, `https://blog.computationalcomplexity.org/search?q=proof`, `https://rjlipton.com/?s=claim`.
   - Lean Zulip and MathOverflow tags, for "Lean-verified" claims.

### Suggested monthly procedure for the repo

1. A scheduled script, for example `scripts/scan_new_attempts.py` run from a
   monthly GitHub Action, runs queries 1–3 and 5 with a date filter of the last
   35 days. It deduplicates by arXiv ID, HAL ID, Zenodo ID or DOI against
   [literature/registry.json](registry.json), and writes candidate rows.
2. Triage rule: keep only items whose title or abstract asserts an
   *unconditional* resolution, or an exact polynomial algorithm for a named
   NP-complete problem. Discard "unless P=NP" papers and surveys. Flag new
   versions of tracked items.
3. For each kept item, record the slug, claim, venue, URL, version count,
   withdrawal comment, and any matching "critique" paper. Assign a provisional
   COMMON_ERRORS family, marked as a hypothesis.
4. Prioritise for formalisation: (i) items with a published critique, because
   a concrete counterexample can be formalised; (ii) Lean- or Rocq-"verified"
   claims (Arthanari 2026; Tang 2025 claims Lean code), where the axiom
   inventory can be audited mechanically with `#print axioms`; (iii) items in
   peer-reviewed journals (Xu–Zhou 2025, Diaby 2026).
5. Open one GitHub issue per new attempt, as a sub-issue of #44, mirroring the
   existing workflow.

## Attempts from 2024 to 2026 that drew expert or public attention

1. **Xu & Zhou, "SAT Requires Exhaustive Search"** (row 24) is the most
   significant episode of the period. It was published in Springer's
   *Frontiers of Computer Science* (2025), where one author is a deputy
   editor-in-chief, according to Allender's guest post.
   - Eric Allender and Ryan Williams wrote a formal comment and asked for
     retraction. They argued that the paper's lower bound for 2-variable
     constraints contradicts Williams's 2005 algorithm, and that the proof
     assumes something unwarranted about all SAT algorithms.
   - The editor-in-chief declined to retract. The comment is to be published
     with its final paragraph removed.
   - Sources: Allender's guest post on the Computational Complexity blog
     (2025-08-04; HN 69 points, 36 comments, https://news.ycombinator.com/item?id=44808693)
     and the comment PDF (https://people.cs.rutgers.edu/~allender/papers/allender.williams.pdf).
   - A 2023 Rochester critique (arXiv:2312.02071) reached the same diagnosis:
     an unproven structural assumption on algorithms.
   - The authors' reply is linked from that post
     (https://github.com/kexu999/RBGame/blob/master/Self-reference_as_key_to_proving_extreme_hardness.pdf).
   - A "Comment on 'SAT requires exhaustive search'" appears in *Front. Comput.
     Sci.* 20(1):2001405 (2026). It was seen only as a library-catalogue record,
     so its authors are **unverified**.
   - The same group's LLM paper (Dong et al., arXiv:2309.05689) used GPT-4
     dialogue to reach a P≠NP "proof schema".
2. **LLM-driven surge in claims (2025).** Scott Aaronson, "Cracking the Top
   Fifty!", 2025-05-08 (https://scottaaronson.blog/?p=8861), reports a
   "massively higher-than-usual volume" of emailed P vs NP solutions. He gets
   several a day, many including ChatGPT transcripts in which the model "fills
   in the details". In the comments, Bill Gasarch reports the same for Lance
   Fortnow's inbox. The Zenodo counts in A.3 show the same surge: dozens of
   titled "proofs" in 2025–2026, several in Lean or with AI-generated
   frameworks. Diaby's 2026 arXiv comment cites an "assessment by the Grok AI"
   in support of the claim.
3. **"Machine-verified" claims.** Arthanari 2026 (row 37) advertises a Lean 4
   machine-verified proof of P=NP. Its own README lists the central necessity
   direction, and the GLS separation-to-optimisation step, as axioms. Tang 2025
   (row 35) cites Lean code, but HN commenters found the repository link dead.
   Expert comment found: none. These are directly relevant to this repo, because
   `#print axioms` gives a mechanical refutation of the "verified" label.
4. **Rochester critique pipeline.** The arXiv critique series continued through
   2024–2025: Du (2404.04395), Chen (2404.00006), Lin (2505.05658), Deng
   (2507.09018) and Quigley (2510.22985). These are the only published
   line-by-line rebuttals of 2024–2025 claims.
5. **Hacker News engagement.**
   - Since 2017, P-vs-NP proof claims rarely exceed a few points. The
     exceptions are Blum 2017 (662 points), the 2021 ToCT incident (112), the
     Lipton–Regan "Advice to claimers" post (2019, 153 points;
     https://news.ycombinator.com/item?id=19716303), Petrov 2022 (34 points, 55
     comments), and Tang 2025 (12 points, 21 comments).
   - Maymin 2026 (231 points) concerns an equivalence, not a resolution.
   - Lipton–Regan also wrote "P vs. NP Proof Claims" (2021-08-10,
     https://rjlipton.com/2021/08/10/p-vs-np-proof-claims/).
6. **No 2024–2026 claim found received a Quanta, New Scientist or similar
   news story.** None was treated as plausible by a recognised complexity
   theorist. Reddit, MathOverflow and cstheory were not swept systematically.

## Unverified items (summary)

- The author of the 2021 ToCT 3-SAT→2-SAT paper.
- The exact URL of the cstheory.stackexchange thread on Blum.
- The *IPI Letters* 2024 publication of Vega's "Note for the P versus NP
  problem" (doi:10.59973/ipil.92 is cited inside his preprints; the journal page
  was not opened).
- The authors of the *Front. Comput. Sci.* 20(1):2001405 comment.
- The claim direction of every Zenodo row (title only), of Kyritsis 2019, and of
  the Kamble, Bodhivardhan, Morgan and Hall records.
- The Preprints.org version titles beyond what search snippets showed (site
  returned 403).
- The HN commenter assertions about Tang 2025.
- Whether Goertzel 2025 was LLM-assisted (not disclosed on the arXiv page).
- viXra and ResearchGate were not covered. Expect additional entries there,
  especially from Plotnikov, Kardash and other authors already in the catalog.
