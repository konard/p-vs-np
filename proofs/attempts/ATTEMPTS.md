# P vs NP Proof Attempts

This document provides a comparison of all documented P vs NP proof attempts in this repository.
Every entry here has **historical sketch** status. A Lean or Rocq file may compile while containing admissions or unproved axioms; neither compilation nor a refutation folder certifies the author's claim or its refutation. See [certified results](../../scripts/proof_status.json) for the separately audited theorem list.

**Legend:**
- ✓ = Claims P = NP
- ✗ = Claims P ≠ NP
- ? = Claims unprovable
- 📄 = Has ORIGINAL.md (root or original/)
- 📎 = Has original paper file (PDF/HTML/TXT/TEX, root or original/)
- 🔷 = Has Lean formalization
- 🔶 = Has Rocq formalization

Formal badges include legacy root-level `lean/` and `rocq/` files; structure warnings and completeness are reported separately by the checker.

---

| Claim | Author | Year | Title | Docs | Formal | Assurance |
|:-----:|--------|------|-------|:----:|:------:|-----------|
| ✗ | Craig Alan Feinstein | 2005 | [Alan Feinstein (2005) - P≠NP Attempt](alan-feinstein-2005-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Craig Alan Feinstein | 2011 | [Alan Feinstein (2011) - P≠NP Proof Attempt](alan-feinstein-2011-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Amar Mukherjee | 2011 | [Amar Mukherjee (2011) - P=NP via Polynomial-Time 3-SAT Algorithm](amar-mukherjee-2011-peqnp/) | 📄 | 🔷 🔶 | Historical sketch |
| ✓ | Anatoly Panyukov | 2014 | [Anatoly Panyukov (2014) - P=NP Attempt](anatoly-panyukov-2014-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Anatoly D. Plotnikov | 2007 | [Anatoly D. Plotnikov (2007) - P=NP Attempt](anatoly-plotnikov-2007-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Anatoly D. Plotnikov | 2011 | [Anatoly Plotnikov (2011) - P≠NP Attempt](anatoly-plotnikov-2011-pneqnp/) | 📄 | 🔷 🔶 | Historical sketch |
| ✓ | Andrea Bianchini | 2005 | [Andrea Bianchini (2005) - P=NP Attempt](andrea-bianchini-2005-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Angela Weiss | 2011 | [Angela Weiss (2011): proposed polynomial 3-SAT algorithm using KE-tableaux](angela-weiss-2011-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Algirdas Antano Maknickas | 2011 | [Formalization: Antano Maknickas (2011) - P=NP Attempt](antano-maknickas-2011-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Ari Blinder | 2009 | [Ari Blinder (2009) - P≠NP Attempt](ari-blinder-2009-pneqnp/) | 📄 | 🔷 🔶 | Historical sketch |
| ✗ | Arto Annila | 2009 | [Arto Annila (2009) - P≠NP Attempt](arto-annila-2009-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Author104 | 2015 | [Frank Vega (2015): P=NP attempt via equivalent-P](author104-2015-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Selmer Bringsjord and Joshua Taylor | 2004 | [Author 11 (2004) - P=NP Attempt](author11-2004-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Bhupinder Singh Anand | 2004 | [Anand (2004) - P≠NP Attempt](author12-2004-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Marius Ionescu (attributed as "Unknown" in Woeginger's list) | 2004 | [Marius Ionescu (2004) - P ≠ NP via OWMF](author13-2004-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Mircea Alexandru Popescu Moscu (listed as entry #18 on Woeginger's list) | 2004 | [Mircea Alexandru Popescu Moscu (2004) - P≠NP Attempt](author15-2004-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Anatoly D. Plotnikov | 1996 | [Plotnikov (1996) - P=NP via Polynomial-Time Clique Partition](author2-1996-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Miron Telpiz | 2000 | [Formalization: Miron Telpiz (2000) - P=NP Claim](author4-2000-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Givi Bolotashvili | 2003 | [Bolotashvili (2003) - P=NP via Linear Ordering Problem](author7-2003-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Unknown (Hubert Chen's webpage) | 2003 | [Formalization: Unknown (2003) - P≠NP Attempt](author8-2003-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Algirdas Antano Maknickas | 2013 | [Formalization: Maknickas (2013) - P=NP via Linear Programming](author93-2013-peqnp/) | 📄 | 🔷 🔶 | Historical sketch |
| ✗ | Bangyan Wen & Yi Lin | 2010 | [Bangyan Wen & Yi Lin (2010) - P≠NP via Formal Logic Reasoning](bangyan-wen-yi-lin-2010-pneqnp/) | 📄 | 🔷 🔶 | Historical sketch |
| ✗ | Bhupinder Singh Anand | 2008 | [Bhupinder Singh Anand (2008) - P≠NP Attempt](bhupinder-singh-anand-2008-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Carlos Barron-Romero | 2010 | [Carlos Barron-Romero (2010) - P≠NP via E2DTSP versus GAP](carlos-barron-romero-2010-euclidean-tsp-gap-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Carlos Barron-Romero | 2010 | [Carlos Barron-Romero (2010) - P≠NP via Complexity of Solution Verification](carlos-barron-romero-2010-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Changlin Wan (with Zhongzhi Shi) | 2010 | [Changlin Wan (2010) - P=NP Attempt](changlin-wan-2010-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Charles Sauerbier | 2002 | [Charles Sauerbier (2002) - P=NP Attempt](charles-sauerbier-2002-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Rustem Chingizovich Valeyev | 2013 | [Chingizovich Valeyev (2013) - P≠NP Proof Attempt](chingizovich-valeyev-2013-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Craig Alan Feinstein | 2003 | [Craig Alan Feinstein (2003-04) - P≠NP Attempt](craig-feinstein-2003-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Craig Alan Feinstein | 2006 | [Craig Alan Feinstein (2006) - P!=NP Attempt](craig-feinstein-2006-pneqnp/) | 📄 | 🔷 🔶 | Historical sketch |
| ✗ | Daegene Song | 2014 | [Daegene Song (2014) - P≠NP via Quantum Self-Reference](daegene-song-2014-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Daniel Uribe | 2016 | [Daniel Uribe (2016) - P≠NP](daniel-uribe-2016-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Matthew Delacorte / Reiner Czerwinski | 2007 | [Delacorte/Czerwinski (2007) - P=NP/PSPACE via Graph Isomorphism](delacorte-czerwinski-2007-peqnppspace/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Vinay Deolalikar | 2010 | [Vinay Deolalikar (2010) - P≠NP Attempt](deolalikar-2010-pneqnp/) | 📄 | 🔷 🔶 | Historical sketch |
| ✓ | Pawan Tamta, B.P. Pande, H.S. Dhami | 2014 | [Dhami et al. (2014) - P=NP Attempt](dhami-2014-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Dmitriy Nuriyev | 2013 | [Dmitriy Nuriyev (2013) - P=NP via Hamiltonian Path](dmitriy-nuriyev-2013-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Douglas Youvan | 2012 | [Douglas Youvan (2012) - P=NP Attempt](douglas-youvan-2012-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Dr. Joachim Mertz | 2005 | [Dr. Joachim Mertz (2005) - P=NP via MERLIN](dr-joachim-mertz-2005-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Eli Halylaurin | 2016 | [Eli Halylaurin (2016) - P=NP Attempt](eli-halylaurin-2016-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Javier A. Arroyo-Figueroa | 2016 | [Figueroa (2016) - P≠NP Proof Attempt](figueroa-2016-pneqnp/) | 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Francesco Capasso | 2005 | [Francesco Capasso (2005) - P=NP Attempt](francesco-capasso-2005-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Frank Vega Delgado | 2010 | [Frank Vega Delgado (2010) - P≠NP Proof Attempt](frank-vega-delgado-2010-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Frederic Gillet | 2013 | [Frederic Gillet (2013) - P=NP Attempt](frederic-gillet-2013-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Guohun Zhu | 2007 | [Guohun Zhu (2007): P=NP attempt](guohun-zhu-2007-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Jose Ignacio Alvarez-Hamelin | 2011 | [Formalization: Hamelin (2011) - P=NP Attempt](hamelin-2011-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Han Xiao Wen | 2010 | [Han Xiao Wen (2010) - P=NP via Knowledge Recognition Algorithm](han-xiao-wen-2010-peqnp/) | 📄 | 🔷 🔶 | Historical sketch |
| ✓ | Hanlin Liu (刘汉林) | 2014 | [Hanlin Liu (2014) - P=NP Attempt](hanlin-liu-2014-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Seenil Gram (pseudonym "has also") | 2001 | [Seenil Gram (2001): "EXP ⊆ NP" Claim](has-also-2001-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Howard Kleiman | 2006 | [Howard Kleiman (2006) - P=NP via Modified Floyd-Warshall Algorithm for ATSP](howard-kleiman-2006-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Junichiro Fukuyama | 2012 | [InfoTechnology Center (2012) - P≠NP Attempt](infotechnology-center-2012-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Jason W Steinmetz | 2011 | [Jason W. Steinmetz (2011) - P=NP Attempt](jason-w-steinmetz-2011-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Javaid Aslam | 2008 | [Javaid Aslam (2008) - P=NP via Counting Hamiltonian Circuits](javaid-aslam-2008-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Jeffrey W. Holcomb | 2011 | [Jeffrey W. Holcomb (2011) - P≠NP Proof Attempt](jeffrey-w-holcomb-2011-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Jerrald Meek | 2008 | [Jerrald Meek (2008) - Karp Postulates P!=NP Attempt](jerrald-meek-2008-karp-postulates-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Jerrald Meek | 2008 | [Jerrald Meek (2008) - P≠NP Attempt](jerrald-meek-2008-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Joonmo Kim | 2014 | [Joonmo Kim (2014) - P≠NP Attempt](joonmo-kim-2014-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Jorma Jormakka | 2008 | [Jorma Jormakka (2008) - P≠NP Proof Attempt](jorma-jormakka-2008-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Ki-Bong Nam, S.H. Wang, and Yang Gon Kim | 2004 | [Ki-Bong Nam, S.H. Wang, and Yang Gon Kim (2004) - P≠NP Attempt](ki-bong-nam-sh-wang-and-yang-gon-kim-published-2004-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Koji Kobayashi | 2011 | [Koji Kobayashi (2011) - P != NP via CHAOS Dependency Relations](koji-kobayashi-2011-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Koji Kobayashi | 2012 | [Koji Kobayashi (2012): P ≠ NP via Topological Approach](koji-kobayashi-2012-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Cynthia Ann Harlan Krieger & Lee K. Jones | 2008 | [Cynthia Ann Harlan Krieger & Lee K. Jones (2008) - P=NP via Polynomial Hamiltonian Circuit Detection](krieger-jones-2008-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Lev Gordeev | 2005 | [Formalization: Lev Gordeev (2005) - P≠NP](lev-gordeev-2005-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Lizhi Du | 2010 | [Lizhi Du (2010) - P=NP via Polynomial-Time 3SAT Algorithm](lizhi-du-2010-peqnp/) | 📄 | 🔷 🔶 | Historical sketch |
| ✓ | Lokman Kolukisa | 2005 | [Lokman Kolukisa (2005) - P=NP via Tautology Checking](lokman-kolukisa-2005-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Louis Coder (Matthias Michael Mueller) | 2012 | [Louis Coder (Matthias Michael Mueller) 2012 - P=NP Claim](louis-coder-2012-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Luigi Salemi | 2009 | [Luigi Salemi (2009) - P=NP Proof Attempt](luigi-salemi-2009-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | André Luiz Barbosa | 2009 | [Luiz Barbosa (2009) - P≠NP Attempt](luiz-barbosa-2009-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Mathias Hauptmann | 2016 | [Mathias Hauptmann (2016) - P≠NP Proof Attempt](mathias-hauptmann-2016-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Matt Groff | 2011 | [Matt Groff (2011): P=NP attempt](matt-groff-2011-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Michael LaPlante | 2015 | [Michael LaPlante (2015) - P=NP Clique Algorithm Attempt](michael-laplante-2015-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Michel Feldmann | 2012 | [Michel Feldmann (2012) - P=NP via Bayesian Inference](michel-feldmann-2012-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Mikhail Katkov | 2010 | [Mikhail Katkov (2010) - P=NP Attempt](mikhail-katkov-2010-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Mikhail N. Kupchik | 2004 | [Mikhail N. Kupchik (2004) - P ≠ NP Proof Attempt](mikhail-kupchik-2004-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Minseong Kim | 2012 | [Minseong Kim (2012) - P≠NP Attempt](minseong-kim-2012-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Miron Teplitz | 2005 | [Miron Teplitz (2005) - P=NP Attempt](miron-teplitz-2005-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Mohamed Mimouni | 2006 | [Mohamed Mimouni (2006) - P=NP Attempt](mohamed-mimouni-2006-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Moustapha Diaby | 2004 | [Moustapha Diaby (2004) - P=NP via Linear Programming Formulation of TSP](moustapha-diaby-2004-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Narendra S. Chaudhari | 2009 | [Narendra S. Chaudhari (2009) - P=NP Attempt](narendra-chaudhari-2009-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ? | Natalia L. Malinina | 2012 | [Natalia L. Malinina (2012) - P vs NP is Unprovable in ZFC](natalia-malinina-2012-unprovable/) | 📄 | 🔷 🔶 | Historical sketch |
| ? | Newton C.A. da Costa & Francisco A. Doria | 2003 | [Formalization: N.C.A. da Costa & F.A. Doria (2003) - P vs NP Unprovability Claim](ncada-costa-fa-doria-2003-unprovable/) | - | 🔷 🔶 | Historical sketch |
| ? | Nicholas Argall | 2003 | [Nicholas Argall (2003) - P=NP is Undecidable](nicholas-argall-2003-undecidable/) | 📄 | 🔷 🔶 | Historical sketch |
| ✓ | Peng Cui | 2014 | [Peng Cui (2014) - P=NP Claim](peng-cui-2014-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Wen-Qi Duan | 2012 | [Qi Duan (2012) - P=NP Proof Attempt](qi-duan-2012-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Radoslaw Hofman | 2006 | [Radoslaw Hofman (2006) - P≠NP Attempt](radoslaw-hofman-2006-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Rafael Valls Hidalgo-Gato | 2009 | [Rafael Valls Hidalgo-Gato (2009) - P=NP Attempt](rafael-valls-hidalgo-gato-2009-peqnp/) | 📄 | 🔷 🔶 | Historical sketch |
| ✓ | Rafee Ebrahim Kamouna | 2008 | [Rafee Ebrahim Kamouna (2008) - P=NP via Paradox-Based Refutation of Cook's Theorem](rafee-ebrahim-kamouna-2008-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Raju Renjit G | 2006 | [Raju Renjit (2006) - Original Proof Idea](renjit-2006-conpeqnp/) | 📄 | 🔷 🔶 | Historical sketch |
| ✗ | Raju Renjit Grover | 2005 | [Renjit Grover (2005) - P≠NP Proof Attempt](renjit-grover-2005-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Khadija Riaz & Malik Sikander Hayat Khiyal | 2006 | [Khadija Riaz & Malik Sikander Hayat Khiyal (2006) - P=NP via Polynomial-Time Hamiltonian Cycle Algorithm](riaz-khiyal-2006-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Gilberto Rodrigo Diduch | 2012 | [Rodrigo Diduch (2012) - P≠NP Proof Attempt](rodrigo-diduch-2012-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Roman V. Yampolskiy | 2011 | [Formalization: Roman Yampolskiy (2011) - P≠NP](roman-yampolskiy-2011-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Ron A. Cohen | 2005 | [Formalization: Ron Cohen (2005) - P≠NP](ron-cohen-2005-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Rubens Ramos Viana | 2006 | [Rubens Ramos Viana (2006) - P≠NP via Quantum States](rubens-ramos-viana-2006-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Ruijia Liao | 2011 | [Ruijia Liao (2011) - P≠NP via 3SAT_N and Cantor Diagonalization](ruijia-liao-2011-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Alejandro Sanchez Guinea | 2015 | [Sanchez Guinea (2015) - P=NP Claim](sanchez-guinea-2015-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Satoshi Tazawa | 2012 | [Satoshi Tazawa (2012) - P≠NP Proof Attempt](satoshi-tazawa-2012-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Sergey Gubin | 2006 | [Sergey Gubin (2006) - P=NP via Polynomial-Time TSP Algorithm](sergey-gubin-2006-peqnp/) | 📄 | 🔷 🔶 | Historical sketch |
| ✓ | Sergey Gubin | 2010 | [Sergey Gubin (2010) - P=NP via ATSP Polytope Formulation](sergey-gubin-2010-peqnp/) | 📄 | 🔷 🔶 | Historical sketch |
| ✓ | Sergey Kardash | 2011 | [Sergey Kardash (2011) - P=NP via Pair Cleaning Method for k-SAT](sergey-kardash-2011-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Sergey V. Yakhontov | 2012 | [Sergey V. Yakhontov (2012) - P=NP Proof Attempt](sergey_v_yakhontov_2012_peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Bhupinder Singh Anand | 2005 | [Singh Anand (2005) - P≠NP Proof Attempt](singh-anand-2005-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Bhupinder Singh Anand | 2006 | [Bhupinder Singh Anand (2006) - P≠NP Attempt](singh-anand-2006-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Stefan Jaeger | 2011 | [Stefan Jaeger (2011) - Both (P=NP and P≠NP)](stefan-jaeger-2011-both/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Stefan Rass | 2016 | [Stefan Rass (2016) - P≠NP Proof Attempt](stefan-rass-2016-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Sten-Ake Tarnlund | 2008 | [Sten-Ake Tarnlund (2008) - P≠NP via First-Order Theory and Universal Turing Machines](sten-ake-tarnlund-2008-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Steven Meyer | 2016 | [Steven Meyer (2016) - P=NP Proof Attempt](steven-meyer-2016-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Tang Pushan (唐普山) | 1997 | [Tang Pushan (1997) - P=NP Attempt](tang-pushan-1997-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Ted Swart (University of Guelph) | 1986 | [Formal Analysis: Ted Swart (1986/87) - P=NP Claim](ted-swart-1986-87-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✗ | Frank Vega Delgado | 2012 | [Vega Delgado (2012) - P≠NP Proof Attempt](vega-delgado-2012-pneqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✗ | Viktor V. Ivanov | 2005 | [Viktor V. Ivanov (2005) - P≠NP Attempt](viktor-ivanov-2005-pneqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Vladimir F. Romanov | 2010 | [Vladimir Romanov (2010) - P=NP via Compact Triplets Structures](vladimir-romanov-2010-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Xinwen Jiang | 2009 | [Xinwen Jiang (2009) - P=NP via Polynomial Time Algorithm for Hamiltonian Circuit](xinwen-jiang-2009-peqnp/) | 📄 | 🔷 🔶 | Historical sketch |
| ✓ | Yann Dujardin | 2009 | [Yann Dujardin (2009) - P=NP Proof Attempt](yann-dujardin-2009-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Yubin Huang | 2015 | [Yubin Huang (2015) - P=NP Attempt](yubin-huang-2015-peqnp/) | - | 🔷 🔶 | Historical sketch |
| ✓ | Doron Zeilberger | 2009 | [Doron Zeilberger (2009) - P=NP via Subset Sum Algorithm (April Fool's Joke)](zeilberger-2009-peqnp/) | 📄 📎 | 🔷 🔶 | Historical sketch |
| ✓ | Zohreh O. Akbari | 2008 | [Zohreh O. Akbari (2008) - P=NP via Polynomial-Time Clique Algorithm](zohreh-akbari-2008-peqnp/) | 📄 | 🔷 🔶 | Historical sketch |

---

*This file is auto-generated by `scripts/check_attempt_structure.py --generate-list`*
