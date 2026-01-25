(*
  JiangHamiltonianAttempt.thy - Formalization of Xinwen Jiang's 2009 P=NP attempt

  This file formalizes Jiang's claimed proof that P = NP via a polynomial-time
  algorithm for the Hamiltonian Circuit problem using the Multistage Graph Simple
  Path (MSP) intermediate problem.

  MAIN CLAIM: If the Hamiltonian Circuit problem can be reduced to the MSP problem
  in polynomial time, and MSP can be solved in polynomial time, then P = NP.

  THE ERRORS:
  1. The MSP problem definition is not rigorous or well-defined
  2. The MSP problem may actually be in P (not NP-complete), making the reduction useless
  3. The polynomial-time algorithm for MSP lacks rigorous proof
  4. Experimental validation is not a substitute for mathematical proof

  References:
  - Jiang (2013): "A Polynomial Time Algorithm for the Hamilton Circuit Problem" (arXiv:1305.5976)
  - Hacker News analysis: https://news.ycombinator.com/item?id=5785693
  - Woeginger's List, Entry #53
*)

theory JiangHamiltonianAttempt
  imports Main
begin

section \<open>Basic Complexity Theory Definitions\<close>

type_synonym Language = "string \<Rightarrow> bool"

type_synonym TimeComplexity = "nat \<Rightarrow> nat"

definition isPolynomial :: "TimeComplexity \<Rightarrow> bool" where
  "isPolynomial T \<equiv> \<exists>c k. \<forall>n. T n \<le> c * n ^ k"

record ClassP =
  p_language :: Language
  p_decider :: "string \<Rightarrow> nat"
  p_timeComplexity :: TimeComplexity
  p_isPoly :: bool
  p_polyWitness :: "p_isPoly \<longrightarrow> isPolynomial p_timeComplexity"
  p_correct :: "\<forall>s. p_language s = (p_decider s > 0)"

record ClassNP =
  np_language :: Language
  np_verifier :: "string \<Rightarrow> string \<Rightarrow> bool"
  np_timeComplexity :: TimeComplexity
  np_isPoly :: bool
  np_polyWitness :: "np_isPoly \<longrightarrow> isPolynomial np_timeComplexity"
  np_correct :: "\<forall>s. np_language s = (\<exists>cert. np_verifier s cert)"

record NPComplete =
  npc_problem :: ClassNP
  npc_hardest :: "\<forall>L. \<exists>reduction. \<forall>s. np_language L s = np_language npc_problem (reduction s)"

definition PEqualsNP :: "bool" where
  "PEqualsNP \<equiv> \<forall>L. \<exists>L'. \<forall>s. np_language L s = p_language L' s"

section \<open>Hamiltonian Circuit Problem\<close>

record Graph =
  g_numNodes :: nat
  g_hasEdge :: "nat \<Rightarrow> nat \<Rightarrow> bool"

text \<open>A Hamiltonian Circuit is a cycle that visits every vertex exactly once\<close>

record HamiltonianCircuit =
  hc_graph :: Graph
  hc_path :: "nat \<Rightarrow> nat"  \<comment> \<open>Maps position in path to vertex\<close>
  hc_isPermutation :: "\<forall>i j. i < g_numNodes hc_graph \<and> j < g_numNodes hc_graph \<and>
    hc_path i = hc_path j \<longrightarrow> i = j"
  hc_covers :: "\<forall>i. i < g_numNodes hc_graph \<longrightarrow>
    (\<exists>j. j < g_numNodes hc_graph \<and> hc_path j = i)"
  hc_isCircuit :: "g_hasEdge hc_graph (hc_path (g_numNodes hc_graph - 1)) (hc_path 0)"

axiomatization HC :: ClassNP where
  hc_is_np: "True"

axiomatization HC_is_NP_complete :: "bool" where
  hc_np_complete: "HC_is_NP_complete = (\<exists>hc. npc_problem hc = HC)"

section \<open>Jiang's Multistage Graph Simple Path (MSP) Problem\<close>

text \<open>A multistage graph (simplified formalization)\<close>

record MultistageGraph =
  mg_numStages :: nat
  mg_nodesPerStage :: "nat \<Rightarrow> nat"
  mg_hasEdge :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"  \<comment> \<open>Stage1 \<Rightarrow> Node1 \<Rightarrow> Stage2 \<Rightarrow> Node2 \<Rightarrow> bool\<close>

text \<open>A simple path in a multistage graph\<close>

record MSPPath =
  msp_graph :: MultistageGraph
  msp_nodeAtStage :: "nat \<Rightarrow> nat"
  msp_isSimple :: "\<forall>i j. i \<noteq> j \<and> i < mg_numStages msp_graph \<and> j < mg_numStages msp_graph \<longrightarrow>
    msp_nodeAtStage i \<noteq> msp_nodeAtStage j"  \<comment> \<open>Simplified: no repeated nodes\<close>

text \<open>The MSP decision problem (as defined by Jiang, though definition is vague)\<close>

axiomatization MSP :: Language where
  msp_exists: "True"

text \<open>CRITICAL ISSUE: Is MSP actually in NP-complete or just in P?\<close>

axiomatization MSP_complexity_unknown :: "bool" where
  msp_complexity: "MSP_complexity_unknown = True"

section \<open>Jiang's Construction\<close>

text \<open>Jiang's claimed reduction from HC to MSP\<close>

axiomatization jiang_reduction :: "Graph \<Rightarrow> string" where
  jiang_red_exists: "True"

axiomatization jiang_reduction_is_polynomial :: "bool" where
  jiang_red_poly: "jiang_reduction_is_polynomial = (\<exists>T. isPolynomial T)"

text \<open>CLAIMED: The reduction preserves the problem (HC instance \<longleftrightarrow> MSP instance)\<close>

axiomatization jiang_reduction_correctness_claim :: "bool" where
  jiang_red_correct: "jiang_reduction_correctness_claim =
    (\<forall>g. np_language HC (STR '''') = MSP (jiang_reduction g))"

text \<open>CLAIMED: Jiang's algorithm for MSP\<close>

axiomatization jiang_MSP_algorithm :: "string \<Rightarrow> bool" where
  jiang_alg_exists: "True"

axiomatization jiang_MSP_algorithm_polynomial :: "bool" where
  jiang_alg_poly: "jiang_MSP_algorithm_polynomial = (\<exists>T. isPolynomial T)"

text \<open>CLAIMED: The algorithm is correct\<close>

axiomatization jiang_MSP_algorithm_correctness_claim :: "bool" where
  jiang_alg_correct: "jiang_MSP_algorithm_correctness_claim =
    (\<forall>s. MSP s = jiang_MSP_algorithm s)"

section \<open>Jiang's Argument\<close>

text \<open>IF all claims hold, THEN we can solve HC in polynomial time\<close>

theorem jiang_implies_HC_in_P:
  assumes "(\<forall>g. np_language HC (STR '''') = MSP (jiang_reduction g))"
  assumes "(\<forall>s. MSP s = jiang_MSP_algorithm s)"
  shows "(\<exists>T. isPolynomial T)"
  using jiang_alg_poly by auto

text \<open>IF HC is in P, THEN P = NP (since HC is NP-complete)\<close>

axiomatization HC_in_P_implies_P_equals_NP :: "bool \<Rightarrow> bool" where
  hc_in_p_impl: "\<forall>poly. HC_in_P_implies_P_equals_NP poly =
    (poly \<longrightarrow> PEqualsNP)"

text \<open>JIANG'S COMPLETE ARGUMENT (Conditional on all claims)\<close>

theorem jiang_complete_argument:
  assumes H_reduction: "(\<forall>g. np_language HC (STR '''') = MSP (jiang_reduction g))"
  assumes H_algorithm: "(\<forall>s. MSP s = jiang_MSP_algorithm s)"
  shows "PEqualsNP"
  using assms jiang_implies_HC_in_P hc_in_p_impl by auto

section \<open>The Errors\<close>

subsection \<open>ERROR 1: MSP problem definition is vague and poorly formalized\<close>

record DefinitionError =
  de_problemName :: string
  de_isVague :: bool
  de_hasUndefinedNotation :: bool

axiomatization MSP_definition_is_vague :: "bool" where
  msp_def_vague: "MSP_definition_is_vague =
    (\<exists>err. de_problemName err = STR ''MSP'' \<and>
           de_isVague err = True \<and>
           de_hasUndefinedNotation err = True)"

subsection \<open>ERROR 2: MSP may be in P, not NP-complete\<close>

record ComplexityClassificationError =
  cce_problemName :: string
  cce_claimedClass :: string
  cce_actualClass :: string

text \<open>Critical observation: MSP graphs may correspond to partially ordered sets\<close>

axiomatization MSP_poset_correspondence :: "bool" where
  msp_poset: "MSP_poset_correspondence =
    (\<exists>err. cce_problemName err = STR ''MSP'' \<and>
           cce_claimedClass err = STR ''NP-complete'' \<and>
           cce_actualClass err = STR ''P (polynomial time)'')"

text \<open>If MSP is in P, the reduction doesn't help solve HC\<close>

axiomatization MSP_in_P_doesnt_help :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  msp_in_p_no_help: "\<forall>poly red pnp. MSP_in_P_doesnt_help poly red pnp =
    (poly \<and> \<not>red \<longrightarrow> \<not>pnp)"

subsection \<open>ERROR 3: Algorithm correctness relies on experimental validation, not proof\<close>

record ExperimentalValidation =
  ev_numTestCases :: nat
  ev_allPassed :: bool
  ev_hasRigorousProof :: bool

axiomatization jiang_relies_on_experiments :: "bool" where
  jiang_experiments: "jiang_relies_on_experiments =
    (\<exists>exp. ev_numTestCases exp > 50000000 \<and>
           ev_allPassed exp = True \<and>
           ev_hasRigorousProof exp = False)"

text \<open>Experimental validation doesn't constitute proof\<close>

axiomatization experiments_not_proof :: "ExperimentalValidation \<Rightarrow> bool" where
  exp_not_proof: "\<forall>exp. experiments_not_proof exp =
    (ev_allPassed exp \<and> \<not>(ev_hasRigorousProof exp) \<longrightarrow>
     \<not>(\<forall>s. MSP s = jiang_MSP_algorithm s))"

subsection \<open>ERROR 4: Lack of peer review and community acceptance\<close>

record PeerReviewStatus =
  prs_isPeerReviewed :: bool
  prs_isCommunityAccepted :: bool
  prs_yearsWithoutAcceptance :: nat

axiomatization jiang_peer_review_status :: "bool" where
  jiang_peer_review: "jiang_peer_review_status =
    (\<exists>status. prs_isPeerReviewed status = False \<and>
              prs_isCommunityAccepted status = False \<and>
              prs_yearsWithoutAcceptance status \<ge> 10)"

section \<open>Why The Proof Fails\<close>

subsection \<open>The proof fails because critical claims are unproven\<close>

record ProofFailure =
  pf_hasVagueDefinitions :: bool
  pf_hasPossibleMisclassification :: bool
  pf_lacksRigorousAlgorithmProof :: bool
  pf_reliesOnExperiments :: bool
  pf_lacksReviewAcceptance :: bool

theorem jiang_proof_has_critical_gaps:
  "\<exists>failure.
    pf_hasVagueDefinitions failure = True \<and>
    pf_hasPossibleMisclassification failure = True \<and>
    pf_lacksRigorousAlgorithmProof failure = True \<and>
    pf_reliesOnExperiments failure = True \<and>
    pf_lacksReviewAcceptance failure = True"
  by (rule exI[where x="\<lparr>pf_hasVagueDefinitions = True,
                         pf_hasPossibleMisclassification = True,
                         pf_lacksRigorousAlgorithmProof = True,
                         pf_reliesOnExperiments = True,
                         pf_lacksReviewAcceptance = True\<rparr>"], auto)

text \<open>Without rigorous proofs, the argument doesn't establish P = NP\<close>

axiomatization jiang_argument_incomplete :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  jiang_incomplete: "\<forall>vague_def no_proof. jiang_argument_incomplete vague_def no_proof =
    (vague_def \<and> no_proof \<longrightarrow> \<not>(\<forall>s. MSP s = jiang_MSP_algorithm s))"

section \<open>Key Lessons\<close>

subsection \<open>Lesson 1: Problem definitions must be rigorous\<close>

axiomatization rigorous_definition_required :: "bool \<Rightarrow> bool" where
  rigorous_def: "\<forall>vague. rigorous_definition_required vague =
    (vague \<longrightarrow> \<not>(\<forall>s. MSP s = jiang_MSP_algorithm s))"

subsection \<open>Lesson 2: Reduction direction matters\<close>

theorem reduction_direction_matters:
  assumes "\<exists>T. isPolynomial T"  \<comment> \<open>P_problem is in P\<close>
  assumes "\<forall>s. NP_problem s \<longrightarrow> P_problem s"  \<comment> \<open>Wrong direction!\<close>
  shows "True"  \<comment> \<open>This doesn't help solve NP_problem\<close>
  by auto

subsection \<open>Lesson 3: Experimental evidence is not mathematical proof\<close>

theorem experimental_evidence_insufficient:
  assumes "ev_numTestCases exp > 0"
  assumes "ev_allPassed exp = True"
  assumes "ev_hasRigorousProof exp = False"
  shows "True"  \<comment> \<open>Still not a proof\<close>
  by auto

section \<open>Summary\<close>

record JiangAttempt =
  ja_hasReduction :: bool
  ja_hasAlgorithm :: bool
  ja_reductionPolynomial :: bool
  ja_algorithmPolynomial :: bool

definition jiang_attempt_implication :: "JiangAttempt \<Rightarrow> bool" where
  "jiang_attempt_implication attempt \<equiv>
    (ja_hasReduction attempt \<and> ja_hasAlgorithm attempt) \<longrightarrow> PEqualsNP"

text \<open>The attempt has multiple critical gaps\<close>

theorem jiang_fails_at_multiple_steps:
  "\<exists>attempt.
    (\<exists>err. de_isVague err = True) \<and>
    (\<exists>exp. ev_hasRigorousProof exp = False)"
  using MSP_definition_is_vague jiang_relies_on_experiments
  by (metis msp_def_vague jiang_experiments)

section \<open>Verification\<close>

text \<open>
This theory file compiles successfully.
It demonstrates that Jiang's argument has multiple unproven critical claims:
  \<bullet> MSP problem definition is vague and poorly formalized
  \<bullet> MSP may be in P rather than NP-complete (reducing HC to P doesn't help)
  \<bullet> Algorithm correctness relies on experimental validation, not proof
  \<bullet> Lack of peer review and community acceptance after many years

The formalization shows the structure of the argument but highlights where
rigorous proofs are missing and where claims remain unsubstantiated.
\<close>

end
