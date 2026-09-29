# Experiments and Proof Explorations

This directory contains research experiments and verification reports. They are not claimed proofs of P = NP or P ≠ NP.

The corrected [Williams experiment](../proofs/experiments/p_not_equal_np_proof_attempt.md) explains the algorithm-to-lower-bound implication and its open premises. Its paired [Lean](../proofs/experiments/WilliamsFramework.lean) and [Rocq](../proofs/experiments/WilliamsFramework.v) regression checks import the shared Idea 41 model. The original compile failure is reproduced by `experiments/issue614/test_framework.py`. The issue #10 target `NP ⊈ P` and the formal refutations of the enumeration and circularity arguments are in [proofs/experiments/issue10](../proofs/experiments/issue10/README.md). The issue #8 target `NP ⊆ P`, a verified DPLL solver with its cost bound, and the [corrected write-up](../proofs/experiments/np_subset_p_proof_attempt.md) that replaces PR #41's documents are in [proofs/experiments/issue8](../proofs/experiments/issue8/README.md).

Other experiments include [issue 28 verification](issue28_verification.md), [issue 31 verification](issue31_verification.md), and the [implementation plan](implementation_plan.md). See [proof experiments](../proofs/experiments/README.md) for the formal proof directory.
