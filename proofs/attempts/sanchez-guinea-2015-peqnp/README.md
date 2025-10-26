# Formalization: Sanchez Guinea (2015) - P=NP Claim

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Frameworks](../../../README.md#-formal-verification)

---

## Metadata

- **Attempt ID**: 103 (from Woeginger's list)
- **Author**: Alejandro Sanchez Guinea
- **Year**: 2015 (April)
- **Claim**: P = NP
- **Paper Title**: "Understanding SAT is in P"
- **arXiv**: [1504.00337](https://arxiv.org/abs/1504.00337)
- **Status**: **Refuted** (2017)

## Summary

In April 2015, Alejandro Sanchez Guinea submitted a paper claiming to prove P=NP by designing an algorithm that allegedly solves the Boolean satisfiability problem (SAT) in polynomial time. The paper introduces the concept of an "understanding" - a satisfying truth assignment explained through the contexts of literals in clauses.

### Main Argument

The author's approach attempts to solve 3-SAT through:

1. **Understanding Concept**: Introduces a notion of "understanding" a SAT formula, which represents a satisfying truth assignment explained through the contexts of literals appearing in clauses.

2. **Mechanical Process**: Proposes a mechanical process (algorithm) that claims to:
   - Determine a satisfying assignment for any 3-SAT instance
   - Detect when no satisfying assignment exists
   - Run in polynomial time

3. **Claimed Implication**: If successful, this would prove SAT ∈ P, which (since SAT is NP-complete) would imply P = NP.

### The Algorithm

The paper presents two main algorithms:
- **Algorithm D**: For determining truth assignments
- **Algorithm U**: For constructing "understandings"

The core claim is that these algorithms can solve 3-SAT instances by analyzing the "contexts of each literal in the instance" to find a solution efficiently.

## Known Refutation

**Refutation Paper**: "A Refutation of Guinea's 'Understanding SAT is in P'"
- **Authors**: Jackson Abascal and Seiven Maimon
- **Year**: 2017 (November)
- **arXiv**: [1711.04412](https://arxiv.org/abs/1711.04412)

### The Error

The refutation paper identifies fundamental flaws in Guinea's proposed algorithms:

1. **Algorithmic Flaw**: The algorithms (particularly Algorithm D and Algorithm U) do not correctly solve all instances of 3-SAT as claimed.

2. **Polynomial Time Claim Invalid**: Even if the algorithms were correct in principle, they do not run in guaranteed polynomial time for all instances.

3. **Gap in Proof**: The paper fails to rigorously prove that the "understanding" concept leads to a polynomial-time algorithm for all 3-SAT instances.

### Why This Matters

This attempt is instructive because:
- It demonstrates a common pattern in failed P=NP attempts: introducing new terminology or concepts without rigorous analysis
- The algorithm may work on some instances but fails to handle all cases
- The polynomial time analysis is incomplete or incorrect
- It shows the importance of formal verification in catching subtle errors in complexity arguments

## Formalization Structure

This directory contains formalizations in three proof assistants to identify and document the exact error:

### 1. Coq Formalization (`coq/`)

Located in `coq/SanchezGuinea2015.v`:
- Formalizes the key definitions from the paper
- Attempts to formalize the claimed algorithm
- Identifies where the formalization breaks down
- Documents the gap or error formally

### 2. Lean Formalization (`lean/`)

Located in `lean/SanchezGuinea2015.lean`:
- Uses Lean 4's dependent type system
- Provides constructive formalization where possible
- Highlights the non-constructive or invalid steps

### 3. Isabelle Formalization (`isabelle/`)

Located in `isabelle/SanchezGuinea2015.thy`:
- Uses Isabelle/HOL's higher-order logic
- Provides alternative formalization perspective
- Documents the error in the proof

## Key Insights from Formalization

Through formal verification, we can identify:

1. **Definitional Issues**: The concept of "understanding" may not be well-defined or may not have the properties claimed.

2. **Algorithmic Gaps**: The algorithms may not terminate in polynomial time, or may not correctly solve all instances.

3. **Logical Leaps**: There may be steps in the reasoning that appear plausible informally but cannot be formalized rigorously.

## Educational Value

This formalization serves multiple purposes:

1. **Historical Record**: Documents a notable P=NP attempt and its refutation
2. **Pattern Recognition**: Helps identify common errors in complexity arguments
3. **Formal Methods Training**: Demonstrates how proof assistants can catch subtle errors
4. **Research Methodology**: Shows the value of formal verification in theoretical computer science

## Verification

To verify the formalizations:

```bash
# Coq
cd coq
coqc SanchezGuinea2015.v

# Lean
cd lean
lake build

# Isabelle
cd isabelle
isabelle build -D .
```

## References

### Original Attempt
- Sanchez Guinea, A. (2015). "Understanding SAT is in P." arXiv:1504.00337
  https://arxiv.org/abs/1504.00337

### Refutation
- Abascal, J., & Maimon, S. (2017). "A Refutation of Guinea's 'Understanding SAT is in P'." arXiv:1711.04412
  https://arxiv.org/abs/1711.04412

### Context
- Woeginger's P-versus-NP page: https://www.win.tue.nl/~gwoegi/P-versus-NP.htm
- Cook, S. (1971). "The complexity of theorem-proving procedures." STOC
- Karp, R. (1972). "Reducibility among combinatorial problems."

## Related Work

- Other formalized P vs NP attempts in this repository
- [P = NP Framework](../../p_eq_np/) - General framework for P=NP proofs
- [P ≠ NP Framework](../../p_not_equal_np/) - General framework for P≠NP proofs

## License

This formalization is provided for educational and research purposes. See repository [LICENSE](../../../LICENSE) file.

## Status

- ✅ Folder structure created
- ✅ README.md with detailed description
- 🚧 Coq formalization (in progress)
- 🚧 Lean formalization (in progress)
- 🚧 Isabelle formalization (in progress)

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Issue #123](https://github.com/konard/p-vs-np/issues/123)
