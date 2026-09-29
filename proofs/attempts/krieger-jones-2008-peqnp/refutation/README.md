# Refutation Formalization

This folder contains formal refutations of specific claims in Krieger & Jones' 2008 attempt.

## What is Refuted

While we cannot directly refute the existence of a polynomial-time Hamiltonian circuit algorithm (that would require proving P≠NP), we can refute specific claims about the proposed approach:

1. **Patent ≠ Proof**: Patent grants do not constitute mathematical validation
2. **Insufficient Specification**: The algorithm description lacks the rigor needed for a proof
3. **Missing Correctness Proof**: No rigorous proof that the algorithm always gives correct answers
4. **Missing Complexity Proof**: No rigorous proof of polynomial time bounds
5. **Lack of Validation**: The claim has not been validated by the theoretical CS community

## Formalization Structure

The refutations formalize:

- The distinction between patent examination and peer review
- Requirements for a valid P=NP proof
- Identification of missing components in the Krieger-Jones attempt
- Common pitfalls in NP-complete algorithm claims

## Key Points

### Why This is Not a Valid Proof

A valid proof that P=NP via a Hamiltonian circuit algorithm requires:

1. **Complete Algorithm**: Unambiguous specification of all steps
2. **Correctness Proof**: Rigorous proof it always produces correct answers
3. **Complexity Proof**: Rigorous proof of polynomial time complexity
4. **Peer Validation**: Verification by the theoretical computer science community

The Krieger-Jones patent application provides none of these with the required rigor.

### Patent vs. Peer Review

Patent examination focuses on:
- Legal novelty and non-obviousness
- Industrial utility
- Enabling disclosure (not mathematical rigor)

Mathematical proof requires:
- Logical completeness
- Verifiable correctness
- Community consensus through peer review

## See Also

- `../proof/` - Forward formalization of the claimed argument
- `../original/` - The original patent application text
