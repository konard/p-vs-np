# Original Proof Description: Natalia L. Malinina (2012)

## Source Information

- **Author**: Natalia L. Malinina
- **Year**: 2012
- **Title**: "On the unprovability of the P ≠ NP conjecture"
- **Listed in**: Woeginger's P vs NP attempts list, Entry #95
- **Claim**: P vs NP is unprovable in ZFC

## Paper Availability

The original paper was listed by Woeginger but a stable public PDF/HTML version could not be retrieved at the time of formalization. The description below reconstructs the core argument based on the description in Woeginger's list and the context of similar "unprovability" attempts.

See [ORIGINAL.md](ORIGINAL.md) for the reconstructed description of the proof idea.

## Core Proof Idea

Malinina's 2012 paper argues that the P vs NP question is undecidable within ZFC, drawing on an analogy with Gödel's incompleteness theorems. The central strategy involves:

1. **Diagonalization Construction**: Building a self-referential algorithm whose existence would contradict provability of P ≠ NP
2. **Gödelian Transfer**: Applying Gödel's second incompleteness theorem to transfer undecidability of the halting problem to P vs NP
3. **Independence Conclusion**: Concluding that neither P = NP nor P ≠ NP can be proved from ZFC

The argument is in the tradition of attempts to show P vs NP is analogous to the Continuum Hypothesis — a natural mathematical question that is independent of the standard axioms of mathematics.
