# Original Paper

**Title**: The Asymmetric Traveling Salesman Problem

**Author**: Howard Kleiman

**Date**: December 2006 (Submitted: December 5, 2006; Last revised: December 9, 2006)

**arXiv ID**: math.CO/0612114

**Links**:
- Abstract: http://arxiv.org/abs/math.CO/0612114
- PDF: https://arxiv.org/pdf/math.CO/0612114

## Abstract

The paper proposes a polynomial-time algorithm for solving the Asymmetric Traveling Salesman Problem (ATSP). The approach:

1. Transforms an n×n asymmetric cost matrix M(a) into a 2n×2n symmetric cost matrix M(s)
2. Applies a modified Floyd-Warshall algorithm to M(s)
3. Claims to extract an optimal tour in M(a) from the result
4. States the algorithm runs in at most O(n⁴) time

The paper claims that if this is correct, it would prove P = NP, since ATSP is NP-hard.

## Note

The original PDF is available at the arXiv link above. This directory contains only reference information, not the full paper, to respect copyright.

## Related Papers by Kleiman

- "The Floyd-Warshall Algorithm, the AP and the TSP" (2001) - arXiv:math/0111309
- "The Symmetric Traveling Salesman Problem" (2005) - arXiv:math/0508212
- "The General Traveling Salesman Problem" (2011) - arXiv:1110.4052
