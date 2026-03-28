# References for Sergey Gubin (2006) P=NP Attempt

## Original Paper

- **Gubin, S.** (2006). "A Polynomial Time Algorithm for The Traveling Salesman Problem"
  - arXiv: cs/0610042
  - URL: https://arxiv.org/abs/cs/0610042
  - PDF: https://arxiv.org/pdf/cs/0610042.pdf
  - Presented at: 22nd Mountain West Conference on Combinatorics, Combinatorial Computing and Combinatorics (2008)

## Refutation Papers

### LP Formulation Refutation

- **Hofman, P.** (2006). "Report on article: P=NP"
  - arXiv: cs/0610125
  - URL: https://arxiv.org/abs/cs/0610125
  - Content: Counter-examples showing non-integral extreme points in Gubin's LP formulation
  - Key Finding: The ATSP polytope as formulated by Gubin has fractional vertices

### SAT Solver Refutation

- **Christopher, I., Huo, D., & Jacobs, B.** (2008). "Critique of Gubin's SAT Solver"
  - arXiv: 0804.2699
  - URL: https://arxiv.org/abs/0804.2699
  - Content: Demonstrates exponential blowup in SAT to 2-SAT reduction
  - Key Finding: The proposed reduction is not polynomial-time

## Background References

### Woeginger's P vs NP List

- **Woeginger, G. J.** "The P-versus-NP page"
  - URL: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
  - Entry #33: Sergey Gubin (2006)

### Related Mathematical Background

- **Karmarkar, N.** (1984). "A new polynomial-time algorithm for linear programming"
  - Combinatorica, 4(4), 373-395
  - Establishes polynomial-time solvability of LP

- **Aspvall, B., Plass, M. F., & Tarjan, R. E.** (1979). "A linear-time algorithm for testing the truth of certain quantified boolean formulas"
  - Information Processing Letters, 8(3), 121-123
  - Establishes polynomial-time solvability of 2-SAT

- **Cook, S. A.** (1971). "The complexity of theorem-proving procedures"
  - Proceedings of the 3rd Annual ACM Symposium on Theory of Computing, 151-158
  - Establishes SAT as NP-complete

### TSP and LP Relaxations

- **Dantzig, G., Fulkerson, R., & Johnson, S.** (1954). "Solution of a large-scale traveling-salesman problem"
  - Operations Research, 2(4), 393-410
  - Classic LP approach to TSP

- **Padberg, M., & Rinaldi, G.** (1991). "A branch-and-cut algorithm for the resolution of large-scale symmetric traveling salesman problems"
  - SIAM Review, 33(1), 60-100
  - Modern LP-based approach showing polynomial LP cannot capture TSP exactly
