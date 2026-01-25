# References for Lizhi Du's 2010 P=NP Attempt

## Primary Paper

**Du, Lizhi (2010). "A Polynomial time Algorithm for 3SAT"**
- arXiv ID: 1004.3702
- First version: April 12, 2010 (v1)
- Latest version: December 22, 2025 (v95)
- URL: https://arxiv.org/abs/1004.3702
- PDF: https://arxiv.org/pdf/1004.3702

### Abstract
The paper claims to solve the P vs NP problem by providing a polynomial-time algorithm for 3SAT. The approach introduces concepts including "checking trees, long unit paths, contradiction unit pairs, and 2-unit/3-unit layers" to transform 3SAT problems into 2SAT problems within polynomial time.

### Status
- 95 revisions over 15 years (2010-2025)
- Not accepted in peer-reviewed venues
- Contains fundamental algorithmic errors identified by critics

## Related Work by Du

**Du, Lizhi (2010). "A Polynomial Time Algorithm for Hamilton Cycle and Its Proof"**
- Presented at: International Conference on Computer Design and Applications (ICCDA 2010)
- Pages: 292-294
- Conference proceedings available via IAENG
- URL: https://www.iaeng.org/publication/IMECS2010/IMECS2010_pp292-294.pdf

Note: This appears to be a related but separate attempt focusing on the Hamiltonian cycle problem rather than 3SAT.

## Critique and Refutation

**He, Yumeng; et al. (2024). "A Critique of Du's 'A Polynomial-Time Algorithm for 3-SAT'"**
- arXiv ID: 2404.04395
- Submission date: April 2024
- URL: https://arxiv.org/abs/2404.04395
- HTML version: https://arxiv.org/html/2404.04395

### Key Findings
The critique identifies a critical flaw in Algorithm 1, Step 3 of Du's paper:
- **Flawed Section**: Step 3's intersection operation on useful units
- **Error**: The algorithm incorrectly eliminates valid solution paths
- **Counter-Example**: An infinite family of satisfiable 3-CNF formulas that Du's algorithm incorrectly classifies as unsatisfiable
- **Conclusion**: Du's algorithm produces false negatives and does not establish P = NP

### Authors
- Yumeng He
- (Additional authors listed in the paper)

## Woeginger's List

**Woeginger, Gerhard J. "The P-versus-NP page"**
- Entry: #60
- URL: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- Credit: Dirk Gerrits provided this reference to the list maintainer

### Entry Details
- Author: Lizhi Du
- Year: April 2010
- Claim: P=NP
- Paper: "A Polynomial Time Algorithm for Hamilton Cycle and Its Proof"
- Link: http://arxiv.org/abs/1004.3702

Note: The list entry mentions "Hamilton Cycle" in the title but links to the 3SAT paper (arXiv:1004.3702), suggesting Du may have worked on both problems.

## Background on 3SAT

**Cook, Stephen A. (1971). "The complexity of theorem-proving procedures"**
- Proceedings of the third annual ACM symposium on Theory of computing
- Pages: 151-158
- Proves 3SAT is NP-complete (Cook-Levin Theorem)

**Levin, Leonid (1973). "Universal sequential search problems"**
- Problems of Information Transmission, 9(3), 265-266
- Independent proof of NP-completeness

## Background on 2SAT

**Krom, Melven R. (1967). "The Decision Problem for a Class of First-Order Formulas in Which all Disjunctions are Binary"**
- Mathematical Logic Quarterly, 13(1-2), 15-20
- Early work on 2SAT decidability

**Even, Shimon; Itai, Alon; Shamir, Adi (1976). "On the complexity of time table and multi-commodity flow problems"**
- SIAM Journal on Computing, 5(4), 691-703
- Shows 2SAT is in P via graph-based algorithm

**Aspvall, Bengt; Plass, Michael F.; Tarjan, Robert E. (1979). "A linear-time algorithm for testing the truth of certain quantified boolean formulas"**
- Information Processing Letters, 8(3), 121-123
- Linear-time algorithm for 2SAT

## Relevance to P vs NP

The distinction between 2SAT (in P) and 3SAT (NP-complete) represents one of the sharpest complexity boundaries in computer science. Du's attempt tries to bridge this gap by reducing 3SAT to 2SAT in polynomial time, which would prove P=NP. However, the identified flaw in the reduction algorithm prevents this from succeeding.

## Access Information

### Available Online
- Du's original paper: freely available on arXiv
- He et al.'s critique: freely available on arXiv
- Woeginger's list: publicly accessible webpage

### Historical Context
- First version submitted: April 12, 2010
- Critique published: April 2024 (14 years later)
- Latest Du revision: December 22, 2025 (continuing revisions despite critique)

## See Also

- [Complexity Zoo - Class P](https://complexityzoo.net/Complexity_Zoo:P)
- [Complexity Zoo - Class NP](https://complexityzoo.net/Complexity_Zoo:N#np)
- [Wikipedia - P versus NP problem](https://en.wikipedia.org/wiki/P_versus_NP_problem)
- [Wikipedia - Boolean satisfiability problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem)
