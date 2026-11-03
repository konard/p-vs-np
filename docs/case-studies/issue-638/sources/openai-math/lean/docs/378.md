# The Exponential Time Hypothesis is False

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [The Exponential Time Hypothesis is False](../../preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf)

## Scope

For fixed $k\ge2$, Lean proves that a deterministic machine exactly counts satisfying assignments of a canonically encoded $k$-CNF on $n$ variables in time $(L+1)^{O_k(1)}2^{O_k(n(\log\log n)^2/\sqrt{\log n})}$, where $L$ is the encoding's bit length. At every step, the machine has visited at most $(L+1)^{O_k(1)}$ tape cells in total.

For $m$ clauses, the October 25 manuscript gives the sharper time bound $(n+m)^{O_k(1)}2^{O_k(n\log\log n/\sqrt{\log n})}$. When $m\le Dn$ for fixed $D>0$, this improves to $(n+m)^{O_{k,D}(1)}2^{O_{k,D}(n/\sqrt{\log n})}$.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Exact counting and SAT on canonical inputs in subexponential time and polynomial space | [SubexponentialSAT.lean](../ComparatorChallenges/SubexponentialSAT.lean) |
