# The Complexity of HCP in Digraphs with Degree Bound Two

**Author**: Guohun Zhu  
**Institution**: Guilin University of Electronic Technology, No.1 Jinji Road, Guilin, Guangxi, 541004, P.R.China  
**Email**: ccghzhu@guet.edu.cn  
**arXiv**: [0704.0309v3 [cs.CC]](https://arxiv.org/abs/0704.0309v3)  
**Date**: 13 Jul 2007  

---

## Abstract

The Hamiltonian cycle problem (HCP) in digraphs D with degree bound two is solved by two mappings in this paper. The first bijection is between an incidence matrix C_{nm} of simple digraph and an incidence matrix F of balanced bipartite undirected graph G; The second mapping is from a perfect matching of G to a cycle of D. It proves that the complexity of HCP in D is polynomial, and finding a second non-isomorphism Hamiltonian cycle from a given Hamiltonian digraph with degree bound two is also polynomial. Lastly it deduces P = NP base on the results.

---

> **Note**: This is an English translation and markdown conversion of the original paper. The full original paper can be found in `ORIGINAL.pdf`.

---

The Complexity of HCP in Digraps with Degree
Bound Two

arXiv:0704.0309v3 [cs.CC] 13 Jul 2007

Guohun Zhu
Guilin University of Electronic Technology,
No.1 Jinji Road,Guilin, Guangxi, 541004,P.R.China
ccghzhu@guet.edu.cn

Abstract. The Hamiltonian cycle problem (HCP) in digraphs D with
degree bound two is solved by two mappings in this paper. The first
bijection is between an incidence matrix Cnm of simple digraph and an
incidence matrix F of balanced bipartite undirected graph G; The second mapping is from a perfect matching of G to a cycle of D. It proves
that the complexity of HCP in D is polynomial, and finding a second
non-isomorphism Hamiltonian cycle from a given Hamiltonian digraph
with degree bound two is also polynomial. Lastly it deduces P = N P
base on the results.

1

Introduction

It is well known that the Hamiltonian cycle problem(HCP) is one of the standard
NP-complete problem [1]. As for digraphs, even when the digraphs on this case:
planar digraphs with indegree 1 or 2 and outdegree 2 or 1 respectively, it is still
N P − Complete which is proved by J.Plesnı́k [2].
Let us named a simple strong connected digraphs with at most indegree 1 or
2 and outdegree 2 or 1 as Γ digraphs. This paper solves the HCP of Γ digraphs
with following main results.
Theorem
 +  1. Given an incidence matrix Cnm of Γ digraph, building a mapping:F =
C
, then F is a incidence matrix of undirected balanced bipartite graph
−C −
G(X, Y ; E), which obeys the following properties:
c1. |X| = n,|Y | = n,|E| = m
c2.
∀xi ∈ X ∧ 1 ≤ d(xi ) ≤ 2
∀yi ∈ Y ∧ 1 ≤ d(yi ) ≤ 2

c3. G has at most n4 components which is length of 4.
Let us named the undirected balanced bipartite graph G(X, Y : E) of Γ
digraph as projector graph.

Theorem 2. Let G be the projector graph of a Γ graph D(V, A), determining
a Hamiltonian cycle in Γ digraph is equivalent to find a perfect match M in
G and r(C ′ ) = n − 1, where C ′ is the incidence matrix of D′ (V, L) ⊆ D and
L = {ai |ai ∈ D ∧ ei ∈ M }.
Let the each component of G corresponding to a boolean variable, a monotonic function f (M ) is build to represents the number of component in D. Based
on this function, the maximum number of non-isomorphism perfect matching is
linear, thus complexity of Γ digraphs has a answer.
Theorem 3. Given the incidence matrix Cnm of a Γ digraph , the complexity
of finding a Hamiltonian cycle existing or not is O(n4 )
The concepts of cycle and rank of graph are given in section 2. Then theorems
1,2,3 are proved in sections 3,4,5 respectively. The last section discusses the P
versus N P in more detail.

2

Definition and properties

Throughout this paper we consider the finite simple (un)directed graph D =
(V, A) (G(V, E), respectively), i.e. the graph has no multi-arcs and no self loops.
Let n and m denote the number of vertices V and arcs A (edges E, respectively),
respectively.
As conventional, let |S| denote the number of a set S. The set of vertices V
and set of arcs of A of a digraph D(V, A) are denoted by V = {vi |1 ≤ i ≤ n}
and A = {aj |(1 ≤ j ≤ m) ∧ aj =< vi , vk >, (vi 6= vk ∈ V )} respectively,
where < vi , vk > is a arc from vi to vk . Let the out degree of vertex vi denoted
by d+ (vi ), which has the in degree by denoted as d− (vi ) and has the degree
d(vi ) which equals d+ (vi ) + d− (vi ). Let the N + (vi ) = {vj | < vi , vj >∈ A}, and
N − (vi ) = {vj | < vj , vi >∈ A}.
Let us define a forward relation ⊲⊳ between two arcs as following, ai ⊲⊳ aj =
vk iff ai =< vi , vk > ∧aj =< vk , vj >. It is obvious that |ai ⊲⊳ ai | = 0 .
A cycle L is a set of arcs (a1 , a2 , . . . , al ) in a digraph D, which obeys two
conditions:
c1. ∀ai S
∈ L, ∃aj , ak ∈ L \ {ai }, ai ⊲⊳ aj 6= aj ⊲⊳ ak ∈ V
ai ⊲⊳ aj | = |L|
c2. |
ai 6=aj ∈L

If a cycle L obeys the following conditions, it is a simple cycle.
c3. ∀L′ ⊂ L, L′ does not satisfy both conditions c1 and c2.
A Hamiltonian cycle L is also a simple cycle of length n = |V | ≥ 2 in digraph.
As for simplify, this paper given a sufficient condition of Hamiltonian cycle in
digraph.
Lemma 1. If a digraph D(V, A) include a sub graph D′ (V, L) with following
two properties, the D is a Hamiltonian graph.
2

c1. ∀vi ∈ D′ → d+ (vi ) = 1 ∧ d− (vi ) = 1,
c2. |L| = |V | ≥ 2 and D′ is a strong connected digraph.
A graph that has at least one Hamiltonian cycle is called a Hamiltonian
graph. A graph G=(V ; E) is bipartite if the vertex set V can be partitioned into
two sets X and Y (the bipartition) such that ∃ei ∈ E, xj ∈ X, ∀xk ∈ X \ {xj },
(ei ⊲⊳ xj 6= ∅ → ei ⊲⊳ xk = ∅) (ei , Y , respectively). if |X| = |Y |, We call that
G is a balanced bipartite graph. A matching M ⊆ E is a collection of edges
such that every vertex of V is incident to at most one edge of M , a matching of
balanced bipartite graph is perfect if |M | = |X|. Hopcroft
√and Karp shows that
constructs a perfect matching of bipartite in O((m + n) n) [3]. The matching
of bipartite has a relation with neighborhood of X.
Theorem 4. [4] A bipartite graph G = (X, Y ; E) has a matching from X into
Y if and only if |N (S)| ≥ S, for any S ⊆ X.
Lemma 2. A even length of simple cycle consist of two disjoin perfect matching.
Two matrices representation for graphs are defined as follows.
Definition 1. [5] The incidence matrix C of undirected graph G is a two dimensional n × m table, each row represents one vertex, each column represents
one edge, the cij in C are given by

1, if vi ∈ ej ;
cij =
(1)
0, otherwise.
It is obvious that every column of an incidence matrix has exactly two 1
entries.
Definition 2. [5] The incidence matrix C of directed graph D is a two dimensional n × m table, each row represents one vertex, each column represents one
arc the cij in C are given by

 1, if < vi , vi >⊲⊳ aj = vi ;
(2)
cij = −1, if aj ⊲⊳< vi , vi >= vi ;

0, otherwise.
It is obvious to obtain a corollary of the incidence matrix as following.

Corollary 1. Each column of an incidence matrix of digraph has exactly one 1
and one −1 entries.
Theorem 5. [5] The C is the incidence matrix of a directed graph with k components the rank of C is given by
r(C) = n − k

(3)

In order to convince to describe the graph D properties, in this paper, we
denotes the r(D) = r(C).
3

3

Divided incidence matrix and Projector incidence
matrix

Firstly, let us divided the matrix of C into two groups.
C + = {cij |cij ≥ 0 otherwise 0 }

(4)

C − = {cij |cij ≤ 0 otherwise 0 }

(5)

It is obvious that the matrix of C + represents the forward arc of a digraph
and C − matrix represents the backward arc respectively. A corollary is deduced
as following.
Corollary 2. A digraph D = (V, A) is strong connected if and only if the rank
of divided incidence matrix satisfies r(C + ) = r(C − ) = |V |.
Secondly, let us combined the the C + and C − as following matrix.
 + 
C
F =
−C −

(6)

In more additional, let F represents as an incidence matrix of undirected
graph G(X, Y ; E). The F is named as projector incidence matrix of C and
G is named as projector graph , where X represents the vertices V + of D, Y
represents the vertices of V − respectively. In another words we build a mapping
F : D → G and denotes it as G = F (D). So the F (D) has 2n vertices and
m edges if D has n vertices and m arcs. We also build up a reverse mapping:
F −1 : G → D When G is a projector graph. To simplify, we also denotes the
arcs ai = F −1 (ei ), vi+ = F −1 (xi ) and vi− = F −1 (yi ).
3.1

Proof of Theorem 1

Firstly, let us prove the theorem 1.
Proof. c1. Since Γ digraph is strong connected, then each vertices of Γ digraph
has at least one forward arcs, each row of C + has at least one 1 entries, and
the U represents the C + , so
|U | = n
the same principle of C − , each row of C − has at least one −1 entries, and
the V represents the C − , so
|V | = n
Since the columns of F equal to the columns of C,
|E| = m
4

c2. Since the degree of each vi of Γ digraph is 1 ≤ d+ (vi ) ≤ 2,
∀ui ∈ U ∧ 1 ≤ d(ui ) ≤ 2

Since the degree of each vi of Γ digraph is 1 ≤ d− (vi ) ≤ 2,
∀vi ∈ V ∧ 1 ≤ d(vi ) ≤ 2

c3. Let us prove by contradiction, suppose there are k > n4 components with
length of 4 in G. Since D is strong connected, according to the corollary 2,
+
r(F ) = 3n
2 − q ≥ r(C ) = n, where q ≥ k is number of components (including k components with length of 4). Thus q ≤ n2 , then there are only x
components without length 4, where x is
n
x=q−k <
(7)
4
Suppose the remind x components with length of t (at least t vertices con3n
n
nected by some edges), then 4k + xt = 3n
2 . So tx = 2 − 4k < 2 . According
to the equation 7, the t < 2. It is contradict that the D is strong connected.
3.2

The cycle in digraph corresponding matching in projector graph

Secondly, let us given the properties after mapping Hamiltonian cycle L of D
into the sub graph M of projector graph G.
Lemma 3. If a Hamiltonian cycle L of D mapping into a forest M of projector
graph G, the forest M consist of |L| number of trees which has only two node
and one edge, and M has a unique perfect matching.
Proof. Let the Γ digraph D(V, A) has a sub digraph D′ (V, L) which exists one
Hamiltonian cycle and |L| = n, the incidence matrix C of L could be permutation
as follows.


1 0 0 . . . 0 −1
 −1 1 0 . . . 0 0 


 0 −1 1 . . . 0 0 

.
C=
(8)

 0 0 −1 . . . 0 0 
0 0 0 ... 0 0 
0 0 0 . . . −1 1
Let
 + 
C
F =
−C −

It is obvious that each row of F has only one 1 entry and each column of F
has two 1 entries.
According to theorem 1, F represents a balanced bipartite graph G(X, Y ; E)
that each vertex has one edge connected, and each edge ei connect on vertex
xi ∈ X , another in Y , in another words, ∃ei ∈ E xj ∈ X,∀xk ∈ X \ {xj }, ei ⊲⊳
xj 6= ∅ → ei ⊲⊳ xk = ∅(ei , Y ,respectively). According the matching definition,
M is a matching, since |E| = |L|, E is a perfect matching. and pair of vertices
between X and Y only has one edge, so M is a forest, and each tree has only
two node with one edge.
5

4

Proof of Theorem 2

Proof. ⇒ Let the Γ digraph D(V, A) has a sub digraph D′ (V, L) which is a
Hamiltonian cycle and |L| = n, let matrix C ′ represents the incidence matrix of
D′ , so r(C ′ ) = n − 1; According to lemma 3, the projector graph F (D′ ) has a
perfect matching, thus F (D) also has a perfect matching.
⇐ Let G(X, Y ; E) be a projector graph of the Γ graph D(V, A),M is a perfect
matching in G. Let D′ (V, L) be a sub graph of D(V, A) and L = {ai |ai ∈ D ∧ei ∈
M }. Since r(L) = n − 1, D′ (V, L) is a strong connected digraph. it deduces that
′
+
−
∀vi ∈ D′ ,d+ (vi ) ≥ 1 ∧ d− (vi ) ≥ 1. Suppose ∃v
Pin∈ D , d (vi ) > 1 (d (vi ) > 1
respectively), Since |M | = n, it deduces that i=1 d(vi ) > 2n + 1, which imply
that |L| > n. this is contradiction with L = {ai |ai ∈ D ∧ ei ∈ M } and |M | = n.
So ∀vi ∈ D′ , d+ (vi ) = d− (vi ) = 1, According the lemma 1, D′ has a Hamiltonian
cycle.

5

Number of perfect matching in projector graph

Let us considering the number of perfect matching in G . Firstly, let us considering a example as shown in figure 1.

a3 ♠a✲
a5 ♠a✲
a7 ♠
1 ♠a
2 ♠✲
4 ♠✲
6 ♠✲
✲
♠a✲

✻a8
✻
✻
✻a14
a
a10
a19
a
a
a
❄9
❄11
❄13
❄ 15
♠
✛ ♠
✛ ♠
✛ ♠
✛ ♠
✛ ♠
✛ ♠
✛ ♠
a21
a12
a17
a22
a20
a18
a16
Figure 1. Original Digraph D
Then the projector graph is shown in figure 2.
♠♠♠

♠ ♠♠ ♠ ♠ ♠ ♠♠ ♠ ♠
❆ e2 ✁
❆ e4 ✁
❆ e13 ✁
❆ ✁
❆ ✁
❆ ✁
...
e9 ❆ ✁e21
e11 ❆ ✁e12
e6 ❆ ✁e17
✁❆
✁❆
✁❆
e1 e8 e22
✁ ❆ e10 e3 e20 ✁ ❆ e19 e5 e18 ✁ ❆ e14
♠♠♠ ♠
✁
❆♠ ♠ ♠ ♠
✁
❆♠ ♠ ♠ ♠
✁
❆♠
G1
G2
G3
Figure 2. Projector graph G
Given a perfect matching M , each component(cycle) in G has two partition
edges belong to M . Let us code component Gi which |Gi | > 2 and matching M
to a binary variable.

1, if Gi ∩ M = {ej , ek , . . .};
Gi =
(9)
0, if Gi ∩ M = {el , eq , . . .}.
6

Now there are two cases for the number of perfect matching.
Label edge. In that cases, the Code(M1 ) = {0, 0, 1} is different with Code(M2 ) = {0, 1, 0}.
If there are k number of components(cycles), then there are 2k perfect matching.
Unlabel edge. In that cases, the Code(M1 ) = {0, 0, 1} is isomorphic to Code(M2 ) = {0, 1, 0}.
The same principle that Code(M3 ) = {0, 1, 1} is isomorphic to Code(M4 ) =
{1, 1, 0} but is not isomorphic to Code(M1 ).
Then let us summary the maximal number of perfect matching in these two
cases.
Lemma 4. The maximal number of labeled perfect matching in a projector graph
n
G is 2 4 , but the maximal number of unlabeled perfect matching in a projector
graph G is n2 .
Proof. According to the theorem 1, there at most n4 components with a components which is length of k = 4. When k=2, there are only one perfect matching
in G; When k = 4, there are n4 components which is C4 , and so on when k = 6,
there are n6 components which is C6 , etc, so on. According to the lemma 2, each
simple cycle has divided the perfect matching into two class. So maximal number
n
perfect matching in the non isomorphism cycle which is 2 4 . Since in unlabeled
cases, every C4 cycle is isomorphism, the maximal number of perfect matching
is 2 ∗ n4 = n2 .
Review the example 1 again, it is easy find that follow proposition.
Proposition 1. Given two perfect matching M 1 and M 2 in projector graph G,
if code(M 1) = code(M 2), then the r(F −1 (M 1)) = r(F −1 (M 2)).
5.1

Proof of Theorem 3

Now let us proof the theorem 3.
Proof. Let G be a project balanced bipartition of D. According theorem 1, the
Γ graph is equivalent to find a perfect match M in a project G.
According to the lemma 4, the maximal number non isomorphism perfect
matching in G is only n.
Thus it is only need exactly enumerate all of non isomorphism perfect matching M , then obtain the value = r(F −1 (M )),if value = n − 1, then the ei ∈ M
is also ei ∈ C, where C ⊂ D is a Hamiltonian cycle.
Since the complexity of rank of matrix is O(n3 ), finding a simple cycle in
a component with degree 2 √
is O(n2 ), and obtaining a perfect matching of a
bipartite graph is O((m + n) n) < O(n2 ) [3]. Then all exactly algorithms need
to calculate the n time o(n3 ). Thus the complexity is O(n4 ).
Since the non isomorphism perfect matching comes from the coding of edges
in the component of G, it is not easy implementation.
7

Let us give two recursive equation to obtain a perfect matching M from G.
Suppose there are k component G1 , G2 , . . . Gk in G where Gi is a component
with degree 2 and |Ei | ≥ 3.
M′ =

M (t + 1) =





M (t) ⊗ Gt , Gt is a cycle ;
M (t),
otherwise.

M ′ , if r(F −1 (M ′ )) > r(F −1 (M (t))) ;
M (t), otherwise.

(10)

(11)

where t ≤ k − 1, when t = 0, M (0) is the initial perfect matching from G.
When r(F −1 (M (t))) = n − 1, According the theorem 1, the A = F −1 (M (t))
is a Hamiltonian cycle solution. If all of r(F −1 (M (t))) < n − 1, then there has
no Hamiltonian cycle in D.
Since the non isomorphism perfect matching M in G is poset, the function
r(F −1 (M )) in G is monotonic, so this approach is exactly approach.
Let us give a example to illustrate the approach in detail.
Example 1. Considering the digraph D in figure 1, then the projector graph G
in figure 2.
Let M (0) = {e1 , e8 , e22 , e9 , e10 , e3 , e20 , e11 , e19 , e5 , e18 , e6 , e17 , e7 , e15 , e16 }.
Thus the r(F −1 (M (0)) = n−3. Let M ′ = r(F −1 (M (0)⊗G3 ),then r(F −1 (M ′ ) =
n − 4, thus M (1) = M (0) and then turn to G2 ,G1 . At last it obtain the solution.
Considering the equation 11, let it substituted by following equations when
r(M ′ ) = n − 1 and t < k − 1.
M (t + 1) = M ′ if r(F −1 (M ′ )) ≥ r(F −1 (M (t)))

(12)

It is obvious that all non-isomorphism Hamiltonian cycle could obtain by the
repeat check the equation 12 and the equation r(M ′ ) = n − 1.
In conversely, if a Hamiltonian cycle of Γ digraphs is given, it represents a
perfect matching M in its projector graph G. Thus the equation 12 and Theorem 3 follows a corollary.
Corollary 3. Given a Hamiltonian Γ digraph, the complexity of determining
another non-isomorphism Hamiltonian cycle is polynomial time.
5.2

The HCP in digraph with bound two

Let us extend the Theorem 3 to digraphs with d+ (v) ≤ 2 and d− (v) ≤ 2 in this
section.
Theorem 6. The complexity of finding a Hamiltonian cycle existing or not in
digraphs with degree d+ (v) ≤ 2 and d− (v) ≤ 2 is polynomial time.
8

Proof. Suppose a digraph D(V, A) having a vertex vi is shown as figure 3, which
is d( vi ) = 2 ∧ d− (vi ) = 2
a2
❍❍
a4 ✟
✯
✟
✟
❍❍
✟
✟
❍
❥ ♠
❍
✟
✯ ❍❍
✟
✟
❍
a1 ✟✟
❍
✟
❥
❍
a3 ❍
✟
Figure 3. A vertex with degree than 2
Let us spilt this vertex to two vertices that one of vertex has degree with
in degree 2 or out degree 1 , another vertex has degree with in degree 1 or out
degree 2 as shown in figure 4. Then the D is derived to a new Γ graph S.

a2

✲ ❤
✯
✟
✟
a1 ✟✟
✟✟

a4 ✟
✯
✟
✟✟
✲❤✟✟
✲
a3

Figrue 4 A vertex in D is mapping to a vertex in Γ digraph
It is obvious that each vertex in the Γ graph S has increase 1 vertices and 1
arcs of D. Suppose the worst cases is each vertex in D has in degree 2 and out
degree 2, the total vertices in S has 2n vertices.
According to the theorem 3, obtain a Hailtonian cycle L′ in S is no more
then O(n4 ), then the D will has a Hamiltonian cycle L′ = L ∩ A.

6

Discussion P versus NP

The P versus N P is a famous open problem in computer science and mathematics, which means to determine whether very language accepted by some
nondeterministic algorithm in polynomial time is also accepted by some deterministic algorithm in polynomial time [6]. Cook give a proposition for the P
versus N P .
Proposition 2. If L is NP-complete and L ∈ P , then P = N P .
According above proposition and the result above section, P versus N P
problem has a answer.
Theorem 7. P = N P
9

Proof. As the result of [2], the complexity of HCP in digraph with bound two
is N P − complete. According the theorem 6, the complexity of HCP in digraph
with bound two is also P , thus according to proposition 2, P = N P .
In fact, the [2] proves that 3SAT p HCP of Γ digraph, since 3SAT is a
N P C problem, which also implies that P = N P .

7

Conclusion

According to the theorem 6, the complexity of determining a Hamiltonian cycle
existence or not in digraph with bound degree two is in polynomial time. And
according to the theorem 7, P versus N P problem has closed, P = N P .

Acknowledgements
The author would like to thank Prof. Kaoru Hirota for valuable suggestions,
thank Prof. Jørgen Bang-Jensen who called mine attention to the paper [2], and
thank Andrea Moro for useful discussions.

References
1. Papadimitriou, C. H. Computational complexity , in Lawler, E. L., J. K. Lenstra, A.
H. G. Rinnooy Kan, and D. B. Shmoys, eds., The Traveling Salesman Problem: A
Guided Tour of Combinatorial Optimization. Wiley, Chichester, UK. (1985), 37–85
2. J.Plesnı́k,The NP-Completeness of the Hamiltonian Cycle Problem in Planar digraphs with degree bound two, Journal Information Processing Letters, Vol.8(1978),
199–201
3. J.E. Hopcroft and R.M. Karp , An n5/2 Algorithm for Maximum Matchings in
Bipartite Graphs . SIAM J. Comput. Vol.2, (1973), 225–231
4. P. Hall, On representative of subsets, J. London Math. Soc. 10, (1935), 26–30
5. Pearl, M, Matrix Theory and Finite Mathematics,McGraw-Hill, New York,(1973),
332–404.
6. Stephen Cook. The P Versus NP Problem ,”http://citeseer.ist.psu.edu/302888.html”
,2000.

10

