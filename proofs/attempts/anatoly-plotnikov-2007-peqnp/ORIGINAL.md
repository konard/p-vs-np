# Original Paper: Experimental Algorithm for the Maximum Independent Set Problem

**Author**: Anatoly D. Plotnikov  
**Institution**: State Scientific Research Institute for Information Infrastructure, National Academy of Sciences of Ukraine, Kiev, Ukraine  
**Published**: arXiv:0706.3565 [cs.DS], June 25, 2007  
**Later Published**: Cybernetics and Systems Analysis, Vol. 48, Issue 5 (2012), pp. 673-680  
**DOI**: 10.1007/s10559-012-9447-3

---

## Abstract

A polynomial experimental algorithm is proposed for finding a maximum independent set in a graph.

---

arXiv:0706.3565v2 [cs.DS] 2 Jul 2007

Experimental Algorithm for the Maximum
Independent Set Problem
Anatoly D. Plotnikov∗

Abstract
We develop an experimental algorithm for the exact solving of the
maximum independent set problem. The algorithm consecutively finds
the maximal independent sets of vertices in an arbitrary undirected graph
such that the next such set contains more elements than the preceding one.
For this purpose, we use a technique, developed by Ford and Fulkerson for
the finite partially ordered sets, in particular, their method for partition
of a poset into the minimum number of chains with finding the maximum
antichain. In the process of solving, a special digraph is constructed, and
a conjecture is formulated concerning properties of such digraph. This
allows to offer of the solution algorithm. Its theoretical estimation of
running time equals to is O(n8 ), where n is the number of graph vertices.
The offered algorithm was tested by a program on random graphs. The
testing the confirms correctness of the algorithm.

MSC 2000: 05C85, 68Q17.
KEYWORDS: the maximum independent set, a clique, NP-hard, NPcomplete, the class NP, a polynomial-time algorithm, the partially ordered set.

1

Introduction

A set of all undirected n-vertex graphs without loops and multiple edges is
denoted by Ln .
Let there be a graph G = (V, Γ) ∈ Ln , where V is the set of graph vertices,
and Γ is a mapping from V to V . Any subgraph Q1 = (V1 , Γ1 ) of G is called a
clique induced by V1 , if
Γ1 (v) = V1 \ {v}
for all v ∈ V1 . In a special case, when Card(V1 ) = 1, the one-vertex subgraph
Q1 = (V1 , Γ1 ) is called a single-vertex clique.
A clique Q1 is called maximal if any vertex v ∈ V cannot be attached to it
so that the new vertex set also has formed a clique of the graph G. A clique Q̂
is called maximum if the graph G has not a clique of the greater size than Q̂.
∗ E-mail address: akplokt(at)kvnk.ua

(remove k’s)

1

It be required to find the maximum clique of a graph G ∈ Ln . The known
problem of finding the maximum clique has formulated [3].
A vertex set U ⊆ V of G is called independent if
U ∩ Γ(U ) = ⊘.
An independent set U of graph vertices is called maximal (MIS) if
U ∪ Γ(U ) = V.
A MIS Ũ is called maximum (MMIS) if Card(Ũ ) ≥ Card(U ) for any MIS
U of G.
It be required to find the MMIS of a graph G. Again, we have formulated
well-know the maximum independent set problem (MISP).
Both of the formulated above problems are NP-complete [3, 1]. They are
closely connected with each other: the solution of one of them attracts the
solution another.
A graph Ḡ is called complement to the graph G if it has the same vertex set,
and edges join two vertices of the graph Ḡ iff these vertices are non-adjacent in
G.
It is not difficult to see that any clique of G corresponds to the independent
set of graph vertices in Ḡ, and conversely. Therefore, the finding the maximum
independent set in one graph is equivalent to the finding the maximum clique in
its complement graph. In the given work, we examine the maximum independent
set problem.
The intention of the given paper is to design a polynomial-time algorithm
for the exact solving of the maximum independent set problem in an arbitrary
undirected graph. For this purpose, we use a technique, developed by Ford
and Fulkerson (see [2] and Appendix A) for the finite partially ordered sets, in
particular, their method of partition poset into the minimum number of chains
with finding the maximum antichain. In the process of the solving, a special
digraph is constructed, and a conjecture is formulated concerning properties
such digraph. This allows to offer a solution algorithm, a theoretical estimation
of running time for which equals to is O(n8 ), where n is the number of graph
vertices. The offered algorithm was tested by a program. The testing confirms
the correctness of the algorithm.
Notice that the author did not aspire to creation of the most optimum and
fast algorithm. In work [8], Tarjan has presented a table, which shows a dynamics of perfecting a complexity evaluation for solving some problems. Whence
one can make a conclusion that after the appearance of an initial algorithm for
solving certain problem, its improvement is found quickly. It is presented that
proposed algorithm also can be improved hereinafter.

2

2

The Basic Definitions

Let there is a graph G = (V, Γ) ∈ Ln . We will partition the vertex set V into
subsets
V 0, V 1, . . . , V m
(1)
in such a way that a subset V k (k = 0, 1, . . . , m) is a MIS of a subgraph Gk
= (V \ (V 0 ∪ V 1 ∪ · · · ∪ V k−1 ), Γk ) = (V k ∪ · · · ∪ V m , Γk ). Clearly, G0 =
(V 0 ∪ · · · ∪ V m , Γ0 ) = G.
By the given undirected graph G and the partition (1) we can construct a
~ 0 ) = (V, ~Γ) in the following way. If an edge of G joins a vertex
digraph G(V
k1
vi ∈ V with a vertex vj ∈ V k2 then this edge is replaced by an arc (vi , vj )
when k1 < k2 . The vertex vi is called the tail of (vi , vj ), and the vertex vj is
called the head of this arc.
~ 0 ) = (V, ~Γ). The set V 0 is
As the result we have an acyclic digraph G(V
called initiating.
In general case we can construct a set D(G) of different acyclic digraphs as it
was indicated above. Each digraph of D(G) corresponds to the graph G ∈ Ln .
Further we will consider only digraphs of D(G).
The maximum length ρ(v) of a directed path, connecting a vertex v ∈ V
with some vertex of the initiating set V 0 , is called the rank of v. The set of all
~ 0)
graph vertices having the same rank ρ(v) = k is called the k-th layer of G(V
k
and designated as V .
~ 0 ) is assigned
To apply the partially ordered set technique, each digraph G(V
~ t (V 0 ) = (V, ~Γt ) [7, 9]. As the digraph
to a transitive closure graph (TCG) G
0
~
~ t (V 0 ) is a graph of a strict
G(V ) is acyclic and loopless, its transitive closure G
partial order (V, >). Further, we will not distinguish the transitive closure graph
~ t (V 0 ) and partially ordered set (poset) (V, >). Therefore, we will consider, for
G
~ t (V 0 ).
example, antichains of the TCG G
There exists an efficient algorithm to construct the TCG. Its running time
is equal to O(n3 ) (see, for example, [7, 6]).
~ t (V 0 ) will be called essential if there exists the arc (vi , vj )
An arc (vi , vj ) of G
0
~
of the digraph G(V ). Otherwise, the arc (vi , vj ) will be called fictitious. An
essential arc is also designated as vi > vj , and a fictitious arc is also designated as
~ t (V 0 ) determines two independent
vi ≫ vj . Obviously that any fictitious arc of G
~ 0 ).
vertices of the digraph G(V
Let there is a poset (A, ≥).
If a ≥ b or b ≥ a, the elements a and b of A are called comparable. If a 6≥ b
and b 6≥ a, such pair of elements is called incomparable.
If A1 ⊆ A and each pair of elements of A1 is comparable, we shall say that
A1 determines a chain of (A, ≥). If A1 ⊆ A and each pair of elements of A1 is
incomparable, we shall say that A1 be an antichain of (A, ≥). The antichain A1
is the maximum in (A, ≥), if Card(A1 ) ≥ Card(A∗ ) for any antichain A∗ ⊆ A
in (A, ≥).

3

We say that poset (A, ≥) is partitioned into chains A1 , . . . , Ap , if each Ai
(Ai 6= ⊘, i = 1, p) be a chain,
p
[

Ai = A,

i=1

and Ai ∩ Aj = ⊘, when i 6= j (i, j ∈ {1, . . . , p}).
The partition of the poset (A, ≥) into chains is called minimum, if it has the
minimum number of elements p in comparison with other partitions of (A, ≥)
into chains. Such partition also is called minimum chain partition (MCP) of
poset (A, ≥).
~ t (V 0 ) is a graph of strict partial order, we can find MCP P = {S1 , . . . , Sp }.
As G
In common case, this partition is ambiguous.
v5
v6
✈
✈
❏ v3 v4 ✡
✡
❏
❏✈ ✡
✈
✡
❏
✄❏
❏ ✡
✡❈
✡
❏
✡ ❈
✄ ❏
❏ ❈
✡ ❏
✄ ✡
❏❈
✡
❏
✄✡
✡
❏
✡
❏
✄✈
✡
❏❈✈
✡
❏
v1
v2
(a)

v5
v6
✈
✈
❏ v3 v4 ✡
✡
❏
❏
✡
✈
❏✈ ✡
❏
✡
❏
✡
✄✄✄❏ ✡ ❈❈❈
✡ ❈❈
✄✄ ❏
✄✄ ✡ ❏ ❈❈
❏ ❈❈
✄✄ ✡
❏❏❈❈✈
✄✡
✈
✄✡
v1
v2
(b)

Figure 1: Different MCPs of the transitive closure graph
Different MCPs of the transitive closure graph is shown on the Fig. 1 (a)
and (b). The digraph arcs, belonging chains of MCP, are represented by thick
lines. Here and hereinafter, we suppose that orientation of arcs of the digraph
is from below to upwards.
Let V (Sq ) (q = 1, p) be the set of vertices, belonging to the chain Sq . If
vertices vi , vj ∈ V (Sq ) are endpoints for a fictitious arc vi ≫ vj then the vertex
~ t (V 0 ) is determined
vj is called marked. The set of all marked vertices of G
by the found MCP P and it differs for different MCPs. The set of all marked
~ t (V 0 ) is designated as B(P).
vertices of G
For example, for the MCP P1 represented in Fig. 1 (a), we have B(P1 ) =
{v5 , v6 }, and for the MCP P2 represented in Fig. 1 (b), we have B(P2 ) = ⊘.
~ 0 ) be a digraph, and G
~ t (V 0 ) be its transitive closure graph.
Lemma 1 Let G(V
~
If B(P) = ⊘, where P is an MCP of Gt (V 0 ), then the maximum antichain U is
the MMIS of the graph G ∈ Ln , and the MCP determines the minimum clique
partition of G.
If conditions of Lemma 1 are satisfied then each chain Sq ∈ P is a clique of
~
G(V 0 ). Therefore, the MCP P is the minimum clique partition.
4

~ t (V 0 ) belong
On the other hand, vertices of the maximum antichain U of G
to distinct cliques, that is, the number of vertices in the MMIS is equal to the
number of vertices in the set U.
Q.E.D.
~ 0 ) has no transitive
Notice that Lemma 1 may be satisfied if the digraph G(V
orientation.
~ t (V 0 ) determines an independent
It is obvious that any antichain U ⊂ V of G
0
~
~ 0)
vertex set of the digraph G(V
), and an independent vertex set U ⊂ V of G(V
~ t (V 0 ) if and only if no two vertices of U belong to
determines an antichain of G
~
the same directed chain of G(V 0 ).

3

A vertex-saturated digraph

~ 0 ) = (V, ~Γ).
Let there is an acyclic digraph G(V
~ 0)
Further, let W ⊂ V be some independent vertex set. For the digraph G(V
~ 0 )). This operation consists of
we define an unary operation cutting σW (G(V
0
~
reorientation of all arcs of G(V ) incoming into vertices of the set W . It is easy
~ 0 ), where
to see that the result of this operation is also a digraph G(Y
Y 0 = (V 0 \ ~Γ−1 (W )) ∪ W.
Here, ~Γ−1 is a maping, inverse to ~Γ.
~ 0 ) ∈ D(G) and W be some independent
Theorem 1 Let there be a digraph G(V
~ 0 ) = σW (G(V
~ 0 )) is also acyclic and G(Y
~ 0) ∈
vertex set. Then a digraph G(Y
D(G).
~ 0 ) = (V, ~Γ) is acyclic then any its part is also
Indeed, since the digraph G(V
~ 1 = (V \ W, ~Γ1 ) is acyclic.
an acyclic digraph. Thus, a directed subgraph G
0
~
~
Obviously, G1 ⊂ G(Y ). Attach the independent vertex set W to the sub~ 1 . Join each vertex x ∈ W with a vertex y of G
~ 1 by the arc (x, y) if and
graph G
~ 0 ). It is evident that the
only if there exists the arc (y, x) of the digraph G(V
~ 0 ) is also acyclic.
resulting digraph G(Y
~ 0 ) ∈ D(G) since any reorientation of arcs of the digraph
At last, we have G(Y
0
~
G(V
) does not change independence relation of its vertices.
Q.E.D.
~ 0 ) and its transitive closure graph G
~ t (V 0 ).
Let there be a digraph G(V
0
~
We can find the MCP P of the graph Gt (V ) constructing the maximum
antichain U simultaneously as it is described in Appendix A.
In general case we can find some distinct maximum antichains.
We will say that an antichain U1 precedes an antichain U2 in the graph
~ t (V 0 ) and designate it as U1 ≺ U2 if for all vertices x ∈ U1 \ U2 there is a
G
vertex y ∈ U2 \ U1 such that x ≤ y.

5

By means of Ford and Fulkerson’s methodology such a maximum antichain
~ t (V 0 ) can be found that precedes any other maximum antichain
U of the TCG G
~ t (V 0 ). This antichain of the
U1 , i.e. U1 ≺ U for any antichain U1 of the TCG G
0
~
graph Gt (V ) we will call general.
In addition to the general antichain, we may find other maximum antichains
~ t (V 0 ) if they exist. So for any vertex v ∈ V of the TCG G
~ t (V 0 ), it is possible
of G
to find a maximum antichain U(v) such that v ∈ U(v). Technically, to find the
~ t (V 0 ) containing the
antichain U(v), it is sufficient, in the adjacent matrix of G
maximum number of units in allowable cells (and the marks are appointed by
the Ford-Fulkerson’s algorithm), to add the mark (∗) to the existing marks for
a row, corresponding to vertex v, and to execute a cycle of appointment of
marks. In this case, in the first step of appointment of marks, all columns are
marked, which contain the admissible cells (incluging a chosen cell). Clearly,
the antchain U(v) will be general for the vertex v, that is, any other antichain,
containing vertex v, will precede this antichain.
a2

a3
①
①
✁✁
✡❆❆
✡ ❆❆ ✁✁
✡
❆❆✁✁
a5 ①
✁✁❆❆
❏
❏ ✁✁ ❆❆
✁①
❏✁
❆❆①
✁
a1
a4

Figure 2: The partially ordered set
Notice that in general case it is not true that for any vertex v ∈ V of the
~ t (V 0 ) there exists a maximum antichain U(v). For example, consider
TCG G
the digraph of the partially ordered set, shown in Fig. 2. It is easy to see that
there are no maximum antichains U(a1 ) and U(a2 ) in it.
~ k ) (k = 0, m − 1) of the digraph G(V
~ 0 ) we will
A directed subgraph G(V
k
call saturated with respect to the initiating set V , if, in its transitive closure
~ t (V k ), any maximum antichain U(v) ⊂ V , when it exists, is a MIS of the
graph G
~ k ) and satisfies the relation: Card(U(v)) = Card(V k ). Evidently,
subgraph G(V
~ m ) has no arcs, and therefore it is saturated with respect to
the subgraph G(V
its initiating set always.
~ 0 ) is called vertex-saturated (VS-digraph) if any of its directed
A digraph G(V
~
subgraphs G(V k ) (k = 0, m), induced by the layer V k , is saturated with respect
to the initiating set V k .
Notice that digraph, represented in Fig. 1, is not vertex-saturated.
~ 0 ). To construct a VS-digraph, we use the
Let there be some digraph G(V
following algorithm.
The algorithm VS.

6

Step 1. Put k := 0 and α := false.
~ t (V k ).
Step 2. Find the transitive closure graph G
~ t (V k ).
Step 3. Construct an MCP of G
~ t (V k ) for each vertex v ∈ V k ∪ · · · ∪
Step 4. Find the maximum antichain of G
m
V .
Step 5. Check whether each of the found maximum antichains U(v) of the graph
~ t (V k ) is a MIS of the digraph G(V
~ k ) and Card(U(v)) = Card(V k ). If
G
~ k ) saturated with respect
it is true, finish the design of the digraph G(V
k
to the initiating set V . Go to Step 6.
Otherwise complete the found antichain U(v) (when it is necessary) to
~ k ) by
a MIS, put W := U(v) and construct a new acyclic digraph G(V
0
~
the cutting operation σW (G(V
)), put α := true and construct the new
0
~
digraph G(V ). Return to Step 2.
Step 6. Compute k := k + 1. If k < m then distinguish the transitive closure
~ t (V k ) from G
~ t (V k−1 ), keeping all chains of the MCP of G
~ t (V k−1 )
graph G
which are incident to vertices of the new graph. Go to Step 4.
If k = m and α = true, go to Step 1. If k = m and α = false, go to Step
7.
Step 7. Finish of this algorithm. A VS-digraph is constructed.
We will show that the algorithm VS constructs a vertex-saturated digraph.
~ 0 ) be a digraph constructed by the algorithm VS. Next, let
Theorem 2 Let G(V
k
~
G(V ) = (Yk , Γ) (k = 0, m) be a directed subgraph induced by the layer V k .
~ t (V k ) = (Yk , Γt ) obeys the
Then each antichain U ⊂ Yk \ V k of the graph G
following relation
Card(V k ∩ Γ−1
(2)
t U) ≥ Card(U)
~ k ), an antichain U ⊂ Yk \ V k of
Assume that, in the directed subgraph G(V
k
~
Gt (V ) = (Yk , Γt ) will be found such that
Card(V k ∩ Γ−1
t (U)) < Card(U).
∗
Construct a set U ∗ = (V k \ Γ−1
t (U)) ∪ U. Clearly, the set U is independent
~ k ) and Card(U ∗ ) > Card(V k ).
in the directed subdigraph G(V
k
~ t (V k ) = (Yk , Γt ) then the set
Since the set V is an antichain of the TCG G
−1
k
k
V \ Γt (U) ⊂ V is an antichain of this graph. The set U ⊂ Yk \ V k is an
~ t (V k ) by conditions of Theorem 2.
antichain of G
∗
Obviously, U ∩ Γt (V k \ Γ−1
t (U)) = ⊘, therefore the set U is an antichain of
~ t (V k ).
G
~ k ) is conWe have obtained a contradiction since the directed subgraph G(V
∗
structed by the algorithm VS and the antichain U could be discovered in Step
5. This proves the validity of Theorem 2.
Q.E.D.

7

~ 0 ), constructed by the algorithm VS, is vertexCorollary 1 The digraph G(V
saturated.
Theorem 3 VS-digraph can be constructed in time O(n5 ).
One completion of the steps 1 – 6 requires O(n3k ) time units, where nk is
~ k ). Assuming that for each completion of these
the size of the vertex set of G(V
steps the maximum antichain increases at one vertex, we obtain the design time
~ k ) vertex-saturated with respect to the initiating set, is equal
of a digraph G(V
4
to O(nk ).
Hence, the design time of a correctly constructed vertex-saturated digraph
~ 0 ) is equal to:
G(V
X
O(n4k ) = O(n5 ).
∀nk

Q.E.D.
~ 0 ) be vertex-saturated. Then there exists an
Theorem 4 Let a digraph G(V
~ t (V 0 ) such that its chains contain only essential arcs.
MCP P of the graph G
~ 0 ) is constructed by the algorithm VS. By Theorem 2,
Let a digraph G(V
each bipartite digraph G(V k , V k+1 ) (k = 0, m) of this digraph satisfies the Hall’s
theorem and, hence, has a matching that saturates each vertex of the set V k+1 ).
Q.E.D.
~ 0 ) be a VS-digraph. Then each chain of an MPP P of
Corollary 2 Let G(V
0
~
Gt (V ) is begun by some vertex v of V 0 .
~ 0 ) as a working
Due to this result we may use the adjacent matrix of G(V
0
~
table for determination MCP of the TCG Gt (V ) of a VS-digraph. Thus, we
will suppose that chains of MPP of the TCG of a VS-digraph are found using
the adjacent matrix of this digraph. That is, we choose only essential arcs
to construct each new MPP!
Certainly, we use the adjacent matrix of the transitive closure graph to search
for the maximum antichains U (v) of such TCG.
The instance of constructing vertex-saturated digraph is shown in Appendix
B.

4

An algorithm for finding MMIS of a graph

~ 0 ) is constructed, which has a MMIS Û such that
Let a saturated digraph G(V
0
Card(Û ) > Card(V ). In this case, at least one of the chains of TCG of the VS~ 0 ) contains a fictitious arc, whose endpoints belong to the MMIS.
digraph G(V
~ t (V 0 ).
Let, further, a some fictitious arc vi ≫ vj is found in the TCG G
~ t (V 0 ) and all vertices,
We shall remove the vertices vi , vj from the digraph G
8

~ 1 (V 0 ) =
which are adjacent with them. As a result, we shall obtain a digraph G
1
(V1 , ~Γ1 ), where
V1 = V \ ({vi , vj } ∪ Γ(vi ) ∪ Γ(vj )),
V10 = V 0 \ (~Γ−1 (vi ) ∪ ~Γ−1 (vj )). ~Γ1 = ~Γ ∩ V1 .
Here Γ(v) = ~Γ(v) ∪ ~Γ−1 (v).
~ 1 (V10 ), we shall use the procedure of constructing a VSFor the digraph G
~ 0 ),
digraph by the algorithm VS. As a result, we shall obtain a digraph G(Z
which shall call induced by removing the fictitious arc vi ≫ vj .
~ 0 ) is constructed on the
An algorithm for finding a MMIS of a digraph G(V
supposition that the following conjecture is true.
~ 0 ) has an independent set U ⊂ V
Conjecture 1 Let a saturated digraph G(V
0
such that Card(U ) > Card(V ). Then it will be found a fictitious arc vi ≫
~ 0 ), induced by removing this arc, the relation
vj such that in the digraph G(Z
0
0
Card(Z ) ≥ Card(V ) − 1 is satisfied.
The worded conjecture allows to formulate a solution algorithm for finding
a MMIS of a graph G ∈ Ln . Input of the algorithm is an undirected graph
G ∈ Ln . Output of the algorithm is the MMIS.
An algorithm for finding a MMIS.
Step 1. Execute an initial orientation of the graph edges so to get an acyclic
digraph G(V 0 ).
Step 2. Execute the algorithm VS for the digraph G(V 0 ).
Step 3. In TCG of the VS-digraph to find an unmarked fictitious arc vi ≫ vj .
Mark the found fictitious arc as considered. If all fictitious arcs are marked,
go to the Step 7.
Step 4. Remove vertices vi , vj as well as all adjacent with them vertices from the
~ 1 (V10 ) will be obtained.
saturated digraph G(V 0 ). As a result, a digraph G
Step 5. Execute the algorithm VS for the digraph G1 (V10 ). As a result, a digraph
~ 0 ) will be obtained.
G(Z
Step 6. If Card(Z 0 ) ≥ Card(V 0 ) − 1, construct a set W = Z 0 ∪ {vi , vj } and
~ 0 )) in the saturated digraph G(V 0 ).
execute the cutting operation σW (G(V
Go to Step 2. Otherwise go back to Step 3.
Step 7. Put a MMIS Û = V 0 .
Theorem 5 If the conjecture 1 is true then the stated algorithm finds a MMIS
of the graph G ∈ Ln .
It is obviously.

Q.E.D.

Theorem 6 The running time of the algorithm of finding a MMIS equals to
O(n8 ).
9

Indeed, single executing of the Steps 3 – 6 requires O(n51 ) of time units,
~ 0 ), induced by removing
where n1 is the number of vertices in the digraph G(Z
a fictitious arc. Since total number of fictitious arcs is O(n2 ), in worse case,
for executing the Steps 3 – 6 is required O(n7 ) of time units. If suppose that
after executing these steps, the found independent set V 0 will be increased to
the unit, the total running time of steps 2 – 6 equals to O(n8 ).
Q.E.D.

5

Conclusion

The pascal-programs were written for the proposed algorithm. Long testing
the program for random graphs has shown that the algorithm runs stably and
correctly.
Of course, the offered algorithm is not competitive in practice because of high
degree of polynomial estimation of the running time. However, the algorithm has
important theoretical significance since there is a good probability to prove that
for NP-complete problems possible to construct a polynomial-time algorithm.
Author thanks Guenter Stertenbrink1 for the help in testing the programs.

References
[1] P. Crescenzi and V. Kann. A compendium of np optimization problems. Technical report, Royal Institute of Technology, Stocholm, 1998.
This is the catalog of NP optimization problems. Also available at
ftp://ftp.nada.kth.se/Theory/Viggo-Kann/compendium.ps.
[2] L. R. Ford and D. R. Fulkerson. Flows in Networks. Princeton Univ. Press,
Princeton, N. J., 1962.
[3] M. R. Garey and D. S. Johnson. Computers and Intractability. W.H.Freeman
and Company, San Francisco, 1979.
[4] J. E. Hopcroft and R. M. Karp. A n5/2 algorithm for maximum matching
in bipartite graphs. J. SIAM Comp., 2:225–231, 1973.
[5] C. H. Papadimitriou and K. Steiglitz. Combinatorial optimization: Algorithms and Complexity. Prentice-hall Inc., Engiewood Cliffs, N. J., 1982.
[6] F. M. Reingold, J. Nivergelt, and N. Deo. Combinatorial Algorithms (Theory
and Practice). Prentice-hall Inc., Engiewood Cliffs, N. J., 1977.
[7] M. N. S. Swamy and K. Thulasiraman. Graphs, Networks and Algorithms.
John Wiley & Sons, N. Y., Chichester, 1981.
[8] R. E. Tarjan. Complexity of combinatorial algorithms.
20(3):457–491, 1978.
1 sktekkrtken(at)akol.com (remove k’s)

10

SIAM Rew.,

[9] D. B. West. Introduction to Graph Theory. Prentice Hall, Inc., Upper Saddle
River, NJ, 1996.

11

Appendix
A

Partially Ordered Sets

We recall some conceptions of Set Theory.
Relations between two objects are called binary. A binary relation R may
be represented by a listing of object pairs, which are in the relation R:
(a1 , b1 ), . . . , (am , bm ).
If (a, b) ∈ R, then this fact we also denote by aRb. When (a, b) 6∈ R, then we
will write aR̄b. If a ∈ A and b ∈ A for all aRb, then R is called a relation on
the set A. Further, we will consider only relations on the finite set A.
If A is a finite set and R is a relation on A, we can represent R as a digraph
~ Each element of A is assigned to a vertex of G,
~ and the vertex ai is joined
G.
with a vertex aj by the arc (ai , aj ) if and only if ai Raj .
A relation R is reflexive if aRa for every a ∈ A. A relation R is irreflexive
if aR̄a for every a ∈ A. A relation R is symmetric if whenever aRb, then bRa.
A relation R is antisymmetric if whenever aRb and bRa, then a = b. A relation
R is transitive if whenever aRb and bRc, then aRc.
A binary relation R is called a partial order if R is antisymmetric, and
transitive. The set A together with the partial order R are called a partially
ordered set. We will denote this partially ordered set by (A, R) or (A, ≥). If
a relation R is irreflexive, then such partial order is called strict. A strictly
ordered set is written by (A, >).
a1 a2 a3 a4 a5
a1 a2 a3 a4 a5
a1
a1
1❥
1 2
1 1❥ 1
✲1
a2
a3
a4
a5

∗
∗
∗
∗

1❄
1
4 1

a2
a3
a4
a5

∗
∗
1❥
1

2
∗

5

1

(a)

(b)

Figure 3: The adjacent matrixes
In Fig. 2, the acyclic graph represents the partial order, induced by the
binary relation
R = {(a1 , a2 ), (a1 , a3 ), (a1 , a5 ), (a4 , a2 ), (a5 , a2 )}.
Here and throughout, we assume that the orientation of arcs of a digraph on a
drawing is from below upwards.
Dilworth’s famous theorem establishes the relationship between a MCP and
the maximum antichain of (A, ≥) [2, 9].
12

Theorem 7 (Dilworth R.P.) Let (A, ≥) be a finite partially ordered set. The
minimum number of disjoint chains, which the set (A, ≥) can be partitioned on,
equals to the capacity of the maximum antichain in (A, ≥).
There is an efficient algorithm for the partitioning a finite partially ordered
set into the minimum number of chains and for finding the maximum antichain,
elaborated by L. R. Ford and D. R. Fulkerson [2]. In essence, this algorithm
finds the maximum matching in a bipartite graph G∗ = (X, Y, Γ∗ ). If a partially
ordered set has n elements, then this graph contains 2n vertices and Card(X) =
Card(Y ) = n. An edge (xi , yj ) joins two vertices x1 ∈ X and yj ∈ Y if and
only if the corresponding elements a1 , a2 ∈ A of (A, ≥) are comparable.
In manual computations, we will use an adjacent matrix M of G∗ as a
working table. Units of M determine its admissible cells. Two cells of M are
called independent if they are located in distinct rows and distinct columns of
M . To find the maximum matching, we will have to find the maximum number
of admissible independent cells of M .
The algorithm for partitioning a partially ordered set into the minimum
number of chains consists of two stages:
• Construct an initial partition of the partially ordered set into chains;
• Improve the existing partition if it is possible.
To avoid ambiguity, we always look through rows and columns of M uniformly: from top to bottom in columns and from left to right in rows.
To obtain an initial partition, we may use the following procedure.
Step 0. Put N = n, where n is the number of rows M , i = 1.
Step 1. If N = 0, then complete the calculations as an initial partition is found.
Step 2. In i-th row of M find the first on the order admissible cell, whose appropriate column is not marked. If such cell is not found, put i := i + 1,
N := N − 1 and go to Step 1. Otherwise, remember the found cell (i, j),
mark a column j, calculate i := i + 1 and go to Step 1.
Fig. 3 (a) shows the adjacent matrix for the strictly ordered set, represented
in Fig. 2. The chosen cells of the initial partition are indicated by a circle.
To find a MCP and the maximum antichain of a set (A, ≥), we will make use
of the Ford-Fulkerson’s algorithm [2]. The algorithm begins to work after termination of the previous procedure, that is, when there exists an initial partition
of the ordered set into chains.
Step 1. Mark rows of M that do not contain the chosen cells, by the symbol
(∗).
Step 2. Look through the newly marked rows of M and find all unchosen cells
in each row. Mark all unmarked columns of M that correspond with such
cells by an index of the row.

13

Step 3. Look through the newly marked columns. If an examined column contains a chosen cell (that is, the cell is enclosed within a circle), then mark
the row containing the chosen cell by an index of the examined column. If
the column does not contain a chosen cell, go to Step 4. If it is impossible
to mark new rows, then go to Step 5.
Step 4. The essence of the given step is the procedure of constructing a new
collection of independent cells, each having one more cell than the former
collection. At each stage of this procedure, except for the final step, we
pick a new admissible cell of M and delete the “old” one. Increasing
the total number of chosen cells happens as follows. In the found j-th
column, choose a new cell in a row m(j), where m(j) is a mark of the
current column. Let we already have chosen the cell (i, j), which marks
m(i) and m(j) correspond to, where m(i) is a mark the i-th row. If
m(j) = (∗), the procedure of constructing a new collection of independent
cells is completed. Delete all marks of rows and columns, and go to Step
2. Otherwise, delete the cell (i, m(i)) and choose a cell (m(m(i)), m(i)).
Put i = m(m(i)), j = m(i) and repeat the process described above.
Step 5. Find the maximum antichain U = Ur \ Uc , where Ur is a set of marked
rows, and Uc is a set of marked columns. Terminate the calculations. The
found admissible cells determine arcs forming chains of the MCP.
Fig. 3 (b) shows the picked cells of the optimal partition for the partially
ordered set, represented in Fig. 2. In this case, the MCP consists of the
chains A1 = {a1 , a3 }, A2 = {a4 , a2 }, and A3 = {a5 }. We also have a set
Ur = {a2 , a3 , a4 , a5 } of marked rows, and a set Uc = {a2 } of marked columns.
Consequently, the maximum antichain U is equal to
U = {a2 , a3 , a4 , a5 } \ {a2 } = {a3 , a4 , a5 }.
Ford-Fulkerson’s methodology, described above, for finding antichains may
be easily adapted to any algorithm of finding the maximum matching in a bipartite graph, for example, Hopcroft-Karp’s algorithm [4], [7], or flow algorithm
[5]. Therefore, we assume that the running-time of a MCP construction is equal
to O(n5/2 ).

B

An instance of constructing a vertex-saturated
digraph

Consider an instance of constructing a vertex-saturated digraph (VS-digraph).
~ 0 ), obtained from an initial undirected graph G
Fig. 4 shows a digraph G(X
as it was described in part 2. Recall that the orientation of arcs of the digraph
in figures is from below upwards.
Construct a VS-digraph.
14

~ t (V 0 ) is shown in Fig. 5. The fictitious
The adjacent matrix of the TCG G
arcs of this graph are represented by the letter f. Arcs, belonging to the MCP
~ t (V 0 ), are put into circles. These arcs are shown in Fig. 4 by thick lines.
of G
First of all, notice that the initiating set V 0 = {v1 , v2 , v3 , v4 } is a MIS of
~ 0 ).
G(V
Find the general antichain U (see Fig. 5 (a)). The set of marked rows is
Ur = {5, 7, 8, 10}, and the set of marked columns is empty, that is, Uc = ⊘.
Therefore:
U = Ur \ Uc = {5, 7, 8, 10} \ ⊘ = {5, 7, 8, 10}.
This antichain is a MIS of the digraph, and Card(U) = Card(V 0 ).
Find the maximum antichains U(v) for graph vertices.
Clearly, U(v5 ) = U(v7 ) = U(v8 ) = U(v10 ) = U.
~ t (X 0 ).
To find U(v1 ), mark the first row of the adjacent matrix of G
Marking the first row in Fig. 5 (b), we have Ur = {1, 3, 4, 5, 6, 7, 8.9.10}, and
Uc = {5, 7, 8, 9, 10}. Consequently,
U(v1 ) = Ur \ Uc = {1, 3, 4, 6}.
This antichain is a MIS of the digraph, and Card(U(v1 )) = Card(X 0 ).
Similarly, marking the second row in Fig. 5 (c), we have
U(v2 ) = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} \ {5, 6, 7, 8, 9, 10} = {1, 2, 3, 4}.
This maximum antichain is also a MIS of the digraph, and Card(U(v2 )) =
Card(V 0 ).
Similarly, we obtain the maximum antichains
U(v3 ) = {3, 4, 5, 8},
U(v4 ) = {4, 5, 8, 9},
and
U(v6 ) = {3, 4, 5, 6}
v10
①
✓✁❇
✓✁ ❇ v9
v8
① ✓✁ ①❇
✁ ✓ ✁✑✑
✓ ❇
v7
v5
❇
✁ ✓✑
✁ ✓
✑✁ ✓
① ✁ ①
✑
✓
❇ ①
❅✁ v6 ✁ ✓
❇
❇
✁ ❅ ✁✓
①
①
✁ ❅①
✓
✁
❇①
v1
v2
v3
v4
Figure 4: A digraph

15

v1
v2
v53
v4

v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
1❥
1
❥
1 1
f 1 1
1
1❥ f
1❥
1
∗

v6
v7
v8
v9
v10

v1
v2
v3
v4
v5
v6
v7
v8
v9
v10

v1
v2
v3
v4
v5
v6
v7
v8
v9
v10

1❥ 1 1
∗
∗
1❥
∗
(a)
v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
1❥
1
1 1❥
f 1 1
1
1❥ f
❥
1
1

5
∗
9
7
∗

1❥ 1 1 8
∗
∗
❥
1 10
∗
2 2 3 2 2 2
(c)
v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
1❥
1
1 1❥
f 1 1
1
1❥ f
1❥
1 ∗
∗
❥
1 1 1
∗
∗
1❥10
∗
4

v1
v2
v3
v4
v5
v6
v7
v8
v9
v10

v1
v2
v3
v4
v5
v6
v7
v8
v9
v10

v1
v2
v3
v4
v5
v6
v7
v8
v9
v10

v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
∗
1❥
1
❥
1 1
f 1 1
1
1❥ f 9
1❥
1 7
∗
❥
1 1 1 8
∗
∗
❥
1 10
∗
1
3 1 6 6
(b)
v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
1❥
1
1f
1
1 1❥
❥
1
1 f ∗
❥
1
1 7
∗
1❥ 1 1
∗
∗
1❥10
∗
3
3 3
(d)
v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
1❥
1
1 1❥
f 1 1
1
1❥ f 9
1❥
1 7
∗
❥
1 1 1 ∗
∗
∗
1❥10
∗

4

3 6 6 6

(e)

(f)
Figure 5: Finding antichains
16

v5 v6 v7 v8 v9 v10

v8

①
v5

v10
①
✁
✁ v9
① ✁ ①
✁
✁
✁
①
v6

①
v7

v5
v6
v7
v8
v9
v10

∗
1❥ 1 1
∗
∗
1❥
∗

(a)

(b)

Figure 6: The directed subgraph induced by the layer V 1
v5 v6 v7 v8 v9 v10
v9
v6
①
v5

①
❙
❙
① ❙
◗
◗ ❙
◗
◗❙
◗
❙①
①
v8
v10

①
v7

(a)

v5
v6
v7
v8
v9
v10

∗
1❥

9
∗

1❥

f

1
10

1
10

6
∗
∗

(b)

Figure 7: The new directed subgraph
from Fig. 5 (d), (e), and (f) correspondingly. Each of these maximum antichains
~ 0 ), and they have the number of elements equal to
is a MIS of the digraph G(V
0
V .
~ 0 ) is saturated with respect to the initiating set V 0 .
Thus, the digraph G(V
~ 0 ).
Now we examine directed subgraphs induced by layers of G(V
1
1
~
Consider directed subgraph G(V ) induced by layer V = {v5 , v6 , v7 }. This
subgraph is represented in Fig. 6 (a). Notice that the adjacent matrix of the
~ t (V 1 ) can be obtained from the adjacent matrix of G
~ t (V 0 ) directly.
TCG G
1
0
~ t (V ) is a part of the MCP of G
~ t (V ). The adjacent
Obviously, the MCP of G
1
~
~ t (V 1 )
matrix of Gt (V ) is shown in Fig. 6 (b). The general antichain U1 of G
equals
U1 = {v5 , v7 , v8 , v10 }.
~ 1 ); however, Card(U1 ) > Card(V 1 ). ConThis antichain is a MIS of G(V
~ 1 ) is not vertex-saturated with respect to
sequently, the directed subgraph G(V
its initiating set.
~ 1)
Therefore, we assume W = {v5 , v7 , v8 , v10 } and reorientate all arcs of G(X
incoming to the vertices of W . We obtain a new directed subgraph represented in

17

Fig. 7 (a). Clearly, this subgraph has a new initiating set V 1 = {v5 , v7 , v8 , v10 }.
~ 1 ) is vertexExamining as above, we find that the new directed subgraph G(V
saturated with respect to its initiating set V 1 .
~ 0 ). The adjacent matrix of this
Thus, we may construct a new digraph G(V
digraph can be obtained from the adjacent matrix of the initial digraph if the
~ 1 ).
corresponding part of it is replaced by the adjacent matrix of G(V
2
~
Similarly, we determine that a directed subgraph G(V ), where V 2 = {6},
is vertex-saturated with respect to its initiating set V 2 .

① v9
✂❇
✂❇
v6 ① ✂ ❇
❇
❅ ✂
❇
✂
v7
v5
v8
❅
✂ ❅① ❇
①
①
①
❍
❍
❍
❍
❍❇
✂
❍
❍❍
❍
v
❍
10
❍❍
❍
❇❍
❍❍ ✂
❍
❍❍
❍①
❍①
①
❇①❍❍
✂
v1

v2

v3

v4

v1
v2
v3
v4
v5
v6
v7
v8
v9
v10

v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
1 f
1❥ f
1❥ 1
1 1
❥
1
1
f 1
f 1❥

(a)

∗
1❥
1❥
1
10

1
10

(b)
Figure 8: The VS-digraph

~ 0 ) is a VS-digraph since
At last, we may make sure that the new digraph G(V
each of its directed subgraphs is vertex-saturated with respect to its initiating
set. This digraph is represented in Fig. 8 (a). The adjacent matrix of the
~ t (V 0 ) and its MCP together are represented in Fig. 8
transitive closure graph G
(b).

18

9
∗
6
∗
∗

