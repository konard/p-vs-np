# Original Paper: Algorithmic Complexity of Pair Cleaning Method for k-Satisfiability Problem

**Author:** Sergey Kardash
**Year:** 2011 (submitted July 30, 2011; revised May 31, 2012)
**arXiv ID:** [1108.0408](https://arxiv.org/abs/1108.0408)
**Subject Classification:** Computational Complexity (cs.CC); Data Structures and Algorithms (cs.DS)
**Woeginger's List:** Entry #76

---

## Abstract

It's known that 3-satisfiability problem is NP-complete. Here polynomial algorithm for solving k-satisfiability (k ≥ 2) problem is assumed. In case theoretical points are right, sets P and NP are equal.

---

## 1 Introduction

**Definition 1.** Formulae A(x) is called k-CNF if

    A(x) = ∩ᵢ₌₁ⁿ ∪ⱼ₌₁ᵏ xᵤᵢⱼ^σᵢⱼ,  σᵢⱼ ∈ {0,1}, uᵢⱼ ∈ {1,…,m}, ∀i ∈ {1,…,n}, ∀j ∈ {1,…,k}

- ∩ — conjunction operation
- ∪ — disjunction operation
- m — number of variables in formulae
- n — number of clauses
- k — number of variables in each disjunction
- nt — number of clause groups

    x^σ = { x,   if σ = 0
           { x̄,  if σ = 1

**Example 1.** 3-CNF A(x) = (x₁ ∪ x₂ ∪ x₃) ∩ (x̄₁ ∪ x₃ ∪ x̄₄). Here m = 4, n = 2, k = 3, nt = 2.

**Definition 2.** Let formulae A(x) is k-CNF. Problem of defining whether equation A(x) = 1 has solution or not is called k-satisfiability problem of formulae A (or k-SAT(A)).

**Example 2.** k-satisfiability problem of formulae A described in Example 1 (k-SAT(A)) is defining whether ∃x ∈ Bᵐ (boolean vector of size m): A(x) = 1. It's evident that x₀ = (1,1,1,1) makes A(x₀) = 1. A(x₀) is satisfiable. k-CNF B(x) = (x₁ ∪ x₂) ∩ (x̄₁ ∪ x₂) ∩ (x₁ ∪ x̄₂) ∩ (x̄₁ ∪ x̄₂) is an example of not satisfiable task. There is no x₀ : A(x₀) = 1. On the contrary A(x) = 0, ∀x.

It was proved that 2-satisfiability problem has polynomial solution (by Krom [2]). We are going to show polynomial algorithm (from n) for any k-SAT. By the way we describe method of getting 1 explicit solution of corresponding equation A(x) = 1 in case source task is satisfiable which is polynomial from n and method of solving equation A(x) = 1 which is polynomial from number of such solutions.

---

## 2 Method Description

Initially new mathematic objects and operations for them are introduced. After description of method in pure mathematic way algorithmic presentation which is more readable is given. Almost each structure has 2 common structures associated with it: 1) variable set associated with this structure and 2) some value sets of these variables. Though they will be defined separately it's easy to see common logic of their introduction.

Let x_{s₁s₂⋯sₖ} = (x_{s₁}, x_{s₂}, …, x_{sₖ}). Further in order to avoid enumeration of variables which are not related to described structure we list important variables using such notation.

**Definition 3.** Clause group signed T_{s₁s₂⋯sₖ}(A) is a set of all clauses ∪ⱼ₌₁ᵏ x_{sⱼ}^σₜⱼ where u_{i1}u_{i2}⋯u_{ik} = s₁s₂⋯sₖ. Variable set associated with T_{u_{s₁}u_{s₂}⋯sₖ}(A) (or X(T_{s₁s₂⋯sₖ}(A))) is x_{s₁s₂⋯sₖ}. Value of clause group T_{s₁s₂⋯sₖ}(A) is a value of x_{s₁s₂⋯sₖ} such that k-CNF consisted of all clauses from clause group T_{s₁s₂⋯sₖ} is equal to 1. Value set induced by clause group T_{s₁s₂⋯sₖ}(A) (or V(T_{s₁s₂⋯sₖ}(A))) is a set of all values of this clause group.

**Example 3.** Though clauses x₁ ∪ x₂ ∪ x₃ and x̄₁ ∪ x₂ ∪ x̄₃ have different degrees they belong to the same clause group T₁₂₃ in case they present in formulae A.

**Example 4.** For example clause group T₁₂₃ consists of clauses x₁ ∪ x₂ ∪ x₃ and x̄₁ ∪ x₂ ∪ x̄₃. Value set induced by this clause group:

| x₁ | x₂ | x₃ |
|----|----|----|
| 0  | 0  | 1  |
| 0  | 1  | 0  |
| 0  | 1  | 1  |
| 1  | 0  | 0  |
| 1  | 1  | 0  |
| 1  | 1  | 1  |

We have excluded from this list only sets which make 3-CNF (x₁ ∪ x₂ ∪ x₃) ∩ (x̄₁ ∪ x₂ ∪ x̄₃) equal to 0 (x₁₂₃ = (0,0,0) and x₁₂₃ = (1,0,1)).

**Definition 4.** k-CNF A(x) all clauses of that can be classified into nt clause groups is called k-CNF of degree nt. It also can be signed as A^n_k(x) or Aₖ(x) or Aⁿ(x).

**Example 5.** 2-SAT A(x) = (x₁ ∪ x₂) ∩ (x̄₁ ∪ x₂) ∩ (x₂ ∪ x₃) ∩ (x̄₂ ∪ x̄₃) has 2 clause groups T₁₂ and T₂₃, so it's degree is 2 and it can be signed as A²₂(x) or A₂(x) or A²(x).

**Definition 5.** Clause combination F for formulae A(x) consisted from clause groups T_{u_{i1,1}u_{i1,2}⋯u_{i1,k}}(A), T_{u_{i2,1}u_{i2,2}⋯u_{i2,k}}(A), …, T_{u_{il,1}u_{il,2}⋯u_{il,k}}(A) is a set of listed clause groups. Variable set associated with it is x_{h₁h₂⋯hᵣ} where each variable index from set of clause groups is presented only once.

**Definition 6.** Value of clause combination F is a value of x_{h₁h₂⋯hᵣ} (variable set associated with it) such that k-CNF consisted of all clauses associated with listed clause groups equals 1.

**Definition 7.** Value set of clause combination F based on A(x) is a set of values of this clause combination.

**Definition 8.** Value set of clause combination F induced by A(x) is a set of all values of this clause combination.

**Example 6.** Let we have 2 clause groups: T₁₂(A) which has clauses x₁ ∪ x₂ and x̄₁ ∪ x₂ in formulae A and T₂₃(A) which has clauses x₂ ∪ x₃ and x̄₂ ∪ x̄₃. Then value set induced by clause combination F(T₁₂, T₂₃) is a set of all possible values of x₁₂₃ which make 2-SAT (x₁ ∪ x₂) ∩ (x̄₁ ∪ x₂) ∩ (x₂ ∪ x₃) ∩ (x̄₂ ∪ x̄₃) equal to 1:

| x₁ | x₂ | x₃ |
|----|----|----|
| 0  | 1  | 0  |
| 0  | 1  | 1  |

Each row of the list is a value of clause combination F(T₁₂, T₂₃), i.e. x₁₂₃ = (0,1,0).

**Definition 9.** Relationship structure for k-CNF A(x) (R(A)) is a set of all possible clause combinations consisted of (k+1) clause groups.

**Example 7.** For 2-CNF A(x) = (x₁ ∪ x₂) ∩ (x₁ ∪ x̄₂) ∩ (x₂ ∪ x₃) ∩ (x₁ ∪ x̄₃) ∩ (x₁ ∪ x₄) ∩ (x̄₁ ∪ x₄) clause groups are: T₁₂, T₂₃, T₁₃, T₁₄. R(A) = {F(T₁₂, T₂₃, T₁₃), F(T₁₂, T₂₃, T₁₄), F(T₁₂, T₁₃, T₁₄), F(T₂₃, T₁₃, T₁₄)}.

**Definition 10.** Value set of relationship structure induced by k-CNF A(x) (Vᵢ(R(A))) is a set of value sets of clause combinations induced by A(x) involved in relationship structure based on k-CNF A(x).

**Definition 11.** Value set of relationship structure based on k-CNF A(x) (Vb(R(A))) is a set of value sets of clause combinations based on A(x) involved in relationship structure based on k-CNF A(x).

**Definition 12.** Value set of relationship structure based on k-CNF A(x) is called empty (V(R(A)) = ∅) if at least one value set of clause combination value set of relationship structure consists of is empty.

**Definition 13.** Let R(A) — relationship structure for k-CNF A(x). V(R(A)) = {V₁, V₂, …, Vt}, G(R(A)) = {G₁, G₂, …, Gt} — 2 value sets of this relationship structures based on A(x). We call V(R(A)) included in G(R(A)) (or V(R(A)) ⊆ G(R(A))) if Vᵢ ⊆ Gᵢ, ∀i ∈ {1,…,t}.

**Definition 14.** Let we have 2 clause combinations F(Tᵢ₁, Tᵢ₂, …, Tᵢs, A) and F(Tⱼ₁, Tⱼ₂, …, Tⱼᵣ, A). Let they have common variables xᵢ₁, xᵢ₂, …, xᵢs — those variables which present in both clause combinations. Clearing of given pair of value sets V₁ and V₂ of clause combinations correspondingly based on k-CNF A(x) is a process of:
- deleting x¹_{a₁a₂⋯aᵤ} ∈ V₁ for which ∄ x²_{b₁b₂⋯bᵤ} ∈ V₂ : x¹_{i₁i₂⋯is} = x²_{i₁i₂⋯is}
- deleting x²_{b₁b₂⋯bᵤ} ∈ V₂ for which ∄ x¹_{a₁a₂⋯aᵤ} ∈ V₁ : x¹_{i₁i₂⋯is} = x²_{i₁i₂⋯is}

Clearing procedure is briefly marked as C(V₁, V₂).

**Definition 15.** Clearing of value set of relationship structure (Vᵣ) based on k-CNF A(x) (pair cleaning method for formulae A(x)) is a process of clearing of all possible pairs of value sets of clause combination based on k-CNF A(x) contained in Vᵣ until clearing is impossible. We'll note result of cleaning as C(V(R(A))).

### Pair Cleaning Method in Algorithmic Form

```
Vnew ← Vsource(R(A))
repeat
    Vold ← Vnew
    for i = 1 → d-1 do
        for j = i+1 → d do
            (Vⁱnew, Vʲnew) ← C(Vⁱnew, Vⁱnew)
        end for
    end for
until Vnew = Vold
```

where:
- d — number of clause combinations in relationship structure
- Vsource(R(A)) — value set of relationship structure induced by A(x)

**Definition 16.** Let V = V(R(A)) — value set of relationship structure based on k-CNF A(x). V is called unclearable if V = C(V).

**Lemma 1.** Let V = V(R(A)) — value set of relationship structure induced by k-CNF A(x). Vres = C(V). Vres ≠ ∅ ⟺ ∃ V₁ ⊆ Vres where V₁ — unclearable value set of relationship structure based on k-CNF A(x) where each value set of clause combination consists of 1 value of this clause combination.

*(Proof by induction on the number of clause groups nt. Base case: nt ≤ k+1 reduces to single clause combination. Inductive step: given Ant+1(x), remove one clause group Tnt+1, apply induction hypothesis to Bnt(x), then extend the single-value unclearable structure to include Tnt+1 using compatibility of common variables.)*

**Lemma 2.** Let V₁ — value set of relationship structure based on k-CNF A(x) where each value set of clause combination consists of 1 value of this clause combination. V₁ is unclearable ⟺ k-CNF A(x) is equal to 1 on this value set.

*(Proof: ⇒ Since all clause combinations are satisfied and common variables agree, the full assignment satisfies the k-CNF. ⇐ Any satisfying assignment restricted to clause combination variables is unclearable.)*

**Theorem 1.** Result of pair cleaning method applied to source k-CNF is not empty ⟺ ∃ solution of equation k-CNF = 1.

*Proof.* Consecutive usage of Lemma 1 and Lemma 2.

**Theorem 2.** V⁰_{Fᵢ} ∈ VFᵢ — member of Vc = C(V) ⟺ ∃ V¹c : V⁰_{Fᵢ} ∈ V^c_{Fᵢ} — member of V¹c.

*(Proof scheme is same as for Lemma 1; full description deferred to full version.)*

---

## 3 Complexity

- Number of values clause group can take is less than 2ᵏ.
- Number of values clause combination can take is less than 2^{k(k+1)}.
- Number of clause combinations in relationship structure is C(nt, k+1).
- Number of comparisons during one iteration pass is less than 2^{2k(k+1)} · C(nt, k+1)².
- Number of iterations is less than 2^{k(k+1)} · C(nt, k+1).
- That means that number of operations for algorithm is less than 2^{3k(k+1)} · C(nt, k+1)³.

Therefore complexity of k-SAT is O(nt^{3(k+1)}). For 3-SAT it's O(nt^{12}).

2^{-k}·n ≤ nt ≤ n ⇒ method's complexity is O(n^{3(k+1)}). For 3-SAT it's O(n^{12}). That means that pair cleaning method is polynomial and P=NP.

---

## References

1. Cook, Stephen (April 2000). The P versus NP Problem. Clay Mathematics Institute. Retrieved 2006-10-18.
2. Krom, Melven R. (1967), "The Decision Problem for a Class of First-Order Formulas in Which all Disjunctions are Binary", Zeitschrift fur Mathematische Logik und Grundlagen der Mathematik, 13, pp. 15-20.
