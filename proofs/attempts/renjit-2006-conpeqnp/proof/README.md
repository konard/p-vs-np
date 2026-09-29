# Renjit (2006) - Forward Proof Attempt

## Note on This Formalization

The original paper "coNP Is Equal To NP" (arXiv:cs.CC/0611147) was **withdrawn by the author** in August 2009 and is no longer available for download. This formalization represents our **best-effort reconstruction** of the likely proof strategy based on:

1. Available metadata (title, abstract, classification)
2. The paper's focus on the clique problem (mentioned in metadata)
3. The author's related 2005 P≠NP attempt (also clique-based, also withdrawn)
4. Common patterns in NP = co-NP attempts

**This is NOT the actual proof** - it is an educated reconstruction for educational purposes.

## Reconstructed Proof Structure

Based on typical approaches in NP = co-NP attempts and the limited available information, the proof likely followed this structure:

### Step 1: Define the Target (NP = co-NP)

**Goal**: Prove that for every problem L in NP, L is also in co-NP (and vice versa).

**Equivalent Formulation**: Show that for every NP problem, both "yes" and "no" instances have polynomial-sized, polynomial-time verifiable certificates.

```
NP = co-NP  ⟺  ∀L ∈ NP. L ∈ co-NP
            ⟺  ∀L ∈ NP. ∀instance.
                   (L(instance) = NO) → ∃poly-cert for NO
```

### Step 2: Focus on the Clique Problem

**Rationale**: Since CLIQUE is NP-complete and NO-CLIQUE is co-NP-complete, proving they have symmetric certificate structures might seem to imply NP = co-NP.

**CLIQUE Problem**:
- Input: Graph G = (V, E), integer k
- Question: Does G contain a clique of size ≥ k?
- NP Certificate for YES: The k vertices forming the clique

**NO-CLIQUE Problem**:
- Input: Graph G = (V, E), integer k
- Question: Does G contain NO clique of size ≥ k?
- co-NP Certificate for YES: ???

### Step 3: Claim a Symmetric Certificate Structure

**Likely Claim**: There exists a polynomial-sized certificate for NO-CLIQUE instances that can be verified in polynomial time.

**Possible Approaches** (common in such attempts):

#### Approach A: Vertex Cover Argument
```
Claim: If graph has no k-clique, then it has a "small" vertex cover
       that blocks all k-cliques.

Proposed Certificate: A set S of vertices such that removing S
                     leaves no k-clique in G-S.

Verification: Check that |S| is "small" and G-S has no k-clique.

ERROR: Checking that G-S has no k-clique is itself a co-NP problem!
       This is circular reasoning - we haven't made progress.
```

#### Approach B: Edge Cover Argument
```
Claim: If graph has no k-clique, then there exists a "small" set
       of missing edges whose addition would be necessary for any k-clique.

Proposed Certificate: A set E' of non-edges such that G must have
                     at least one edge from E' in any potential k-clique.

Verification: Check that |E'| is polynomial and every k-subset needs
             an edge from E'.

ERROR: Verifying "every k-subset needs an edge from E'" requires
       checking all (n choose k) subsets - exponential!
```

#### Approach C: Structural Decomposition
```
Claim: If graph has no k-clique, it has a polynomial-sized proof
       based on graph decomposition.

Proposed Certificate: A decomposition of G into components, each
                     provably having no k-clique for structural reasons.

Verification: Check each component's structure.

ERROR: Either:
  - The decomposition is not always possible in polynomial size
  - Verifying "component has no k-clique" requires co-NP verification
  - The decomposition doesn't cover all cases
```

### Step 4: Claim Generalization to All NP Problems

**Likely Argument**: Since CLIQUE is NP-complete, all NP problems reduce to CLIQUE. Therefore, the certificate structure for CLIQUE/NO-CLIQUE extends to all NP/co-NP problems.

**Formalization Attempt**:
```
1. CLIQUE is NP-complete
2. ∀L ∈ NP. L ≤ₚ CLIQUE (polynomial-time reduction exists)
3. We showed CLIQUE has symmetric certificate structure (Steps 2-3)
4. Therefore, ∀L ∈ NP. L has symmetric certificate structure
5. Therefore, NP = co-NP
```

**ERROR**: Step 3→4 is invalid! Reductions preserve decidability, not certificate structure.

### Step 5: Conclude NP = co-NP

**Conclusion**: From the claimed symmetric certificate structure for CLIQUE and the (invalid) generalization, conclude NP = co-NP.

## Where the Proof Goes Wrong

### Critical Error 1: The Certificate Construction

**Problem**: None of the typical approaches for constructing polynomial "no" certificates actually work:

- **Approach A (Vertex Cover)**: Circular - verification requires solving another co-NP problem
- **Approach B (Edge Cover)**: Verification requires exponential checking
- **Approach C (Decomposition)**: Either not always possible, or verification is circular

**Fundamental Issue**: Proving non-existence of a k-clique inherently requires reasoning about all (n choose k) potential cliques. For k = Θ(n), this is exponential.

### Critical Error 2: The Generalization

**Problem**: Even IF we had symmetric certificates for CLIQUE/NO-CLIQUE (which we don't), this wouldn't extend to all NP problems.

**Why Reductions Don't Transfer Certificates**:

Suppose L ≤ₚ CLIQUE via reduction f.
- For instance x of L: f(x) is a graph
- If x ∈ L, then f(x) has a k-clique → we get a CLIQUE certificate
- But the CLIQUE certificate (k vertices) doesn't directly give us an L certificate!

The reduction f transforms **instances**, not certificates. It tells us:
```
x ∈ L  ⟺  f(x) ∈ CLIQUE
```

But NOT:
```
cert is a certificate for x ∈ L  ⟺  f'(cert) is a certificate for f(x) ∈ CLIQUE
```

Certificate structures are NOT preserved under reductions!

### Critical Error 3: Special Cases vs Universal Proof

**Problem**: The construction might work for special graph structures but fail generally.

Examples where finding/verifying NO-CLIQUE might seem easier:
- **Complete graphs**: Obviously have k-cliques for k ≤ n
- **Empty graphs**: Obviously have no k-cliques for k ≥ 2
- **Trees**: Have no k-cliques for k ≥ 3 (tree structure is verifiable in P)
- **Planar graphs**: Have no k-cliques for k ≥ 5 (four-color theorem)

But these are SPECIAL cases. A proof needs to work for:
- Arbitrary graphs
- All values of k
- All instances, including adversarially constructed ones

## Why This Proof Cannot Be Completed

The formalization in `lean/RenjitProof.lean` and `rocq/RenjitProof.v` attempts to follow the reconstructed proof structure but necessarily includes:

1. **Axioms for unproven claims**: Where the original proof likely made unjustified claims
2. **`sorry` / `Admitted` for gaps**: Where the proof steps cannot be completed
3. **Comments explaining impossibility**: Why certain steps cannot be formalized correctly

This is intentional - the goal is to show WHERE and WHY the proof fails, not to complete an impossible proof.

## Key Impossibility Results

### Theorem: No Polynomial NO-CLIQUE Certificates (Likely)

If NP ≠ co-NP (as widely believed), then:
- NO-CLIQUE ∉ NP (there are no polynomial "yes" certificates for NO-CLIQUE)
- Equivalently: CLIQUE ∉ co-NP (no polynomial "no" certificates for CLIQUE)

This is consistent with our intuition that verifying non-existence is harder than verifying existence.

### Theorem: Certificate Structure Not Preserved by Reductions

For any NP-complete problem L and reduction f: L ≤ₚ SAT:
- Certificates for L instances do not necessarily transform to SAT certificates
- Even though L and SAT are "equivalent" for decidability, their certificate structures differ

## Educational Value

This formalization demonstrates:

1. **Reconstructing Historical Attempts**: How to analyze a proof strategy from limited information
2. **Identifying Error Patterns**: Common mistakes in complexity proofs
3. **Understanding Reductions**: What NP-completeness does and doesn't imply
4. **Certificate Asymmetry**: The fundamental challenge in NP vs co-NP
5. **Formal Verification**: Using proof assistants to expose gaps in informal proofs

## References

1. Karp, R.M. (1972). "Reducibility Among Combinatorial Problems." (NP-completeness of CLIQUE)
2. Arora & Barak (2009). "Computational Complexity: A Modern Approach." Chapter 2.
3. Baker, Gill, Solovay (1975). "Relativizations of the P=?NP Question." (Oracle separations)
4. Fortnow (2009). "The Status of the P versus NP Problem." Communications of the ACM.
