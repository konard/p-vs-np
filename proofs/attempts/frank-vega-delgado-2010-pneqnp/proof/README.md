# Forward Proof Formalization: Vega Delgado 2010

This directory contains the formal proof attempt following Vega Delgado's November 2010 approach as faithfully as possible.

## Contents

- `lean/VegaDelgado2010Proof.lean` - Lean 4 formalization
- `rocq/VegaDelgado2010Proof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture:

1. **One-Way Function Definition**: Formal definition of computability and hardness of inversion
2. **Known Implication**: The established theorem that one-way functions exist → P ≠ NP (equivalently, P = NP → one-way functions do not exist)
3. **Vega Delgado's Claimed Construction**: The attempt to define and argue existence of a specific one-way function
4. **Critical Gap Identification**: The step where the argument for hardness of inversion fails

## The Attempted Proof Logic

Vega Delgado's November 2010 argument proceeds:

1. **Define** a candidate one-way function `f` computable in polynomial time
2. **Claim** that inverting `f` requires superpolynomial time
3. **Derive** that `f` is a genuine one-way function (the FAILING STEP)
4. **Apply** the known theorem: one-way functions exist → P ≠ NP
5. **Conclude** P ≠ NP

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) / `Admitted` (Rocq) placeholders at the critical gaps where the argument fails:

1. **Hardness of inversion** (`owf_inversion_hard`): The claim that the candidate function is hard to invert is not proven — it implicitly assumes P ≠ NP (circular) or makes an unsubstantiated claim about computational hardness.

2. **Existence of one-way functions** (`one_way_functions_exist`): Since hardness is not established, the existence of one-way functions cannot be concluded.

## The Core Error

The proof is circular:

| What Vega Delgado Claims | Why It Fails |
|---|---|
| Function `f` is hard to invert | Hardness requires P ≠ NP to establish |
| One-way functions exist | Unproven — equivalent to assuming P ≠ NP |
| P = NP → no one-way functions | Known theorem (valid) |
| Contrapositive: one-way functions exist → P ≠ NP | Known theorem (valid) |
| Conclusion: P ≠ NP | Invalid — built on circular premise |

The existence of one-way functions is itself an open problem. Showing they exist is essentially the same as showing P ≠ NP. Vega Delgado's argument attempts to bypass this by constructing a "candidate" function, but does not rigorously prove its hardness without implicitly assuming P ≠ NP.

## See Also

- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) - Description of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
- [`../README.md`](../README.md) - Overview of the attempt
- [`../../vega-delgado-2012-pneqnp/`](../../vega-delgado-2012-pneqnp/) - Vega Delgado's 2012 attempt (#83) with different approach
