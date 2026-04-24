# Forward Proof Formalization: Vega Delgado 2010

This directory contains the formal proof attempt following Vega Delgado's November 2010 `CERTIFYING` argument as faithfully as possible.

## Contents

- `lean/VegaDelgado2010Proof.lean` - Lean 4 formalization
- `rocq/VegaDelgado2010Proof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture:

1. **The CERTIFYING problem**: The paper's search problem, where one asks for an input that produces a given output for a deterministic machine.
2. **Membership in NP**: The easy direction, where a candidate input can be checked efficiently.
3. **The claimed contradiction**: The paper's unsupported leap from `CERTIFYING ∈ P` to an undecidable language in NP.
4. **The refutation point**: The missing reduction/argument that makes the contradiction go through.

## The Attempted Proof Logic

Vega Delgado's November 2010 argument proceeds:

1. **Define** `CERTIFYING` as a problem about reconstructing a machine input from its output
2. **Show** that `CERTIFYING` lies in NP
3. **Claim** that `CERTIFYING ∈ P` would force an undecidable language into NP
4. **Use** the fact that NP languages are decidable to reach a contradiction
5. **Conclude** that `CERTIFYING ∉ P` and hence P ≠ NP

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) / `Admitted` (Rocq) placeholders at the critical gap where the argument fails:

1. **Unsupported implication** (`certifying_in_p_implies_undecidable_np`): The claim that `CERTIFYING ∈ P` yields an undecidable language in NP is not proven.

2. **Search-versus-decision gap**: The paper uses a search-style task to argue about class separation, but does not provide the missing reduction needed to make the contradiction rigorous.

## The Core Error

The proof is incomplete at the only step that would make it work:

| What Vega Delgado Claims | Why It Fails |
|---|---|
| `CERTIFYING ∈ NP` | Plausible at the level of a witness check |
| `CERTIFYING ∈ P →` undecidable language in NP | Unsupported leap |
| NP languages are decidable | Correct |
| Contradiction | Never fully established |

The existence of an efficiently checkable witness does not by itself produce an undecidable language. The paper does not supply the missing formal reduction.

## See Also

- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) - Description of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
- [`../README.md`](../README.md) - Overview of the attempt
