# Angela Weiss (2011) - Original Proof Idea

## Overview

M. Angela Weiss's 2011 draft, "A Polynomial Algorithm for 3-sat", claims to prove
P = NP by using KE-tableaux to build a compressed "macro" representation of the
branching structure of a 3-SAT tableau.

The paper's intended pipeline is:

1. Start from a 3-SAT instance.
2. Apply KE-tableau reasoning to expand the instance into closed and open branches.
3. Compress the relevant branching information into a macro.
4. Evaluate the macro in polynomial time.
5. Conclude that 3-SAT is in P, and therefore P = NP.

## What This Folder Contains

- [`README.md`](README.md) - Short description of the original idea and source material
- [`ORIGINAL.md`](ORIGINAL.md) - English reconstruction of the draft paper
- [`ORIGINAL.pdf`](ORIGINAL.pdf) - Closest available original source from the author's website

## Relation to the Main Attempt

- [`../README.md`](../README.md) - Full overview and error analysis
- [`../proof/README.md`](../proof/README.md) - Forward formalization of the claimed argument
- [`../refutation/README.md`](../refutation/README.md) - Formal refutation and gap analysis
