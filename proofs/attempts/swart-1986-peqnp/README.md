# Ted Swart (1986/87) - P=NP Attempt

**Attempt ID**: 1
**Author**: Ted Swart (University of Guelph)
**Year**: 1986/87
**Claim**: P = NP

## Summary

In 1986/87, Ted Swart wrote several papers (some titled "P=NP") that gave linear programming formulations of polynomial size for the Hamiltonian cycle problem.

## The Argument

Swart's approach:
1. Formulate the Hamiltonian cycle problem as a linear program
2. Claim the formulation has polynomial size
3. Since Hamiltonian cycle is NP-complete, and linear programming is in P, conclude P=NP

## Known Refutation

Mihalis Yannakakis refuted this in 1988, showing that expressing the traveling salesman polytope (or any 0/1 polytope associated with an NP-complete problem) with a symmetric linear program requires exponential size.

**Reference**: Yannakakis, M. (1988). "Expressing combinatorial optimization problems by linear programs". *Proceedings of 29th IEEE Symposium on Foundations of Computer Science*, pp. 223-228.

## The Error

The error in Swart's proof is that the linear programming formulation, when correctly constructed for the Hamiltonian cycle problem, actually requires exponential size (exponential number of constraints or variables). Swart's claimed polynomial-size formulation was either:

1. Incorrect (didn't actually capture the Hamiltonian cycle problem), or
2. Not actually polynomial-sized when fully written out

Yannakakis' result shows that no symmetric extended formulation of polynomial size can exist for NP-complete problems (unless P=NP, creating a circular argument).

## Formalization Status

- [ ] Coq: Not started
- [ ] Lean: Not started
- [ ] Isabelle: Not started

## Formalization Plan

To formalize this attempt, we need to:

1. Define linear programs formally
2. Define the Hamiltonian cycle problem
3. Formalize Swart's proposed LP formulation
4. Show that either:
   - The formulation doesn't correctly capture Hamiltonian cycle, OR
   - The formulation requires exponential size
5. Reference Yannakakis' impossibility result if needed

## Source

- Woeginger's list: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #1)
- Original papers by Swart (to be added)

## See Also

- [Parent issue #44](https://github.com/konard/p-vs-np/issues/44) - Test all P vs NP attempts formally
- [Issue tracking this attempt](https://github.com/konard/p-vs-np/issues/TBD)

---

*Created: 2025-10-17*
*Last updated: 2025-10-17*
