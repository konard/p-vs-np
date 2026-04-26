# Forward Proof Formalization

The files in this directory model Romanov's intended P=NP proof skeleton.

The disputed step is represented explicitly:

```text
SEPNonEmpty formula -> Satisfiable formula
```

This is the sufficiency direction of Romanov's Theorem 2. The formalization
marks it with `sorry` in Lean and `Admitted` in Rocq because the paper does not
provide a derivation of this global soundness invariant from the local CTS and
hyperstructure operations.

