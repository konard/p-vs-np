# Forward Proof Attempt

This folder follows the paper's proof strategy:

1. Model E2DTSP and GAP as abstract decision or optimization problems.
2. Record the paper's claim that E2DTSP has a triangle-reduction
   property.
3. Record the paper's claim that arbitrary GAP lacks this property.
4. Show that the final P≠NP conclusion requires an additional theorem:
   lacking this specific structure implies no polynomial-time algorithm
   exists.

The Lean and Rocq files keep that additional theorem admitted/commented as
the exact point where the original proof cannot be completed.
