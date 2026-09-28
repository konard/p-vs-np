# Refutation Notes

Argall's argument fails because incompleteness is existential, not universal.

Goedel incompleteness yields some undecidable sentence for each suitable consistent theory. It does not follow that each formally expressible sentence is undecidable. The P=NP sentence may be expressible in ZFC while still being provable, refutable, or independent; incompleteness alone does not decide which case holds.

The Lean and Rocq files prove this structural point with an abstract countermodel: a theory may be incomplete and still prove a particular expressible statement.
