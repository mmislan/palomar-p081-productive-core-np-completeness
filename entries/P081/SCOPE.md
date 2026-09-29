# Formal scope

`UnconstrainedPACDetection.complexity_root` states
`Complexity.NPComplete BinaryPACVerifier.language` without hypotheses.

Inputs encode finite reversible reaction identities using literal nonnegative
integer reactant and product matrices. A core is an inclusion-minimal nonempty
productive motif. Each selected reaction has a selected entity on both literal
sides, and a signed real flow supported on the selected reactions strictly
produces every selected entity. No prescribed target or allowed-food set is an
input. Malformed and non-canonical binary encodings are rejected.

NP membership and polynomial many-one reductions use Complexitylib's multi-tape
Turing-machine semantics. The proof includes Cook–Levin, an actual polynomial-time
verifier and a total polynomial-time reduction from SAT. Their definitions are
reproduced in the Challenge for recursive comparison with the Solution.

This is a structural decision problem. The selected statement imposes no kinetic
law, concentration bounds or thermodynamic feasibility requirement. Literal
reactants and products, rather than the net matrix alone, determine admissibility.

The cited question is the unconstrained variant identified at the end of
Section 2.1 of Kosc et al., [PNAS 122, e2421274122 (2025)](https://pmc.ncbi.nlm.nih.gov/articles/PMC12067211/).
The precise encoding and reversible-source conventions are specified above.
