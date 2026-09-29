# Unconstrained detection of productive autocatalytic cores is NP-complete

Kosc, Kuperberg, Rajon and Charlat ([PNAS 122, e2421274122, 2025, Section 2.1](https://pmc.ncbi.nlm.nih.gov/articles/PMC12067211/)) left open the complexity of detecting an autocatalytic core without a prescribed target species or allowed-food set. For finite reversible reaction networks with literal nonnegative integer reactant and product matrices, this unconstrained detection problem is proved NP-complete. A core is a nonempty entity/reaction pair, minimal under componentwise inclusion, with a selected reactant and product in every selected reaction and a signed real flow that strictly produces every selected entity. The input uses a canonical binary encoding. NP membership and a total polynomial-time many-one reduction from SAT are formalized using Complexitylib’s multi-tape Turing machines, including the Cook–Levin theorem.

[Formal statement](Registry/P081/Challenge.lean) · [Proof](Registry/P081/Solution.lean) · [Manuscript](papers/P081/paper.pdf) · [Metadata](entries/P081/formalization.yaml) · [Claim correspondence](entries/P081/CLAIM-EVIDENCE.md)

The complete project proof closure is included, together with the selected Complexitylib sources and their [attribution](proofs/Complexitylib/UPSTREAM.md). Lean and its dependencies are pinned in `lean-toolchain` and `lake-manifest.json`.
