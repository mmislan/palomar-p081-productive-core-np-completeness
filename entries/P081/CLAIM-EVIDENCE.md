# P081: claim-to-evidence correspondence

## Selected declaration

`UnconstrainedPACDetection.complexity_root : Complexity.NPComplete BinaryPACVerifier.language`

It has no hypotheses. `NPComplete L` unfolds to `L ∈ NP ∧ NPHard L`, where
`NPHard L` means `∀ L' ∈ NP, L' ≤ₚ L`. The Solution
(`Registry/P081/Solution.lean`) only imports
`proofs/UnconstrainedPACDetection/ComplexityRoot.lean`, which proves the theorem
from `SAT.NPHard_language` (Cook–Levin, proved in the imported Complexitylib
sources), `VerifierNPPolynomial.in_NP` and the total reduction
`sat_reduction : SAT.language ≤ₚ BinaryPACVerifier.language`.

| Mathematical content | Exact formal content in the Challenge | Evidence |
|---|---|---|
| Main theorem: UPAC is NP-complete under polynomial-time many-one reductions (manuscript Theorem 2) | `complexity_root : NPComplete BinaryPACVerifier.language` | The Solution derives the selected theorem from NP membership, the total SAT reduction and Cook–Levin, all included in its import closure. |
| Input language | `BinaryPACVerifier.language = {input \| ∃ s, BinarySourceData.decode input = some s ∧ ∃ c, s.toSource.PAC c}` | Definition in the Challenge; identical text in `proofs/UnconstrainedPACDetection/BinaryPACVerifier.lean`. |
| Canonical dense binary encoding of \|E\|, \|R\| and the left and right matrices, reaction-major, entity-minor (manuscript Section 1 and formal appendix) | `BinaryFields.encodeField` writes each bit prefixed by `1` and terminates with `0`; `DenseSource.encode` encodes `entities.bits :: reactions.bits :: values.map Nat.bits`; `decode` accepts only when the value count is `2 * (entities * reactions)` **and** re-encoding reproduces the input exactly. With `m = entities` and `n = reactions`, `toSource` reads left entries at index `r * m + x` and right entries at `m * n + r * m + x`. | Definition only. Malformed or non-canonical strings are outside the language. |
| Source, admissibility, productivity (manuscript Definition 1) | `ReversibleSource` has literal `left`/`right : Reaction → Entity → ℕ`; `net = right - left` over `ℝ`; `sideAdmissible X r` requires some `e ∈ X` with `0 < left r e` and some `e ∈ X` with `0 < right r e`; `Productive X S` requires a real flow zero outside `S` with `0 < Σ_r net r e * flow r` for every `e ∈ X`. | Definition. Flows may be negative (signed reversible flux). Entities outside `X` are unconstrained. |
| Motif and PAC (inclusion-minimal motif) | `Motif (X,S)`: `X` and `S` nonempty, every `r ∈ S` side-admissible for `X`, and `Productive X S`. `PAC c`: `Motif c ∧ ∀ smaller < c, ¬ Motif smaller`, with `<` the product order on `Finset Entity × Finset Reaction`, i.e. componentwise inclusion with at least one strict inclusion. | Definition; matches the manuscript's componentwise minimality. |
| NP, FP, polynomial many-one reduction | `NP = ⋃ k, NTIME (· ^ k)`; `NTIME T` = languages decided by a multi-tape `NTM` in time `f` with `f =O T`; `DecidesInTime` requires all choice paths to halt within `f(|x|)` and `x ∈ L ↔` some choice path halts with output cell 1 equal to `1`. `FP` = functions computed by a deterministic multi-tape `TM` in time `T =O n^d`. `L ≤ₚ L'` = `∃ f ∈ FP, ∀ x, x ∈ L ↔ f x ∈ L'`. `BigO` is `Asymptotics.IsBigO` at `atTop` on real casts. | Reproduced Complexitylib (Apache-2.0) definitions under their original names; included in the recursive Comparator comparison. |

Supporting results (not selected, in the Solution closure): square-witness
characterization (manuscript Lemma 3; `CoreWitness`, `SquareMinor`),
linkage in both directions, `FormulaLinkage.formula_paths_iff_sat`,
`FormulaPACEncoding.compile_correct`, `FormulaTotalWriter.compile_mem_FP` and
`VerifierNPPolynomial.in_NP` (manuscript formal appendix table).

## Literature correspondence

T. Kosc, D. Kuperberg, E. Rajon and S. Charlat, *Thermodynamic consistency of
autocatalytic cycles*, PNAS 122(18):e2421274122, 2025,
[doi:10.1073/pnas.2421274122](https://doi.org/10.1073/pnas.2421274122). Section 2.1, Definition 3 and Theorem 1 prove NP-completeness for
PAC-DETECTION with a prescribed target entity `A` and allowed-food set `F`; the
paragraph concluding the proof explicitly says that whether the unconstrained
variant is NP-complete remains open.

The entry settles the unconstrained variant for one explicit model: finite
reversible sources given by literal nonnegative integer reactant and product
matrices, signed real flows, and a canonical binary encoding. Deciding whether
such a source contains a productive autocatalytic core is NP-complete; the
reduction is from SAT and is total on all binary strings. It is not a statement
about maximum-RAF detection (Andersen et al. 2012 treat a different
formulation), dynamical realizability, or kinetics.

## Evidence boundary

- Encoding choice: the result is for the stated canonical binary encoding with
  literal left/right matrices. Non-canonical strings are rejected, and a net
  matrix is never substituted for the literal pair.
- Computational model: NP and FP are defined by Complexitylib multi-tape Turing
  machines with a read-only input tape, work tapes and an output tape; the
  selected theorem depends on these definitions matching the proof environment,
  which Comparator must check.
- The theorem imposes no conserved elemental composition, elementary arity,
  concentration bound or kinetic law; a structural YES instance need not be a
  dynamically realizable pathway.
- Proof dependencies: the complete local import closure is included. It contains
  the reduction, verifier, encoding and graph-construction infrastructure,
  together with the selected Complexitylib Cook–Levin development. It does not
  assume acceptance of another submission or an unproved mathematical hardness
  hypothesis.
- Third-party code: the selected Complexitylib modules retain their Apache-2.0
  license and copyright notices. The original revision and local adaptations
  are documented in `proofs/Complexitylib/UPSTREAM.md`.
