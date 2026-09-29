Selected dependency closure from SamuelSchlesinger/complexitylib.
Immutable commit: 43d4bb1a30bd93846eab5480bec8a37113586109.
Lean 4.30.0; mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f.
Source files retain upstream copyright and Apache-2.0 notices.
Only modules in the selected dependency closure are included.

Local toolchain adaptations (target Lean v4.35.0-rc2,
mathlib 065356127b1d): Asymptotics.lean adds `import Mathlib.Algebra.Polynomial.Eval.Degree`
(home of `Polynomial.natDegree`/`eval_eq_sum_range` after the Mathlib split);
SAT/CookLevin.lean `atMostOne_unique` uses a local `Std.Symm` instance instead of the
deprecated `Symmetric`; Models/TuringMachine/SingleTape/Internal/Sim.lean imports
`Mathlib.Basic.Finite.{Prod,Sum}` (replacements of deprecated modules); plus the central
`if_false -> ite_false` / `Set.diff_eq -> Set.sdiff_eq` renames. Statements are unchanged.

The release uses Lean module headers, public imports and exposed public sections.
Original copyright headers and declaration bodies are retained.
