import Lake
open Lake DSL

package palomarSubmissions where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "065356127b1dc0016f66b7283ce0ce2c4055aa55"

/- Proof modules retain their original names. Build a selected Solution module
   explicitly; do not eagerly rebuild all selected research developments. -/
lean_lib ResearchProofs where
  roots := #[`proofs]
  globs := #[.submodules `proofs]
  leanOptions := #[⟨`warningAsError, true⟩]

/- Challenges deliberately contain sorry statements for Comparator to discharge
   against the separate Solution environment. Do not import Challenge in Solution. -/
lean_lib RegistryStatements where
  roots := #[`Registry]
  globs := #[.submodules `Registry]
