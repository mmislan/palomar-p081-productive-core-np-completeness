module

public import proofs.UnconstrainedPACDetection.MixedColumns
public import proofs.UnconstrainedPACDetection.SquareMinor

@[expose] public section

/-!
# Mixed nonsingular minors

For a nonambiguous reversible source, literal two-sided admissibility is
exactly the statement that the restricted net column contains a negative and
a positive entry.  Consequently unconstrained PAC existence is exactly the
existence of a nonempty nonsingular square submatrix all of whose selected
columns are mixed-sign.
-/

namespace UnconstrainedPACDetection

variable {Entity Reaction : Type*}
  [Fintype Entity] [DecidableEq Entity]
  [Fintype Reaction] [DecidableEq Reaction]

def ReversibleSource.MixedSquareMinor
    (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) : Prop :=
  candidate.1.Nonempty ∧
    candidate.2.Nonempty ∧
    (∀ reaction ∈ candidate.2,
      (∃ entity ∈ candidate.1, source.net reaction entity < 0) ∧
        ∃ entity ∈ candidate.1, 0 < source.net reaction entity) ∧
    candidate.1.card = candidate.2.card ∧
    LinearIndependent ℝ (fun reaction : ↥candidate.2 =>
      fun entity : ↥candidate.1 => source.net reaction.1 entity.1)

omit [Fintype Entity] [Fintype Reaction] [DecidableEq Reaction] in
theorem squareMinor_iff_mixedSquareMinor
    (source : ReversibleSource Entity Reaction)
    (hNA : source.Nonambiguous)
    (candidate : Candidate Entity Reaction) :
    source.SquareMinor candidate ↔ source.MixedSquareMinor candidate := by
  simp only [ReversibleSource.SquareMinor,
    ReversibleSource.MixedSquareMinor]
  constructor
  · rintro ⟨hentities, hreactions, hadmissible, hcard, hindependent⟩
    exact ⟨hentities, hreactions, fun reaction hreaction =>
      (source.sideAdmissible_iff_mixed hNA candidate.1 reaction).1
        (hadmissible reaction hreaction), hcard, hindependent⟩
  · rintro ⟨hentities, hreactions, hmixed, hcard, hindependent⟩
    exact ⟨hentities, hreactions, fun reaction hreaction =>
      (source.sideAdmissible_iff_mixed hNA candidate.1 reaction).2
        (hmixed reaction hreaction), hcard, hindependent⟩

theorem exists_pac_iff_exists_mixedSquareMinor
    (source : ReversibleSource Entity Reaction)
    (hNA : source.Nonambiguous) :
    (∃ candidate, source.PAC candidate) ↔
      ∃ candidate, source.MixedSquareMinor candidate := by
  rw [exists_pac_iff_exists_squareMinor source]
  apply exists_congr
  exact squareMinor_iff_mixedSquareMinor source hNA

/-! Every integer matrix is the net matrix of a literal nonambiguous source. -/

def integerMatrixSource
    (matrix : Reaction → Entity → ℤ) : ReversibleSource Entity Reaction where
  left reaction entity := Int.toNat (-matrix reaction entity)
  right reaction entity := Int.toNat (matrix reaction entity)

omit [Fintype Entity] [DecidableEq Entity]
    [Fintype Reaction] [DecidableEq Reaction] in
theorem integerMatrixSource_net
    (matrix : Reaction → Entity → ℤ)
    (reaction : Reaction) (entity : Entity) :
    (integerMatrixSource matrix).net reaction entity =
      (matrix reaction entity : ℝ) := by
  rcases hentry : matrix reaction entity with n | n
  · simp [integerMatrixSource, ReversibleSource.net, hentry]
  · simp [integerMatrixSource, ReversibleSource.net, hentry]

omit [Fintype Entity] [DecidableEq Entity]
    [Fintype Reaction] [DecidableEq Reaction] in
theorem integerMatrixSource_nonambiguous
    (matrix : Reaction → Entity → ℤ) :
    (integerMatrixSource matrix).Nonambiguous := by
  intro reaction entity
  rcases hentry : matrix reaction entity with n | n
  · simp [integerMatrixSource, hentry]
  · simp [integerMatrixSource, hentry]

#print axioms UnconstrainedPACDetection.squareMinor_iff_mixedSquareMinor
#print axioms UnconstrainedPACDetection.exists_pac_iff_exists_mixedSquareMinor
#print axioms UnconstrainedPACDetection.integerMatrixSource_net
#print axioms UnconstrainedPACDetection.integerMatrixSource_nonambiguous

end UnconstrainedPACDetection
