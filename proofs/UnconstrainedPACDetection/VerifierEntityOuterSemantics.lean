module

public import proofs.UnconstrainedPACDetection.VerifierEntityOuterBudget

@[expose] public section

namespace UnconstrainedPACDetection.VerifierEntityOuterSemantics
open VerifierCanonicalCoordinates (coefficient)
open VerifierCanonicalLoop (reaction)

theorem net_sum (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (w : BinaryWitnessData.Witness) (x : Fin s.entities) :
    (∑ j ∈ Finset.range s.reactions,
      ((coefficient s true (reaction s hn j) x : ℤ)-coefficient s false (reaction s hn j) x)*
        VerifierCanonicalContribution.flow w j) =
    ∑ r, s.toSource.netInt r x * w.values s.reactions r := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  have he : reaction s hn r.val = r := Fin.ext (VerifierCanonicalLoop.reaction_val s hn r.val r.isLt)
  simp [he,coefficient,VerifierCanonicalContribution.flow,BinaryWitnessData.Witness.values,
    ReversibleSource.netInt]

theorem verdict_iff (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (w : BinaryWitnessData.Witness) (x : Fin s.entities) :
    VerifierEntityCheck.verdict s hn x w = true ↔
      0 < ∑ r, s.toSource.netInt r x * w.values s.reactions r := by
  rw [VerifierEntityCheck.verdict_iff,net_sum]

/-- The actual outer machine's accumulated bit is exactly the productivity
clause of the existing source-faithful integer-flow certificate checker. -/
theorem positive_iff (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (w : BinaryWitnessData.Witness) :
    VerifierEntityOuterLoop.accumulator s hn w true s.entities = true ↔
      ∀ x ∈ w.entities s.entities, 0 < ∑ r, s.toSource.netInt r x * w.values s.reactions r := by
  rw [VerifierEntityOuterLoop.selected_verdicts_iff]
  simp only [BinaryWitnessData.Witness.entities,Finset.mem_filter,Finset.mem_univ,true_and]
  simp_rw [verdict_iff]

theorem integerFlowChecks_iff (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (w : BinaryWitnessData.Witness) :
    s.toSource.IntegerFlowChecks (w.entities s.entities) (w.values s.reactions) ↔
      (w.entities s.entities).Nonempty ∧
      (∀ r, w.values s.reactions r ≠ 0 → s.toSource.sideAdmissible (w.entities s.entities) r) ∧
      VerifierEntityOuterLoop.accumulator s hn w true s.entities = true := by
  rw [ReversibleSource.IntegerFlowChecks,positive_iff]

end UnconstrainedPACDetection.VerifierEntityOuterSemantics
