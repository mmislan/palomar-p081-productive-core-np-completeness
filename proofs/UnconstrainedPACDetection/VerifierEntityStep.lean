module

public import proofs.UnconstrainedPACDetection.VerifierEntityAdvance

@[expose] public section

namespace UnconstrainedPACDetection.VerifierEntityStep
open Complexity Complexity.TM
open VerifierEntityLift (frame)
open VerifierIndexedField (counter)
open VerifierBufferedProduct (wordTape)

def pred (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) (k : ℕ) (a : Bool) :
    Complexity.TM.TapePred 13 := fun inp work out => inp.HasBinarySuffix s.encode ∧
      inp.cells = (wordTape s.encode).cells ∧ work = frame s w (counter k) ∧ out.HasBinaryPrefix [a]

theorem stable (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) (k : ℕ) (a : Bool) :
    ∀ inp work out, pred s w k a inp work out →
      pred s w k a (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out ⟨hi,hcells,hwork,hout⟩
  have ho : out.read ≠ .start := by rw [hout.read_blank]; decide
  have hw : ∀ j, (work j).read ≠ .start := by
    intro j
    rw [hwork]
    exact (VerifierEntityAdvance.frame_safe s w k j).1
  have ht := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start hw ho
  simpa only [ht.1,ht.2.1,ht.2.2] using (show pred s w k a inp work out from ⟨hi,hcells,hwork,hout⟩)

def checked : TM 13 := seqTM VerifierEntityOperation.machine VerifierEntityAdvance.machine

theorem checked_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) (a : Bool) :
    checked.HoareTime (pred s w (2+x.val) a)
      (pred s w (2+x.val+1) (VerifierEntityCheck.verdict s hn x w && a))
      (17000*(VerifierCanonicalBuffers.envelope s w [] []+1)^3+3*s.encode.length+2*x.val+24) := by
  have h := seqTM_hoareTime _ _
    (VerifierEntityOperation.entity_hoare s hs hn x w hw a)
    (stable s w (2+x.val) (VerifierEntityCheck.verdict s hn x w && a))
    (VerifierEntityAdvance.advance_hoare s w (2+x.val) (VerifierEntityCheck.verdict s hn x w && a))
  exact h.mono_bound (by omega)

theorem skipped_hoare (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (k : ℕ) (a : Bool) : VerifierEntityAdvance.machine.HoareTime (pred s w k a)
      (pred s w (k+1) a) (2*k+6) := VerifierEntityAdvance.advance_hoare s w k a

end UnconstrainedPACDetection.VerifierEntityStep
