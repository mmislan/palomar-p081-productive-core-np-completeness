module

public import proofs.UnconstrainedPACDetection.VerifierNonemptyCheck

@[expose] public section

namespace UnconstrainedPACDetection.VerifierActivationNonempty
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierActivationProduce (frame)

def result (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) : Bool :=
  VerifierFlowBothSource.result s w && w.mask.any id

theorem frame_off (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (inp : Tape) (work : Fin 4 → Tape) (out : Tape) (h : VerifierActivationDock.final s w inp work out) :
    ∀ j, (work j).read ≠ .start := by
  rcases h with ⟨_,h0,h3,hf,_⟩
  intro j
  by_cases hj0 : j = 0
  · subst j; rw [h0]; exact VerifierFlowPassHoare.ended_off _
  by_cases hj3 : j = 3
  · subst j; rw [h3]
    exact ((Tape.StartInvariant.init_ofBool (VerifierActivationSource.flags s w)).move .right).2
      (1+2*s.reactions) (by omega)
  rw [hf j hj0 hj3]
  exact (VerifierActivationProduce.frame_parked s w _ (VerifierReactionLoop.word_parked _) j).read_ne_start

def final (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) : Complexity.TM.TapePred 4 :=
  fun inp work out => inp.HasBinarySuffix [] ∧
    work 0 = VerifierFlowRestart.flowInput w.mask (VerifierFlowBothSource.flowWire w) ∧
    work 3 = VerifierFlowPassHoare.advance (wordTape (VerifierActivationSource.flags s w)) (2*s.reactions) ∧
    (∀ j, j ≠ 0 → j ≠ 3 → work j = frame s w (wordTape (VerifierActivationSource.flags s w)) j) ∧
    out = one .start (result s w)

def machine : TM 4 := seqTM VerifierActivationDock.machine VerifierNonemptyCheck.machine

theorem check_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (w : BinaryWitnessData.Witness) (hm : w.mask.length = s.entities) (hw : w.flow.length = s.reactions) :
    machine.HoareTime
      (fun inp work out => inp.HasBinarySuffix (BinaryFields.encode (s.values.map Nat.bits)) ∧
        work = frame s w (wordTape []) ∧ out = wordTape [])
      (final s w) (50*(s.encode.length+2*w.encode.length+1)^2) := by
  have stable : ∀ inp work out, VerifierActivationDock.final s w inp work out →
      VerifierActivationDock.final s w (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
    intro inp work out hp
    have ho : out.read ≠ .start := by rw [hp.2.2.2.2]; change Γ.blank ≠ Γ.start; decide
    obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hp.1.read_ne_start
      (frame_off s w inp work out hp) ho
    simpa only [hi',hw',ho'] using hp
  have second : VerifierNonemptyCheck.machine.HoareTime (VerifierActivationDock.final s w)
      (final s w) (2*w.encode.length+6) := by
    intro inp work out hp
    have hoff := frame_off s w inp work out hp
    rcases hp with ⟨hi,h0,h3,hf,hout⟩
    subst out
    obtain ⟨d,t,ht,hd,hh,hdi,hd0,hdf,hdo⟩ := VerifierNonemptyCheck.check_hoare w work inp
      (VerifierFlowBothSource.result s w) h0 hoff hi.read_ne_start _ _ _ ⟨rfl,rfl,rfl⟩
    refine ⟨d,t,ht,hd,hh,by rwa [hdi],hd0,?_,?_,hdo⟩
    · rw [hdf 3 (by decide)]; exact h3
    · intro j hj0 hj3; rw [hdf j hj0]; exact hf j hj0 hj3
  have h := seqTM_hoareTime _ _ (VerifierActivationDock.activation_hoare s hs w hm hw) stable second
  apply h.mono_bound
  let X := s.encode.length+2*w.encode.length+1
  have hx : 2*w.encode.length+1 ≤ X := by dsimp [X]; omega
  have hsq : X ≤ X^2 := by nlinarith
  change 40*X^2+1+(2*w.encode.length+6) ≤ 50*X^2
  nlinarith

theorem result_iff (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (hm : w.mask.length = s.entities) : result s w = true ↔
      (w.entities s.entities).Nonempty ∧
        ∀ r, w.values s.reactions r ≠ 0 → s.toSource.sideAdmissible (w.entities s.entities) r := by
  rw [result,Bool.and_eq_true,VerifierMaskNonemptyRouting.selected_iff w s.entities hm,
    VerifierFlowBothSource.result_iff]
  exact and_comm

theorem certificate_iff (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (w : BinaryWitnessData.Witness) (hm : w.mask.length = s.entities) :
    VerifierEntityOuterLoop.accumulator s hn w (result s w) s.entities = true ↔
      s.toSource.IntegerFlowChecks (w.entities s.entities) (w.values s.reactions) := by
  have ha : VerifierEntityOuterLoop.accumulator s hn w (result s w) s.entities = true ↔
      result s w = true ∧ VerifierEntityOuterLoop.accumulator s hn w true s.entities = true := by
    simp only [VerifierEntityOuterLoop.accumulator_true_iff,true_and]
  rw [ha,result_iff s w hm,VerifierEntityOuterSemantics.positive_iff]
  simp only [ReversibleSource.IntegerFlowChecks,and_assoc]

end UnconstrainedPACDetection.VerifierActivationNonempty
