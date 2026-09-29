module

public import proofs.UnconstrainedPACDetection.VerifierActivationProduce

@[expose] public section

namespace UnconstrainedPACDetection.VerifierActivationDock
open Complexity Complexity.TM
open VerifierActivationProduce (frame)
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierFlowPassHoare (ended advance)

def stage (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) (ft out₀ : Tape) : Complexity.TM.TapePred 4 :=
  fun inp work out => inp.HasBinarySuffix [] ∧ work = frame s w ft ∧ out = out₀

theorem stable (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) (ft out₀ : Tape)
    (hf : Parked ft) (ho : out₀.read ≠ .start) :
    ∀ inp work out, stage s w ft out₀ inp work out → stage s w ft out₀
      (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out ⟨hi,hw,hout⟩
  subst work; subst out
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start
    (fun j => (VerifierActivationProduce.frame_parked s w ft hf j).read_ne_start) ho
  exact ⟨by rwa [hi'],hw',ho'⟩

theorem seed_hoare (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) :
    (emitBitsTM (n := 4) [true]).HoareTime
      (stage s w (wordTape (VerifierActivationSource.flags s w)) (wordTape []))
      (stage s w (wordTape (VerifierActivationSource.flags s w)) (one .start true)) 1 := by
  rintro inp work out ⟨hi,hw,hout⟩
  subst work; subst out
  obtain ⟨d,hd,hh,hdi,hdw,hdo⟩ := emitBitsTM_reachesIn_frame [true] inp
    (frame s w (wordTape (VerifierActivationSource.flags s w))) (wordTape []) []
    ⟨hi.1,hi.2.2.2⟩
    (VerifierActivationProduce.frame_parked s w _ (VerifierReactionLoop.word_parked _)) outAcc_nil_init
  refine ⟨d,1,le_rfl,hd,hh,by rwa [hdi],hdw,?_⟩
  rw [VerifierVerdictAnd.prefix_eq d.output true (VerifierEntityLoopBody.prefix_of_acc _ _ hdo),hdo.2.1]

def final (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) : Complexity.TM.TapePred 4 :=
  fun inp work out => inp.HasBinarySuffix [] ∧
    work 0 = ended w.encode ∧
    work 3 = advance (wordTape (VerifierActivationSource.flags s w)) (2*s.reactions) ∧
    (∀ j, j ≠ 0 → j ≠ 3 → work j = frame s w (wordTape (VerifierActivationSource.flags s w)) j) ∧
    out = one .start (VerifierFlowBothSource.result s w)

def machine : TM 4 := seqTM VerifierActivationProduce.machine
  (seqTM VerifierActivationProduce.rewind (seqTM (emitBitsTM [true]) VerifierFlowRouting.machine))

theorem activation_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (w : BinaryWitnessData.Witness) (hm : w.mask.length = s.entities) (hw : w.flow.length = s.reactions) :
    machine.HoareTime
      (fun inp work out => inp.HasBinarySuffix (BinaryFields.encode (s.values.map Nat.bits)) ∧
        work = frame s w (wordTape []) ∧ out = wordTape [])
      (final s w) (40*(s.encode.length+2*w.encode.length+1)^2) := by
  let fs := VerifierActivationSource.flags s w
  have hblank : (wordTape []).read ≠ .start := (Tape.init_move_right_hasBinaryString _).hasBinarySuffix.read_ne_start
  have hone : (one .start true).read ≠ .start := by change Γ.blank ≠ Γ.start; decide
  have hend : Parked (ended fs) := ⟨by change 1 ≤ fs.length+1; omega,
    ((Tape.StartInvariant.init_ofBool fs).move .right).2⟩
  have rewind : VerifierActivationProduce.rewind.HoareTime
      (stage s w (ended fs) (wordTape [])) (stage s w (wordTape fs) (wordTape [])) (fs.length+3) := by
    rintro inp work out ⟨hi,hwork,hout⟩
    subst work; subst out
    obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := VerifierActivationProduce.rewind_hoare s w inp hi.read_ne_start
      _ _ _ ⟨rfl,rfl,rfl⟩
    exact ⟨d,t,ht,hd,hh,by rwa [hdi],hdw,hdo⟩
  have consume : VerifierFlowRouting.machine.HoareTime
      (stage s w (wordTape fs) (one .start true)) (final s w) (6*w.encode.length+12) := by
    rintro inp work out ⟨hi,hwork,hout⟩
    subst work; subst out
    obtain ⟨d,t,ht,hd,hh,hdi,hd0,hd3,hdf,hdo⟩ := VerifierFlowRouting.check_hoare s w hw
      (frame s w (wordTape fs)) inp rfl rfl
      (fun j => (VerifierActivationProduce.frame_parked s w _ (VerifierReactionLoop.word_parked _) j).read_ne_start)
      hi.read_ne_start _ _ _ ⟨rfl,rfl,rfl⟩
    exact ⟨d,t,ht,hd,hh,by rwa [hdi],hd0,hd3,hdf,hdo⟩
  have htail := seqTM_hoareTime _ _ (seed_hoare s w)
    (stable s w (wordTape fs) (one .start true) (VerifierReactionLoop.word_parked _) hone) consume
  have hmid := seqTM_hoareTime _ _ rewind
    (stable s w (wordTape fs) (wordTape []) (VerifierReactionLoop.word_parked _) hblank) htail
  have h := seqTM_hoareTime _ _ (VerifierActivationProduce.produce_hoare s hs w hm hw)
    (stable s w (ended fs) (wordTape []) hend hblank) hmid
  apply h.mono_bound
  have hc := BinaryWireBounds.field_count_le (w.mask :: w.flow.map BinaryFields.writeInt)
  simp only [List.length_cons,List.length_map] at hc
  change w.flow.length+1 ≤ w.encode.length at hc
  have hlen : fs.length = 2*s.reactions := by simp [fs,VerifierActivationSource.flags]; omega
  have hcount : fs.length ≤ 2*w.encode.length := by omega
  let X := s.encode.length+2*w.encode.length+1
  have hx : 2*w.encode.length+1 ≤ X := by dsimp [X]; omega
  have hsq : X ≤ X^2 := by nlinarith
  change 20*X^2+1+(fs.length+3+1+(1+1+(6*w.encode.length+12))) ≤ 40*X^2
  nlinarith

end UnconstrainedPACDetection.VerifierActivationDock
