module

public import proofs.UnconstrainedPACDetection.VerifierNPMachine

@[expose] public section

namespace UnconstrainedPACDetection.VerifierNPAcceptance
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)
open VerifierNPMachine

attribute [local irreducible] VerifierNPStart.machine VerifierNPGuess.machine
  VerifierNPEvaluate.machine
attribute [local irreducible] VerifierNPStart.bound VerifierNPGuess.bound evaluationBudget
attribute [local irreducible] NTM.trace

set_option maxHeartbeats 10000

theorem existsRun_transport {n : Nat} (M M' : NTM n) (T T' : Nat)
    (hM : M = M') (hT : T = T') (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (R : Tape → Prop)
    (h : ∃ choices : Fin T' → Bool,
      let d := M'.trace T' choices ⟨M'.qstart,inp,work,out⟩
      M'.halted d ∧ R d.output) :
    ∃ choices : Fin T → Bool,
      let d := M.trace T choices ⟨M.qstart,inp,work,out⟩
      M.halted d ∧ R d.output := by
  subst M'
  subst T'
  exact h

theorem existsRun_initCfg {n : Nat} (M : NTM n) (T : Nat) (src : List Bool)
    (R : Tape → Prop)
    (h : ∃ choices : Fin T → Bool,
      let d := M.trace T choices
        ⟨M.qstart,Tape.init (src.map Γ.ofBool),fun _ : Fin n => Tape.init [],Tape.init []⟩
      M.halted d ∧ R d.output) :
    ∃ choices : Fin T → Bool,
      let d := M.trace T choices (M.initCfg src)
      M.halted d ∧ R d.output :=
  h

theorem guessEvaluate_specified_witness_raw (src wit : List Bool)
    (hlen : wit.length ≤ VerifierNPBound.cap src.length) :
    ∃ choices : Fin (VerifierNPGuess.bound src.length + 1 + evaluationBudget src.length) → Bool,
      let d := (VerifierNTMSequence.machine VerifierNPGuess.machine
        VerifierNPEvaluate.machine.toNTM).trace
          (VerifierNPGuess.bound src.length + 1 + evaluationBudget src.length) choices
          ⟨(VerifierNTMSequence.machine VerifierNPGuess.machine
            VerifierNPEvaluate.machine.toNTM).qstart,word src,
            VerifierNPPrepare.preparedWork src.length,word []⟩
      (VerifierNTMSequence.machine VerifierNPGuess.machine
        VerifierNPEvaluate.machine.toNTM).halted d ∧
        OutAcc [BinaryIntegerVerifier.verify src wit] d.output := by
  obtain ⟨cg,hg,hbefore⟩ := VerifierNPGuess.generates src wit hlen
  exact VerifierNTMSequence.chosen_tail_init VerifierNPGuess.machine
    VerifierNPEvaluate.machine.toNTM (VerifierNPGuess.bound src.length)
    (evaluationBudget src.length) cg (word src)
    (VerifierNPPrepare.preparedWork src.length) (word [])
    (Q := VerifierNPEvaluate.before src wit)
    (R := fun _ _ out => OutAcc [BinaryIntegerVerifier.verify src wit] out) hg hbefore
    ((VerifierNPEvaluate.evaluate_hoare src wit).mono_bound
      (evaluation_bound src wit hlen)).toNTM (before_stable src wit)

theorem guessVerify_specified_witness (src wit : List Bool)
    (hlen : wit.length ≤ VerifierNPBound.cap src.length) :
    ∃ choices : Fin (guessVerifyBound src.length) → Bool,
      let d := guessVerify.trace (guessVerifyBound src.length) choices
        ⟨guessVerify.qstart,word src,VerifierNPPrepare.preparedWork src.length,word []⟩
      guessVerify.halted d ∧ OutAcc [BinaryIntegerVerifier.verify src wit] d.output :=
  existsRun_transport guessVerify
    (VerifierNTMSequence.machine VerifierNPGuess.machine VerifierNPEvaluate.machine.toNTM)
    (guessVerifyBound src.length)
    (VerifierNPGuess.bound src.length + 1 + evaluationBudget src.length)
    rfl rfl (word src) (VerifierNPPrepare.preparedWork src.length) (word [])
    (fun out => OutAcc [BinaryIntegerVerifier.verify src wit] out)
    (guessEvaluate_specified_witness_raw src wit hlen)

theorem setup_exact (src : List Bool) :
    VerifierNPStart.machine.toNTM.HoareTime (VerifierNPStart.initial src)
      (fun inp work out => inp = word src ∧
        work = VerifierNPPrepare.preparedWork src.length ∧ out = word [])
      (VerifierNPStart.bound src.length) :=
  (VerifierNPStart.setup_hoare src).toNTM.strengthen_post
    (fun inp work out h => show inp = word src ∧
        work = VerifierNPPrepare.preparedWork src.length ∧ out = word [] from
      ⟨h.1,h.2.1,h.2.2.eq outAcc_nil_init⟩)

theorem specified_witness_raw (src wit : List Bool)
    (hlen : wit.length ≤ VerifierNPBound.cap src.length) :
    ∃ choices : Fin (VerifierNPStart.bound src.length + 1 + guessVerifyBound src.length) → Bool,
      let outer := VerifierNTMSequence.machine VerifierNPStart.machine.toNTM guessVerify
      let d := outer.trace
        (VerifierNPStart.bound src.length + 1 + guessVerifyBound src.length) choices
        ⟨outer.qstart,Tape.init (src.map Γ.ofBool),
          fun _ : Fin 33 => Tape.init [],Tape.init []⟩
      outer.halted d ∧ OutAcc [BinaryIntegerVerifier.verify src wit] d.output := by
  exact VerifierNTMSequence.prefix_fixed VerifierNPStart.machine.toNTM guessVerify
    (VerifierNPStart.bound src.length) (guessVerifyBound src.length)
    (Tape.init (src.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
    (word src) (VerifierNPPrepare.preparedWork src.length) (word [])
    (P := VerifierNPStart.initial src)
    (R := fun _ _ out => OutAcc [BinaryIntegerVerifier.verify src wit] out)
    ⟨rfl,rfl,rfl⟩ (setup_exact src)
    (transitionInput_eq_self (word_parked src).read_ne_start)
    (funext (fun j => transitionTape_eq_self
      (VerifierNPPrepare.prepared_parked src.length j).read_ne_start))
    (transitionTape_eq_self (word_parked []).read_ne_start)
    (guessVerify_specified_witness src wit hlen)

theorem specified_witness (src wit : List Bool)
    (hlen : wit.length ≤ VerifierNPBound.cap src.length) :
    ∃ choices : Fin (bound src.length) → Bool,
      let d := machine.trace (bound src.length) choices (machine.initCfg src)
      machine.halted d ∧ OutAcc [BinaryIntegerVerifier.verify src wit] d.output :=
  existsRun_initCfg machine (bound src.length) src
    (fun out => OutAcc [BinaryIntegerVerifier.verify src wit] out)
    (existsRun_transport machine
      (VerifierNTMSequence.machine VerifierNPStart.machine.toNTM guessVerify)
      (bound src.length)
      (VerifierNPStart.bound src.length + 1 + guessVerifyBound src.length)
      rfl rfl (Tape.init (src.map Γ.ofBool)) (fun _ : Fin 33 => Tape.init [])
      (Tape.init []) (fun out => OutAcc [BinaryIntegerVerifier.verify src wit] out)
      (specified_witness_raw src wit hlen))

theorem decides : machine.DecidesInTime BinaryIntegerVerifier.language bound :=
  decides_of_generates specified_witness

end UnconstrainedPACDetection.VerifierNPAcceptance
