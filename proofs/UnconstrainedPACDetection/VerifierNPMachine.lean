module

public import proofs.UnconstrainedPACDetection.VerifierNPStart
public import proofs.UnconstrainedPACDetection.VerifierNPGuess
public import proofs.UnconstrainedPACDetection.VerifierNTMSequence

@[expose] public section

namespace UnconstrainedPACDetection.VerifierNPMachine
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def evaluationBudget (N : Nat) : Nat :=
  let W := VerifierNPBound.cap N
  26*N+84*(W+1)^2+14*W+232+256*(2*(W+1)^2+2)^3+
    100*(2*W+1)^2+22000*(N+3*W+2)^4

theorem evaluation_bound (src wit : List Bool) (hw : wit.length ≤ VerifierNPBound.cap src.length) :
    VerifierSeparatedMachine.budget src wit ≤ evaluationBudget src.length := by
  rw [VerifierSeparatedMachine.budget_polynomial]
  dsimp only [evaluationBudget]
  gcongr

theorem before_stable (src wit : List Bool) : ∀ inp work out,
    VerifierNPEvaluate.before src wit inp work out →
    VerifierNPEvaluate.before src wit (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out ⟨hi,hw,ho⟩
  refine ⟨?_,?_,?_⟩
  · rw [hi]; exact transitionInput_eq_self (word_parked src).read_ne_start
  · intro j
    change transitionTape (work (placeWorkIdx 0 3 j)) = VerifierRawStage.initialWork wit j
    rw [hw]
    apply transitionTape_eq_self
    dsimp only [VerifierRawStage.initialWork]
    split
    · exact (word_parked wit).read_ne_start
    · exact (word_parked []).read_ne_start
  · rw [transitionTape_eq_self ho.parked.read_ne_start]; exact ho

theorem after_stable (src : List Bool) : ∀ inp work out,
    VerifierNPGuess.after src inp work out →
    VerifierNPGuess.after src (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out ⟨wit,hlen,h⟩
  exact ⟨wit,hlen,before_stable src wit inp work out h⟩

def post (src : List Bool) : NTM.TapePred 33 := fun _ _ out =>
  ∃ wit, wit.length ≤ VerifierNPBound.cap src.length ∧
    OutAcc [BinaryIntegerVerifier.verify src wit] out

theorem evaluation_hoare (src : List Bool) : VerifierNPEvaluate.machine.toNTM.HoareTime
    (VerifierNPGuess.after src) (post src) (evaluationBudget src.length) := by
  rintro inp work out ⟨wit,hlen,h⟩ choices
  have he := ((VerifierNPEvaluate.evaluate_hoare src wit).mono_bound
    (evaluation_bound src wit hlen)).toNTM inp work out h choices
  exact ⟨he.1,wit,hlen,he.2⟩

def guessVerify : NTM 33 := VerifierNTMSequence.machine VerifierNPGuess.machine
  VerifierNPEvaluate.machine.toNTM
def guessVerifyBound (N : Nat) : Nat := VerifierNPGuess.bound N+1+evaluationBudget N

theorem guessVerify_hoare (src : List Bool) : guessVerify.HoareTime
    (EmitPred (word src) (VerifierNPPrepare.preparedWork src.length) [])
    (post src) (guessVerifyBound src.length) :=
  VerifierNTMSequence.hoare _ _ (VerifierNPGuess.guess_hoare src)
    (evaluation_hoare src) (after_stable src)

def machine : NTM 33 := VerifierNTMSequence.machine VerifierNPStart.machine.toNTM guessVerify
def bound (N : Nat) : Nat := VerifierNPStart.bound N+1+guessVerifyBound N

theorem verification_hoare (src : List Bool) : machine.HoareTime
    (VerifierNPStart.initial src) (post src) (bound src.length) :=
  VerifierNTMSequence.hoare _ _ (VerifierNPStart.setup_hoare src).toNTM
    (guessVerify_hoare src)
    (emitPred_transition (word_parked src) (VerifierNPPrepare.prepared_parked src.length) [])

theorem hoareTime_post {n : Nat} (M : NTM n) {pre post : NTM.TapePred n}
    {T : Nat} (h : M.HoareTime pre post T) (inp : Tape)
    (work : Fin n → Tape) (out : Tape) (hpre : pre inp work out)
    (choices : Fin T → Bool) :
    let d := M.trace T choices ⟨M.qstart,inp,work,out⟩
    post d.input d.work d.output :=
  (h inp work out hpre choices).2

theorem hoareTime_post_initCfg {n : Nat} (M : NTM n) (T : Nat → Nat)
    (pre post : List Bool → NTM.TapePred n)
    (h : ∀ src, M.HoareTime (pre src) (post src) (T src.length))
    (hinit : ∀ src, pre src (M.initCfg src).input
      (M.initCfg src).work (M.initCfg src).output)
    (src : List Bool) (choices : Fin (T src.length) → Bool) :
    let d := M.trace (T src.length) choices (M.initCfg src)
    post src d.input d.work d.output :=
  (h src _ _ _ (hinit src) choices).2

theorem initial_at_init (src : List Bool) :
    VerifierNPStart.initial src (machine.initCfg src).input
      (machine.initCfg src).work (machine.initCfg src).output :=
  ⟨rfl,rfl,rfl⟩

theorem verification_outputs (src : List Bool)
    (choices : Fin (bound src.length) → Bool) :
    let d := machine.trace (bound src.length) choices (machine.initCfg src)
    post src d.input d.work d.output :=
  hoareTime_post_initCfg machine bound (fun src => VerifierNPStart.initial src)
    post verification_hoare initial_at_init src choices

theorem allPathsHaltIn_of_hoareTime {n : Nat} (tm : NTM n) (T : Nat → Nat)
    (pre post : List Bool → NTM.TapePred n)
    (h : ∀ src, tm.HoareTime (pre src) (post src) (T src.length))
    (hinit : ∀ src, pre src (tm.initCfg src).input
      (tm.initCfg src).work (tm.initCfg src).output) :
    tm.AllPathsHaltIn T := by
  intro src choices
  exact (h src _ _ _ (hinit src) choices).1

theorem all_paths_halt : machine.AllPathsHaltIn bound := by
  exact allPathsHaltIn_of_hoareTime machine bound
    (fun src => VerifierNPStart.initial src) post verification_hoare initial_at_init

attribute [local irreducible] VerifierNPStart.machine VerifierNPGuess.machine
  VerifierNPEvaluate.machine VerifierNPStart.bound VerifierNPGuess.bound
  evaluationBudget machine bound NTM.trace

theorem decides_of_generates
    (generates : ∀ src wit, wit.length ≤ VerifierNPBound.cap src.length →
      ∃ choices : Fin (bound src.length) → Bool,
        let d := machine.trace (bound src.length) choices (machine.initCfg src)
        machine.halted d ∧ OutAcc [BinaryIntegerVerifier.verify src wit] d.output) :
    machine.DecidesInTime BinaryIntegerVerifier.language bound :=
  OutAcc.decides_of_verifier machine bound VerifierNPBound.cap BinaryIntegerVerifier.verify
    BinaryIntegerVerifier.language BinaryIntegerVerifier.language_iff_short_verified
    (fun _ _ h => BinaryIntegerVerifier.verify_sound h) all_paths_halt generates
    (fun src choices => verification_outputs src choices)

end UnconstrainedPACDetection.VerifierNPMachine
