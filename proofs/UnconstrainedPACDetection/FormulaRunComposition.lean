module

public import proofs.UnconstrainedPACDetection.FormulaValidWriter
public import proofs.Complexitylib.Models.TuringMachine.Composition.Internal

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRunComposition
open Complexity Complexity.TM

def Run {n : Nat} (M : TM n) (x y : List Bool) (B : Nat) : Prop :=
  ∃ d t, t≤B ∧ M.reachesIn t (M.initCfg x) d ∧ M.halted d ∧ d.output.HasOutput y

theorem virtual_run {n : Nat} (M : TM n) (x y : List Bool) (B : Nat)
    (hne : M.qstart≠M.qhalt) (h : Run M x y B) (realInput : Tape) :
    ∃ d t, t≤B ∧ (retargetInputStarted M).reachesIn t (retargetInputStartedCfg M x realInput) d ∧
      (retargetInputStarted M).halted d ∧ d.output.HasOutput y := by
  obtain ⟨d,t,ht,hr,hh,ho⟩ := h
  have hn : t≠0 := by intro he; subst t; cases hr; exact hne hh
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  cases hr with
  | step hs rest =>
    next c =>
      have hc : c=startedCfg M x hne := by
        have he : some c=some (startedCfg M x hne) := by rw [← hs,step_initCfg_startedCfg M x hne]
        exact Option.some.inj he
      subst c
      obtain ⟨hinv,hw,hoinv⟩ := Tape.StartInvariant.step M (step_initCfg_startedCfg M x hne)
        (Tape.StartInvariant.init_ofBool x) (fun _ => Tape.StartInvariant.init_nil) Tape.StartInvariant.init_nil
      obtain ⟨finalReal,hr'⟩ := retargetInput_reachesIn_of_reachesIn M rest hinv hw hoinv realInput
      refine ⟨retargetWrap M finalReal d,u,by omega,?_,hh,ho⟩
      rw [retargetInputStartedCfg_eq_retargetWrap_internal M x realInput hne]
      exact retargetInputStarted_reachesIn_of_retargetInput_internal M hr'

theorem compose {nf ng : Nat} (F : TM nf) (G : TM ng) (x y z : List Bool) (A B : Nat)
    (hF : Run F x y A) (hG : Run G y z B) (hne : G.qstart≠G.qhalt) :
    Run (compositionTM F G) x z (2*A+2*y.length+B+11) := by
  obtain ⟨C,t,ht,hrF,hhF,hraw,hhead,hvirtual,hscratch,hinv,hinputHead,hw,hout⟩ :=
    compositionFirstTM_boundary_of_run_internal F ng x y A hF
  let boundaryInput := transitionInput C.input
  let boundaryWork := fun i => transitionTape (C.work i)
  let boundaryOutput := transitionTape C.output
  have htail := compositionTailTM_hoareTime_of_virtualRun_internal (nf := nf) G (G := fun _ => B)
    y (A+1) (fun out => out.HasOutput z) (virtual_run G y z B hne hG)
  obtain ⟨D,u,hu,hrTail,hhTail,hoTail⟩ := htail boundaryInput boundaryWork boundaryOutput (by
    refine ⟨hraw,(hw _).1,?_,hvirtual,hscratch,hout,hinv,hinputHead,?_⟩
    · dsimp only [boundaryWork]; omega
    · intro i; exact hw (compositionPrefixIdx nf ng i))
  let first := compositionFirstTM F ng
  let tail := compositionTailTM nf ng G
  let final := phase2Wrap first tail D
  refine ⟨final,t+1+u,by omega,?_,?_,?_⟩
  · have h := seqTM_reachesIn_of_reachesIn first tail hrF hhF hrTail
    have hstart : (compositionTM F G).initCfg x = phase1Wrap first tail (first.initCfg x) := by rfl
    rw [hstart]
    exact h
  · simpa [compositionTM,first,tail,final] using (phase2Wrap_halted_iff first tail D).2 hhTail
  · simpa [final,phase2Wrap] using hoTail

end UnconstrainedPACDetection.FormulaRunComposition
