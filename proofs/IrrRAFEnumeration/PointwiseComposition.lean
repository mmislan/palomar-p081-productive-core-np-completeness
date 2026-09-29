module

public import proofs.Complexitylib.Models.TuringMachine.Composition.Internal.FirstPhase
public import proofs.Complexitylib.Models.TuringMachine.Composition.Internal.Tail

@[expose] public section

namespace IrrRAFEnumeration.PointwiseComposition
open Complexity Complexity.TM

theorem virtual_run {ng : Nat} (tm : TM ng) (hne : tm.qstart ≠ tm.qhalt)
    (y z : List Bool) (U : Nat)
    (hrun : ∃ c t, t ≤ U ∧ tm.reachesIn t (tm.initCfg y) c ∧ tm.halted c ∧ c.output.HasOutput z)
    (realInput : Tape) :
    ∃ c t, t ≤ U ∧ (retargetInputStarted tm).reachesIn t
      (retargetInputStartedCfg tm y realInput) c ∧
      (retargetInputStarted tm).halted c ∧ c.output.HasOutput z := by
  obtain ⟨c,t,ht,hr,hh,ho⟩ := hrun
  have ht0 : t ≠ 0 := by
    intro he
    subst t
    cases hr
    exact hne hh
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht0
  cases hr with
  | step hs hr =>
    next mid =>
      have hm : mid = startedCfg tm y hne := by
        apply Option.some.inj
        rw [← hs,step_initCfg_startedCfg tm y hne]
      subst mid
      obtain ⟨hi,hw,hout⟩ := Tape.StartInvariant.step tm (step_initCfg_startedCfg tm y hne)
        (Tape.StartInvariant.init_ofBool y) (fun _ => Tape.StartInvariant.init_nil)
        Tape.StartInvariant.init_nil
      obtain ⟨realFinal,hv⟩ := retargetInput_reachesIn_of_reachesIn tm hr hi hw hout realInput
      refine ⟨retargetWrap tm realFinal c,u,by omega,?_,hh,ho⟩
      rw [retargetInputStartedCfg_eq_retargetWrap tm y realInput hne]
      exact retargetInputStarted_reachesIn_of_retargetInput tm hv

/-- Compose two actual runs on this input. Neither component is required to
have a uniform input-polynomial runtime; the second may be output-polynomial. -/
theorem compose_runs {nf ng : Nat} (tmF : TM nf) (tmG : TM ng)
    (hne : tmG.qstart ≠ tmG.qhalt) (x y z : List Bool) (T U : Nat)
    (hF : ∃ c t, t ≤ T ∧ tmF.reachesIn t (tmF.initCfg x) c ∧ tmF.halted c ∧ c.output.HasOutput y)
    (hG : ∃ c t, t ≤ U ∧ tmG.reachesIn t (tmG.initCfg y) c ∧ tmG.halted c ∧ c.output.HasOutput z) :
    ∃ c t, t ≤ 2*T+2*y.length+11+U ∧
      (compositionTM tmF tmG).reachesIn t ((compositionTM tmF tmG).initCfg x) c ∧
      (compositionTM tmF tmG).halted c ∧ c.output.HasOutput z := by
  obtain ⟨C,t,ht,hr,hh,hraw,hhead,hvirtual,hscratch,hinv,hinhead,hwork,hout⟩ :=
    compositionFirstTM_boundary_of_run_internal tmF ng x y T hF
  have htail := compositionTailTM_hoareTime_of_virtualRun_internal (nf := nf)
    (G := fun _ => U) tmG y (T+1) (fun out => out.HasOutput z)
      (virtual_run tmG hne y z U hG)
  obtain ⟨D,u,hu,hr2,hh2,ho⟩ := htail (transitionInput C.input)
    (fun i => transitionTape (C.work i)) (transitionTape C.output)
      ⟨hraw,(hwork _).1,hhead.trans (Nat.add_le_add_right ht 1),hvirtual,hscratch,
        hout,hinv,hinhead,fun i => hwork (compositionPrefixIdx nf ng i)⟩
  have hseq := seqTM_reachesIn_of_reachesIn (compositionFirstTM tmF ng)
    (compositionTailTM nf ng tmG) hr hh hr2
  change u ≤ ((T+1+2)+1+((y.length+1)+1+((y.length+1+2)+1+U))) at hu
  exact ⟨phase2Wrap (compositionFirstTM tmF ng) (compositionTailTM nf ng tmG) D,
    t+1+u,by omega,hseq,(phase2Wrap_halted_iff _ _ _).mpr hh2,ho⟩

end IrrRAFEnumeration.PointwiseComposition
