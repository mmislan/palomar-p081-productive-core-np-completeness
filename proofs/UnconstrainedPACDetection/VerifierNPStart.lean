module

public import proofs.UnconstrainedPACDetection.VerifierNPPrepare

@[expose] public section

namespace UnconstrainedPACDetection.VerifierNPStart
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def bump : TM 33 where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun _ i w o => allIdle true i w o
  δ_right_of_start := fun _ i w o => rightOfStart_allIdle i w o

def initial (src : List Bool) : Complexity.TM.TapePred 33 := fun inp work out =>
  inp = Tape.init (src.map Γ.ofBool) ∧ work = (fun _ => Tape.init []) ∧ out = Tape.init []

theorem bump_hoare (src : List Bool) : bump.HoareTime (initial src)
    (VerifierNPCountRouting.initial src) 1 := by
  rintro inp work out ⟨rfl,rfl,rfl⟩
  refine ⟨⟨true,word src,fun _ => word [],word []⟩,1,le_rfl,.step ?_ .zero,rfl,rfl,rfl,rfl⟩
  rfl

def machine : TM 33 := seqTM bump VerifierNPPrepare.setup
def bound (N : Nat) : Nat := 3*N+18+VerifierNPPrepare.arithmeticTime N

theorem setup_hoare (src : List Bool) : machine.HoareTime (initial src)
    (EmitPred (word src) (VerifierNPPrepare.preparedWork src.length) []) (bound src.length) := by
  have hs : ∀ inp work out, VerifierNPCountRouting.initial src inp work out →
      VerifierNPCountRouting.initial src (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
    rintro inp work out ⟨rfl,rfl,rfl⟩
    exact phaseTransition_eq_self_of_reads_ne_start (word_parked src).read_ne_start
      (fun _ : Fin 33 => (word_parked []).read_ne_start) (word_parked []).read_ne_start
  have h := seqTM_hoareTime _ _ (bump_hoare src) hs (VerifierNPPrepare.setup_hoare src)
  exact h.mono_bound (by unfold bound; omega)

end UnconstrainedPACDetection.VerifierNPStart
