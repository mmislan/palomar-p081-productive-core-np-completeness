module

public import proofs.Complexitylib.Models.TuringMachine.Registers.Horner
public import Mathlib.Tactic

@[expose] public section

namespace UnconstrainedPACDetection.VerifierNPBound
open Complexity Complexity.TM

def cap (N : Nat) : Nat := 16*(N+1)^3

/-- The three registers lie outside the evaluator's work bank 0..29. -/
def machine : TM 33 := hornerLayersTM 30 31 32 [16,0,0,0]

def finalWork (work : Fin 33 → Tape) (N : Nat) : Fin 33 → Tape :=
  Function.update (Function.update work 32 (regTape (cap N))) 31 (regTape (cap N))

theorem fold_value (N : Nat) : hornerFold (N+1) [16,0,0,0] 0 = cap N := by
  simp [hornerFold,cap]
  ring

theorem prefixes (N k : Nat) (hk : k ≤ 4) :
    hornerFold (N+1) (List.take k [16,0,0,0]) 0 ≤ cap N := by
  have hx : 1 ≤ N+1 := by omega
  have h2 : N+1 ≤ (N+1)*(N+1) := by nlinarith
  have h3 : (N+1)*(N+1) ≤ (N+1)*(N+1)*(N+1) := by nlinarith
  interval_cases k <;> norm_num [hornerFold,cap,pow_succ] <;> nlinarith

theorem counter_hoare (N : Nat) (inp : Tape) (work : Fin 33 → Tape)
    (hi : Parked inp) (hp : ∀ j, Parked (work j))
    (h30 : work 30 = regTape (N+1)) (h31 : work 31 = regTape 0) (h32 : work 32 = regTape 0) :
    machine.HoareTime (EmitPred inp work []) (EmitPred inp (finalWork work N) [])
      (4*(layerBudget (cap N)+1)+1) := by
  have hx : N+1 ≤ cap N := by
    have h := prefixes N 2 (by omega)
    simp only [List.take_succ_cons,List.take_zero,hornerFold] at h
    omega
  have h := hornerLayersTM_hoareTime (30 : Fin 33) 31 32 (by decide) (by decide) (by decide)
    (cap N) (N+1) hx inp hi 16 [0,0,0] 0 0 work []
    (fun k hk => prefixes N k (by simpa using hk)) (Nat.zero_le _) hp h30 h31 h32
  simpa only [fold_value,List.length_cons,List.length_nil,finalWork,machine] using h

theorem evaluator_frame (N : Nat) (work : Fin 33 → Tape) (j : Fin 33) (hj : j.val < 30) :
    finalWork work N j = work j := by
  have h31 : j ≠ 31 := by intro h; subst j; omega
  have h32 : j ≠ 32 := by intro h; subst j; omega
  simp only [finalWork,Function.update_of_ne h31,Function.update_of_ne h32]

end UnconstrainedPACDetection.VerifierNPBound
