module

public import proofs.UnconstrainedPACDetection.FormulaUnaryScript

@[expose] public section

namespace UnconstrainedPACDetection.FormulaHeaderStaging
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)
open FormulaUnaryScript (Op)

def initial (c o v e r : Nat) (t : Fin 28) : Nat :=
  if t.val=0 then c else if t.val=1 then o else if t.val=2 then v else
  if t.val=3 then 1 else if t.val=4 then e else if t.val=5 then r else 0

def ops : List (Op 28) :=
  [.copy 1 15 (by decide),.inc 15,.copy 2 16 (by decide),.copy 0 18 (by decide),
   .copy 15 17 (by decide),.copy 16 20 (by decide),.copy 18 21 (by decide),
   .copy 5 26 (by decide),.inc 26,.inc 26,.copy 5 25 (by decide),.inc 25,
   .set 22 20,.mulAdd 1 22 24 (by decide) (by decide) (by decide),.set 22 1,.set 23 4,
   .copy 26 27 (by decide),.set 0 0,.set 1 0,.set 2 0,.set 3 0,.set 4 0,.set 5 0,.set 6 0,
   .set 8 1,.set 13 1,.set 19 1]

def cap (c o v e r : Nat) : Nat := e+r+20*o+v+c+25

theorem safe (c o v e r : Nat) : FormulaUnaryScript.Safe ops (initial c o v e r) (cap c o v e r) := by
  norm_num [ops,FormulaUnaryScript.Safe,FormulaUnaryScript.Allowed,FormulaUnaryScript.eval,initial,
    Function.update_apply,Fin.ext_iff,cap]
  omega

theorem result (c o v e r : Nat) : FormulaUnaryScript.frame (FormulaUnaryScript.run ops (initial c o v e r)) =
    FormulaRowQuery.frame 0 (o+1) v c (20*o) (r+1) (r+2) (regTape (r+2)) := by
  funext t
  fin_cases t <;>
    norm_num [ops,FormulaUnaryScript.run,FormulaUnaryScript.eval,FormulaUnaryScript.frame,initial,
      Function.update_apply,Fin.ext_iff,FormulaRowQuery.frame,FormulaAllTails.frame,
      FormulaExternalTailPhase.frame,FormulaAllRailTails.frame,FormulaChangingFrame.extend,
      FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,FormulaRailTailReentrant.frame,
      FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank,Nat.mul_comm]
  all_goals first | exact (FormulaEndpointRegisters.unary_word 0).symm | exact (FormulaEndpointRegisters.unary_word 1).symm

def machine : TM 28 := FormulaUnaryScript.machine ops

theorem hoare (c o v e r : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) : machine.HoareTime
    (EmitPred inp (FormulaUnaryScript.frame (initial c o v e r)) ys)
    (EmitPred inp (FormulaRowQuery.frame 0 (o+1) v c (20*o) (r+1) (r+2) (regTape (r+2))) ys)
    (27*(opBudget (cap c o v e r)+1)) := by
  have h := FormulaUnaryScript.hoare ops (initial c o v e r) (cap c o v e r) (safe c o v e r) inp hi ys
  rw [result] at h
  exact h

end UnconstrainedPACDetection.FormulaHeaderStaging
