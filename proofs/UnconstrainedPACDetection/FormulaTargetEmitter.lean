module

public import proofs.UnconstrainedPACDetection.FormulaLookupMatching
public import proofs.Complexitylib.Models.TuringMachine.Registers.ForReg
public import proofs.Complexitylib.Models.TuringMachine.Registers.Emit

@[expose] public section

namespace UnconstrainedPACDetection.FormulaTargetEmitter
open Complexity Complexity.TM

@[reducible] def unary {n : Nat} (r : Fin n) : TM n := forRegTM (emitBitsTM [true]) r

/-- Emit the live unary register while restoring its head and all work tapes. -/
theorem unary_hoare {n : Nat} (r : Fin n) (v : Nat) (inp : Tape)
    (work : Fin n → Tape) (ys : List Bool) (hi : Parked inp)
    (hp : ∀ j, Parked (work j)) (hr : work r = regTape v) :
    (unary r).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys ++ List.replicate v true)) (4*v+2) := by
  have h := forRegTM_hoareTime (emitBitsTM [true]) r v inp (fun _ => work)
    (fun k => ys ++ List.replicate k true) 1 hi (fun _ => hr) (fun _ j _ => hp j) (by
      intro k _
      have hw : ∀ j, Parked (Function.update work r ⟨k+2,regCells v⟩ j) := by
        intro j
        by_cases hj : j = r
        · subst j
          simpa using (parked_regCells (v := v) (by omega : 1 ≤ k+2))
        · simpa only [Function.update_of_ne hj] using hp j
      have he := emitBitsTM_hoareTime [true] inp (Function.update work r ⟨k+2,regCells v⟩)
        (ys ++ List.replicate k true) hi hw
      simpa only [List.length_cons, List.length_nil, List.replicate_add,
        List.replicate_one, List.append_assoc] using he)
  simpa only [List.replicate_zero,List.append_nil,show v*(1+2)+(v+2) = 4*v+2 by omega]
    using h

@[reducible] def machine {n : Nat} (r : Fin n) (b : Bool) : TM n :=
  seqTM (emitBitsTM [!b]) (seqTM (unary r) (emitBitsTM [true]))

/-- One finite program per Boolean sign; the unbounded variable is read from a register. -/
theorem target_hoare {n : Nat} (r : Fin n) (b : Bool) (v : Nat) (inp : Tape)
    (work : Fin n → Tape) (ys : List Bool) (hi : Parked inp)
    (hp : ∀ j, Parked (work j)) (hr : work r = regTape v) :
    (machine r b).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys ++ FormulaLookupMatching.marked (FormulaLookupMatching.target v b)))
      (4*v+6) := by
  have ht := seqTM_hoareTime _ _ (unary_hoare r v inp work (ys ++ [!b]) hi hp hr)
    (emitPred_transition hi hp _) (emitBitsTM_hoareTime [true] inp work _ hi hp)
  have h := seqTM_hoareTime _ _ (emitBitsTM_hoareTime [!b] inp work ys hi hp)
    (emitPred_transition hi hp _) ht
  have h' := h.mono_bound (show 1+1+(4*v+2+1+1) ≤ 4*v+6 by omega)
  unfold EmitPred
  simpa only [machine, FormulaLookupMatching.marked,FormulaLookupMatching.target,SAT.Lit.encodeRaw,
    SAT.Unary.encode,List.append_assoc,List.singleton_append] using h'

end UnconstrainedPACDetection.FormulaTargetEmitter
