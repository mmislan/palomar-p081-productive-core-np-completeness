module

public import proofs.IrrRAFEnumeration.SATMachineAddress

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

/-- Append the Boolean value in a parked unary 0/1 register in one tape step. -/
def emitRegisterBitTM {k : Nat} (r : Fin k) : TM k where
  Q := BumpPhase
  qstart := .go
  qhalt := .done
  δ := fun _ ih wh _ =>
    (.done, fun i => readBackWrite (wh i),
      if wh r = Γ.one then Γw.one else Γw.zero,
      idleDir ih, fun i => idleDir (wh i), Dir3.right)
  δ_right_of_start := fun _ _ _ _ =>
    ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => rfl⟩

theorem emitRegisterBitTM_correct {k : Nat} (r : Fin k) (b : Bool)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hip : Parked inp) (hwp : ∀ i, Parked (work i))
    (hr : work r = regTape (if b then 1 else 0)) :
    (emitRegisterBitTM r).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys ++ [b])) 1 := by
  rintro inp' work' out ⟨hi,hw,hout⟩
  subst inp'
  subst work'
  have hwrite : (if (work r).read = Γ.one then Γw.one else Γw.zero) = Γ.ofBool b := by
    rw [hr]
    cases b <;> simp [Tape.read, regTape, regCells, Γ.ofBool]
  have hs : (emitRegisterBitTM r).step
      { state := .go, input := inp, work := work, output := out } = some
      { state := .done, input := inp, work := work,
        output := out.writeAndMove (Γ.ofBool b) .right } := by
    simp only [TM.step, emitRegisterBitTM, reduceCtorEq, ↓reduceIte]
    rw [hwrite]
    refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, rfl⟩)
    · exact hip.move_idle
    · funext i; exact (hwp i).writeAndMove_readBack_idle
  exact ⟨_,1,le_rfl,.step hs .zero,rfl,rfl,rfl,outAcc_append_bit hout b⟩

/-- Address, read, and append one actual CNF incidence bit. -/
def clauseEmitterTM : TM 6 := seqTM addressedClauseTM (emitRegisterBitTM 5)

theorem clauseEmitterTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (j : Fin m) (x : Choice n) (ys : List Bool) :
    clauseEmitterTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ)) (lookupRegisters j x) ys)
      (EmitPred (parkedInput (cnfBits Φ))
        (Function.update (positionRegisters j x) 5
          (regTape (if x ∈ Φ j then 1 else 0)))
        (ys ++ [decide (x ∈ Φ j)]))
      (256*((cnfBits Φ).length+3)^3+2) := by
  let W := Function.update (positionRegisters j x) 5
    (regTape (if x ∈ Φ j then 1 else 0))
  have hwp : ∀ i, Parked (W i) :=
    updateReg_parked _ (positionRegisters_parked j x) _ _
  have h₁ := addressedClauseTM_correct Φ j x ys
  have h₂ := emitRegisterBitTM_correct (5 : Fin 6) (decide (x ∈ Φ j))
    (parkedInput (cnfBits Φ)) W ys (parkedInput_parked _) hwp (by simp [W])
  simpa [clauseEmitterTM, W, Nat.add_assoc] using seqTM_hoareTime _ _ h₁
    (emitPred_transition (parkedInput_parked _) hwp ys) h₂

end IrrRAFEnumeration.SATSource
