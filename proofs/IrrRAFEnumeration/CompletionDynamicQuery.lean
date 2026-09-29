module

public import proofs.IrrRAFEnumeration.CompletionBufferRestore

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def containerMask {r : Nat} (U : Finset (Fin r)) : List Bool :=
  List.ofFn (fun j => decide (j ∈ U))

theorem containerMask_cell {r : Nat} (U : Finset (Fin r)) (j : Fin r) :
    (parkedInput (containerMask U)).cells (1+j.val) = Γ.ofBool (decide (j ∈ U)) := by
  have h := Tape.init_ofBool_cells_lt (containerMask U) j.val (by simp [containerMask])
  simpa [containerMask,parkedInput,Nat.add_comm] using h

theorem containerMask_clauses {r : Nat} (U : Finset (Fin r)) :
    maskClauses (parkedInput (containerMask U)) 1 0 r = PositiveCompletionCNF.containerExclusions U := by
  have h := maskClauses_eq_each (parkedInput (containerMask U)) 1 0 r
    (fun j => decide (j ∈ U)) (containerMask_cell U)
  simpa [PositiveCompletionCNF.containerExclusions,PositiveCompletionCNF.negative,
    PositiveCompletionCNF.selectVar] using h

def dynamicWork {r : Nat} (U : Finset (Fin r)) (pos index : Nat)
    (base blockers : List Bool) : Fin 7 → Tape :=
  frameWork (m := 2)
    (frameWork (m := 1) (maskWork (regTape r) pos index 0)
      (fun _ => parkedInput (containerMask U)))
    (fun i => if i = 5 then parkedInput base else parkedInput blockers)

theorem dynamicWork_parked {r : Nat} (U : Finset (Fin r)) (pos index : Nat)
    (base blockers : List Bool) : ∀ i, Parked (dynamicWork U pos index base blockers i) := by
  intro i
  fin_cases i <;> first | exact parked_regTape _ | exact parkedInput_parked _

def dynamicMaskTM : TM 7 := (retargetInput maskScanTM).liftTM 2

theorem dynamicMaskTM_correct {r : Nat} (U : Finset (Fin r))
    (base blockers : List Bool) (inp : Tape) (ys : List Bool) (hp : Parked inp) :
    dynamicMaskTM.HoareTime (EmitPred inp (dynamicWork U 1 0 base blockers) ys)
      (EmitPred inp (dynamicWork U (1+r) r base blockers)
        (ys++SAT.CNF.encode (PositiveCompletionCNF.containerExclusions U)))
      (r*(10*r+58)+r+2) := by
  let vin := parkedInput (containerMask U)
  have h := maskScanTM_correct vin 1 0 r ys (parkedInput_parked _) rfl rfl
  rw [containerMask_clauses U] at h
  have hv := virtualEmitter_correct maskScanTM inp vin vin
    (maskWork (regTape r) 1 0 0) (maskWork (regTape r) (1+r) (0+r) 0)
    _ _ _ hp ⟨rfl,(parkedInput_parked _).2⟩
    (fun i => ⟨by fin_cases i <;> rfl,(maskWork_parked _ _ _ _ (parked_regTape _ ) i).2⟩) h
  have hf := liftTM_frame_correct (retargetInput maskScanTM) 2
    (fun i : Fin 7 => if i = 5 then parkedInput base else parkedInput blockers)
    (fun i _ => by split <;> exact parkedInput_parked _) inp inp _ _ _ _ _ hv
  have htime : r*(5*1+5*0+10*r+53)+r+2 = r*(10*r+58)+r+2 := by ring
  rw [htime] at hf
  simpa only [dynamicMaskTM,dynamicWork,Nat.zero_add] using hf

def dynamicQueryTM : TM 7 :=
  seqTM (appendRestoreTM 5) (seqTM (appendRestoreTM 6) dynamicMaskTM)

def dynamicQueryTime (baseLength blockersLength r : Nat) :=
  2*baseLength+2*blockersLength+r*(10*r+58)+r+14

/-- Every new query reuses the stored chemistry and blockers, and freshly emits exclusions. -/
theorem dynamicQueryTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase (decC := decC) Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    dynamicQueryTM.HoareTime (EmitPred inp (dynamicWork U 1 0 base blocks) [])
      (EmitPred inp (dynamicWork U (1+r) r base blocks)
        (SAT.CNF.encode (assembledBase (decC := decC) Q C ++ PositiveCompletionCNF.outputBlockers G ++
          PositiveCompletionCNF.containerExclusions U)))
      (dynamicQueryTime base.length blocks.length r) := by
  dsimp only
  let base := SAT.CNF.encode (assembledBase (decC := decC) Q C)
  let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
  let W := dynamicWork U 1 0 base blocks
  have hw : ∀ i, Parked (W i) := dynamicWork_parked _ _ _ _ _
  have h₁ := appendRestoreTM_correct (5 : Fin 7) base inp W [] hp hw rfl rfl (parkedInput_chunk base)
  have h₂ := appendRestoreTM_correct (6 : Fin 7) blocks inp W base hp hw rfl rfl (parkedInput_chunk blocks)
  have h₃ := dynamicMaskTM_correct U base blocks inp (base++blocks) hp
  simp only [List.nil_append] at h₁
  have h₂₃ := seqTM_hoareTime _ _ h₂ (emitPred_transition hp hw _) h₃
  have h := seqTM_hoareTime _ _ h₁ (emitPred_transition hp hw _) h₂₃
  rw [SAT.CNF.encode_append,SAT.CNF.encode_append]
  change dynamicQueryTM.HoareTime (EmitPred inp W [])
    (EmitPred inp (dynamicWork U (1+r) r base blocks)
      (base ++ blocks ++ SAT.CNF.encode (PositiveCompletionCNF.containerExclusions U)))
    (dynamicQueryTime base.length blocks.length r)
  exact h.mono_bound (by
    unfold dynamicQueryTime
    omega)

end IrrRAFEnumeration.CompletionQuery
