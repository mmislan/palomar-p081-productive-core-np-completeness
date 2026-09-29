module

public import proofs.IrrRAFEnumeration.CompletionReactantFamily

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def firingBase (d r i : Nat) := r+(d+1)*d+i*r

def firingClauses {d r : Nat} (Q : CRS (Fin d) (Fin r)) (i : Fin d) (j : Fin r) : SAT.CNF :=
  [PositiveCompletionCNF.implies (PositiveCompletionCNF.fireVar d i j)
    [PositiveCompletionCNF.selectVar j]] ++
  PositiveCompletionCNF.each d (fun x => if x ∈ Q.inputs j then
    [PositiveCompletionCNF.implies (PositiveCompletionCNF.fireVar d i j)
      [PositiveCompletionCNF.rowVar r ⟨i.val,by omega⟩ x]] else [])

def firingWork (d p a b fire j : Nat) (fuel : Tape) : Fin 8 → Tape :=
  frameWork (m := 1) (catalystFamilyWork d p a b fire fuel) (fun _ => regTape j)

theorem firingWork_parked (d p a b fire j : Nat) (fuel : Tape) (hf : Parked fuel) :
    ∀ k, Parked (firingWork d p a b fire j fuel k) := by
  intro k
  fin_cases k <;> simp only [firingWork,frameWork,catalystFamilyWork] <;>
    first | exact hf | exact parked_regTape _

def firingRowTM : TM 8 :=
  seqTM (pairClauseTM 4 7) (implicationScanTM.liftTM 3)

theorem firingRowTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (i : Fin d) (j : Fin r)
    (fuel : Tape) (hf : Parked fuel) (ys : List Bool) :
    firingRowTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (firingWork d (reactantStart d r j.val) (r+i.val*d) (r+i.val*d)
          (firingBase d r i.val+j.val) j.val fuel) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (firingWork d (reactantStart d r j.val+d) (r+i.val*d+d) (r+i.val*d)
          (firingBase d r i.val+j.val) j.val fuel)
        (ys++SAT.CNF.encode (firingClauses Q i j)))
      (3*(firingBase d r i.val+j.val)+3*j.val+23+
        (d*(5*reactantStart d r j.val+5*(r+i.val*d)+3*(firingBase d r i.val+j.val)+10*d+63)+d+2)) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  let p := reactantStart d r j.val
  let b := r+i.val*d
  let f := firingBase d r i.val+j.val
  let zs := ys++SAT.CNF.encode [[⟨false,f⟩,⟨true,j.val⟩]]
  have hp : Parked inp := parkedInput_parked _
  have hw := firingWork_parked d p b b f j.val fuel hf
  have h1 := pairClauseTM_correct (4 : Fin 8) 7 f j.val inp
    (firingWork d p b b f j.val fuel) ys hp hw rfl rfl
  have hs := implicationScanTM_correct f inp p b d zs hp rfl rfl
  let extra : Fin 8 → Tape := fun k => if k = 5 then fuel else if k = 6 then regTape b else regTape j.val
  have he : ∀ k, 5 ≤ k.val → Parked (extra k) := by
    intro k _
    by_cases h5 : k = 5
    · simpa [extra,h5] using hf
    · by_cases h6 : k = 6 <;> simp only [extra,h5,h6,↓reduceIte] <;> exact parked_regTape _
  have h2 := liftTM_frame_correct implicationScanTM 3 extra he inp inp
    (implicationWork f (regTape d) p b 0) (implicationWork f (regTape d) (p+d) (b+d) 0)
    zs (zs++SAT.CNF.encode (implicationClauses f inp p b d))
    (d*(5*p+5*b+3*f+10*d+63)+d+2) hs
  have ew (p a : Nat) : frameWork (m := 3) (implicationWork f (regTape d) p a 0) extra =
      firingWork d p a b f j.val fuel := by
    funext k
    fin_cases k <;> simp [frameWork,implicationWork,extra,firingWork,catalystFamilyWork]
  rw [ew,ew] at h2
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw zs) h2
  have hc := implicationClauses_eq_each f inp p b d (fun x => decide (x ∈ Q.inputs j))
    (original_reactant_cell Q C j)
  have ho : zs++SAT.CNF.encode (implicationClauses f inp p b d) =
      ys++SAT.CNF.encode (firingClauses Q i j) := by
    rw [hc]
    simp [zs,firingClauses,PositiveCompletionCNF.implies,PositiveCompletionCNF.positive,
      PositiveCompletionCNF.fireVar,PositiveCompletionCNF.selectVar,PositiveCompletionCNF.rowVar,
      f,firingBase,b,SAT.CNF.encode_cons,List.append_assoc]
  rw [ho] at h
  have h' := h.mono_bound (by omega :
    (3*f+3*j.val+22)+1+(d*(5*p+5*b+3*f+10*d+63)+d+2) ≤
      3*f+3*j.val+23+(d*(5*p+5*b+3*f+10*d+63)+d+2))
  unfold EmitPred at h' ⊢
  dsimp only [firingRowTM, inp, p, b, f] at h' ⊢
  exact h'

end IrrRAFEnumeration.CompletionQuery
