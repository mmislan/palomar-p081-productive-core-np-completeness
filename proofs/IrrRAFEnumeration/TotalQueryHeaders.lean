module

public import proofs.IrrRAFEnumeration.TolerantHeader

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

theorem unary_count_length (z : List Bool) :
    (readUnary z).1+(readUnary z).2.length ≤ z.length := by
  rcases unary_split z with h | ⟨h,ht⟩
  · have hl := congrArg List.length h
    simp only [List.length_append,List.length_replicate,List.length_cons] at hl
    omega
  · have hl := congrArg List.length h
    simp only [List.length_replicate] at hl
    simp only [ht,List.length_nil,Nat.add_zero]
    omega

theorem parse_count_bound (z : List Bool) :
    (parse z).knownCount+(parse z).moleculeCount+(parse z).reactionCount ≤ z.length := by
  have h1 := unary_count_length z
  have h2 := unary_count_length (readUnary z).2
  have h3 := unary_count_length (readUnary (readUnary z).2).2
  dsimp only [parse]
  omega

theorem parked_stream (z : List Bool) : StreamAt (parkedInput z) z := by
  intro i
  change (Tape.init (z.map Γ.ofBool)).cells (1+i) = _
  rw [Nat.add_comm,Tape.init_cells_succ]
  simp

theorem headers_stream_correct {k : Nat} (rg rd rr : Fin k)
    (hdg : rd ≠ rg) (hrg : rr ≠ rg) (hrd : rr ≠ rd)
    (inp : Tape) (z : List Bool) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (hg : work rg = regTape 0) (hd : work rd = regTape 0) (hr : work rr = regTape 0)
    (hz : StreamAt inp z) :
    (headersTM rg rd rr).HoareTime (EmitPred inp work ys)
      (EmitPred (advanceInput inp ((parse z).knownCount+(parse z).moleculeCount+(parse z).reactionCount+3))
        (Function.update (Function.update (Function.update work rg (regTape (parse z).knownCount))
          rd (regTape (parse z).moleculeCount)) rr (regTape (parse z).reactionCount)) ys)
      (2*((parse z).knownCount+(parse z).moleculeCount+(parse z).reactionCount)+8) := by
  let p1 := readUnary z
  let p2 := readUnary p1.2
  let p3 := readUnary p2.2
  let I1 := advanceInput inp (p1.1+1)
  let I2 := advanceInput I1 (p2.1+1)
  let W1 := Function.update work rg (regTape p1.1)
  let W2 := Function.update W1 rd (regTape p2.1)
  have hp1 : Parked I1 := advanceInput_parked _ _ hp
  have hp2 : Parked I2 := advanceInput_parked _ _ hp1
  have hw1 : ∀ i, Parked (W1 i) := updateReg_parked work hw rg p1.1
  have hw2 : ∀ i, Parked (W2 i) := updateReg_parked W1 hw1 rd p2.1
  have hs1 : StreamAt I1 p1.2 := stream_after_header inp z hz
  have hs2 : StreamAt I2 p2.2 := stream_after_header I1 p1.2 hs1
  have h1 := header_stream_correct rg inp z work ys hp hw hg hz
  have h2 := header_stream_correct rd I1 p1.2 W1 ys hp1 hw1
    (by simpa [W1,Function.update_of_ne hdg] using hd) hs1
  have h3 := header_stream_correct rr I2 p2.2 W2 ys hp2 hw2
    (by simpa [W2,W1,Function.update_of_ne hrd,Function.update_of_ne hrg] using hr) hs2
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition hp2 hw2 ys) h3
  have hall := seqTM_hoareTime _ _ h1 (emitPred_transition hp1 hw1 ys) h23
  change (headersTM rg rd rr).HoareTime (EmitPred inp work ys)
    (EmitPred (advanceInput I2 (p3.1+1))
      (Function.update W2 rr (regTape p3.1)) ys)
    ((2*p1.1+2)+1+((2*p2.1+2)+1+(2*p3.1+2))) at hall
  have hi : advanceInput I2 (p3.1+1) = advanceInput inp (p1.1+p2.1+p3.1+3) := by
    apply Tape.ext
    · dsimp [I2,I1,advanceInput]; omega
    · rfl
  have ht : (2*p1.1+2)+1+((2*p2.1+2)+1+(2*p3.1+2)) = 2*(p1.1+p2.1+p3.1)+8 := by omega
  rw [hi,ht] at hall
  exact hall

theorem headers_raw_correct {k : Nat} (rg rd rr : Fin k)
    (hdg : rd ≠ rg) (hrg : rr ≠ rg) (hrd : rr ≠ rd)
    (z : List Bool) (work : Fin k → Tape) (ys : List Bool)
    (hw : ∀ i, Parked (work i))
    (hg : work rg = regTape 0) (hd : work rd = regTape 0) (hr : work rr = regTape 0) :
    (headersTM rg rd rr).HoareTime (EmitPred (parkedInput z) work ys)
      (EmitPred (advanceInput (parkedInput z)
        ((parse z).knownCount+(parse z).moleculeCount+(parse z).reactionCount+3))
        (Function.update (Function.update (Function.update work rg (regTape (parse z).knownCount))
          rd (regTape (parse z).moleculeCount)) rr (regTape (parse z).reactionCount)) ys)
      (2*z.length+8) := by
  have h := headers_stream_correct rg rd rr hdg hrg hrd (parkedInput z) z work ys
    (parkedInput_parked z) hw hg hd hr (parked_stream z)
  exact TM.HoareTime.mono_bound h (by have hb := parse_count_bound z; omega)

end IrrRAFEnumeration.CompletionQuery
