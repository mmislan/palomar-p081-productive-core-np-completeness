module

public import proofs.IrrRAFEnumeration.QueryBoundaryProbe
public import proofs.IrrRAFEnumeration.SATDimensionInit
public import proofs.IrrRAFEnumeration.SATTapeFrame

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

def guardWork (g d r m : Nat) : Fin 6 → Tape :=
  frameWork (m := 2) (lengthWork g d r m) (fun _ => regTape 0)

theorem guardWork_parked (g d r m : Nat) : ∀ i, Parked (guardWork g d r m i) := by
  intro i
  unfold guardWork frameWork
  split
  · exact lengthWork_parked g d r m _
  · exact parked_regTape _

theorem guardWork_zero : guardWork 0 0 0 0 = fun _ => regTape 0 := by
  funext i
  fin_cases i <;> simp [guardWork, frameWork, lengthWork, sourceValue]

def guardPreparationTM : TM 6 :=
  seqTM bumpTM (seqTM (headersTM 0 1 2)
    (seqTM (expectedLengthTM.liftTM 2)
      (seqTM rewindInputTM (boundaryProbeTM 3 4 5))))

def guardTime (N : Nat) := lengthTime N+3*N+80*(N+1)^2+68

theorem guardPreparationTM_correct (z : List Bool) :
    let p := parse z
    let m := expectedLength p.knownCount p.moleculeCount p.reactionCount
    guardPreparationTM.HoareTime
      (fun inp work out => inp = Tape.init (z.map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (fun inp w out =>
        EmitPred (parkedInput z)
          (boundaryWork (guardWork p.knownCount p.moleculeCount p.reactionCount m)
            3 4 5 (parkedInput z) m) [] inp w out ∧
        ((w 4).read = Γ.one ∧ (w 5).read = Γ.one ↔ SizeCheck z))
      (guardTime z.length) := by
  dsimp only
  let p := parse z
  let m := expectedLength p.knownCount p.moleculeCount p.reactionCount
  let s := p.knownCount+p.moleculeCount+p.reactionCount
  let W0 : Fin 6 → Tape := fun _ => regTape 0
  let W1 := guardWork p.knownCount p.moleculeCount p.reactionCount 0
  let W2 := guardWork p.knownCount p.moleculeCount p.reactionCount m
  let inp1 := advanceInput (parkedInput z) (s+3)
  have hp1 : Parked inp1 := advanceInput_parked _ _ (parkedInput_parked z)
  have hw1 : ∀ i, Parked (W1 i) := guardWork_parked _ _ _ _
  have hw2 : ∀ i, Parked (W2 i) := guardWork_parked _ _ _ _
  have hb : bumpTM.HoareTime _ (EmitPred (parkedInput z) W0 []) 1 :=
    (bumpTM_hoareTime z).strengthen_post (by
      rintro inp work out ⟨hi,hw,ho⟩
      exact ⟨hi,funext (fun i => (hw i).eq_regT),ho⟩)
  have hh := headers_raw_correct (0 : Fin 6) 1 2 (by decide) (by decide) (by decide)
    z W0 [] (fun _ => parked_regTape _) rfl rfl rfl
  have he : Function.update (Function.update (Function.update W0 0 (regTape p.knownCount))
      1 (regTape p.moleculeCount)) 2 (regTape p.reactionCount) = W1 := by
    funext i
    fin_cases i <;> simp [W0,W1,guardWork,frameWork,lengthWork,sourceValue]
  change (headersTM 0 1 2).HoareTime (EmitPred (parkedInput z) W0 [])
    (EmitPred inp1 _ []) (2*z.length+8) at hh
  rw [he] at hh
  have ha := liftTM_frame_correct expectedLengthTM 2 (fun _ => regTape 0)
    (fun _ _ => parked_regTape _) inp1 inp1
    (lengthWork p.knownCount p.moleculeCount p.reactionCount 0)
    (lengthWork p.knownCount p.moleculeCount p.reactionCount m) [] [] (lengthTime z.length)
    (expectedLengthTM_inputBound _ _ _ _ (parse_count_bound z) inp1 [] hp1)
  have hr := rewindParsedInput_correct z (s+3) W2 [] hw2
  have hq := queryProbeTM_correct (3 : Fin 6) 4 5 (by decide) (by decide) (by decide)
    z W2 [] hw2
    (by simp [W2,guardWork,frameWork,lengthWork,m,p])
    (by simp [W2,guardWork,frameWork]) (by simp [W2,guardWork,frameWork])
  have hrq := seqTM_hoareTime _ _ hr (emitPred_transition (parkedInput_parked z) hw2 []) hq
  have harq := seqTM_hoareTime _ _ ha (emitPred_transition hp1 hw2 []) hrq
  have hharq := seqTM_hoareTime _ _ hh (emitPred_transition hp1 hw1 []) harq
  have hall := seqTM_hoareTime _ _ hb
    (emitPred_transition (parkedInput_parked z) (fun _ => parked_regTape _) []) hharq
  apply hall.mono_bound
  have hs : s ≤ z.length := parse_count_bound z
  have hc := lengthCap_le p.knownCount p.moleculeCount p.reactionCount z.length hs
  have hm : m ≤ 10*(z.length+1)^2 := by
    dsimp [lengthCap] at hc
    dsimp [m]
    omega
  change 1+1+(2*z.length+8+1+(lengthTime z.length+1+(s+3+3+1+(8*m+49)))) ≤ _
  unfold guardTime
  omega

end IrrRAFEnumeration.CompletionQuery
