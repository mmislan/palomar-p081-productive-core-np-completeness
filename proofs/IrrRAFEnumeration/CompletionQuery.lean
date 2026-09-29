module

public import proofs.IrrRAFEnumeration.EnumerationContract
public import proofs.IrrRAFEnumeration.SATDimensionParsing

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def headers (g d r : Nat) (body : List Bool) : List Bool :=
  List.replicate g true ++ false ::
    (List.replicate d true ++ false :: (List.replicate r true ++ false :: body))

/-- Prefix the known-list count to the unchanged CRS input; append the
container mask followed by the known masks in their explicit list order. -/
def bits {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) : List Bool :=
  List.replicate G.length true ++ false ::
    (inputBits Q C (Equiv.refl _) (Equiv.refl _) ++
      outputBody (Equiv.refl _) [U] ++ outputBody (Equiv.refl _) G)

def body {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) : List Bool :=
  List.ofFn (fun i => incidence Q C (Equiv.refl _) (Equiv.refl _) ((slotCode d r).symm i)) ++
    outputBody (Equiv.refl _) [U] ++ outputBody (Equiv.refl _) G

theorem bits_headers {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) :
    bits Q C G U = headers G.length d r (body Q C G U) := by
  unfold bits headers body inputBits
  have hshape (A B X Y Z : List Bool) :
      (A ++ [false] ++ B ++ [false] ++ X) ++ Y ++ Z =
        A ++ false :: (B ++ false :: (X ++ Y ++ Z)) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  exact congrArg (fun tail => List.replicate G.length true ++ false :: tail)
    (hshape _ _ _ _ _)

theorem body_length {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) :
    (body Q C G U).length = d+3*r*d+r+G.length*r := by
  unfold body
  rw [List.length_append, List.length_append, List.length_ofFn,
    outputBody_length, outputBody_length]
  simp only [List.length_singleton, Nat.one_mul]
  ring

theorem bits_length {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) :
    (bits Q C G U).length = G.length+2*d+2*r+3+3*r*d+G.length*r := by
  rw [bits_headers]
  have hb := body_length Q C G U
  unfold headers
  rw [List.length_append, List.length_replicate, List.length_cons,
    List.length_append, List.length_replicate, List.length_cons,
    List.length_append, List.length_replicate, List.length_cons, hb]
  omega

def headersTM {k : Nat} (rg rd rr : Fin k) : TM k :=
  seqTM (headerRegTM rg) (seqTM (headerRegTM rd) (headerRegTM rr))

theorem headersTM_correct {k : Nat} (rg rd rr : Fin k)
    (hdg : rd ≠ rg) (hrg : rr ≠ rg) (hrd : rr ≠ rd)
    (g d r : Nat) (tail : List Bool) (work : Fin k → Tape) (ys : List Bool)
    (hw : ∀ i, Parked (work i))
    (hg : work rg = regTape 0) (hd : work rd = regTape 0) (hr : work rr = regTape 0) :
    (headersTM rg rd rr).HoareTime (EmitPred (parkedInput (headers g d r tail)) work ys)
      (EmitPred (advanceInput (parkedInput (headers g d r tail)) (g+d+r+3))
        (Function.update (Function.update (Function.update work rg (regTape g)) rd (regTape d)) rr (regTape r)) ys)
      (2*(g+d+r)+8) := by
  let W1 := Function.update work rg (regTape g)
  let W2 := Function.update W1 rd (regTape d)
  have hw1 : ∀ i, Parked (W1 i) := updateReg_parked work hw rg g
  have hw2 : ∀ i, Parked (W2 i) := updateReg_parked W1 hw1 rd d
  have h1 := headerRegTM_bits rg []
    (List.replicate d true ++ false :: (List.replicate r true ++ false :: tail)) g work ys hw hg
  have h2 := headerRegTM_bits rd (List.replicate g true ++ [false])
    (List.replicate r true ++ false :: tail) d W1 ys hw1
    (by simpa [W1,Function.update_of_ne hdg] using hd)
  have h3 := headerRegTM_bits rr
    ((List.replicate g true ++ [false]) ++ (List.replicate d true ++ [false])) tail r W2 ys hw2
    (by simpa [W2,W1,Function.update_of_ne hrd,Function.update_of_ne hrg] using hr)
  have e1 : [] ++ (List.replicate g true ++ false ::
      (List.replicate d true ++ false :: (List.replicate r true ++ false :: tail))) = headers g d r tail := by
    simp [headers]
  have e2 : (List.replicate g true ++ [false]) ++ (List.replicate d true ++ false ::
      (List.replicate r true ++ false :: tail)) = headers g d r tail := by
    simp [headers,List.append_assoc]
  have e3 : ((List.replicate g true ++ [false]) ++ (List.replicate d true ++ [false])) ++
      (List.replicate r true ++ false :: tail) = headers g d r tail := by
    simp [headers,List.append_assoc]
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  simp only [List.length_nil,Nat.zero_add,List.length_append,List.length_replicate,List.length_singleton] at h1 h2 h3
  have epos : g+1+(d+1) = g+1+d+1 := by omega
  rw [epos] at h3
  have h23 := seqTM_hoareTime _ _ h2
    (emitPred_transition (advanceInput_parked _ _ (parkedInput_parked _)) hw2 ys) h3
  have hall := seqTM_hoareTime _ _ h1
    (emitPred_transition (advanceInput_parked _ _ (parkedInput_parked _)) hw1 ys) h23
  have ep : g+1+d+1+r+1 = g+d+r+3 := by omega
  have et : (2*g+2)+1+((2*d+2)+1+(2*r+2)) = 2*(g+d+r)+8 := by omega
  rw [ep,et] at hall
  exact hall

end IrrRAFEnumeration.CompletionQuery
