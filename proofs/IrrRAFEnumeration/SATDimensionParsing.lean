module

public import proofs.IrrRAFEnumeration.SATHeaderParsing

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open SATCompletion Complexity Complexity.TM

theorem unary_header_cell (pre tail : List Bool) (v i : Nat) (hi : i ≤ v) :
    (parkedInput (pre ++ (List.replicate v true ++ false :: tail))).cells
      (pre.length+i+1) = if i < v then Γ.one else Γ.zero := by
  change (Tape.init ((pre ++ (List.replicate v true ++ false :: tail)).map Γ.ofBool)).cells
    (pre.length+i+1) = _
  rw [Tape.init_cells_succ, List.map_append]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_map, Nat.add_sub_cancel_left]
  rw [List.map_append]
  by_cases hlt : i < v
  · rw [List.getElem?_append_left (by simpa using hlt)]
    simp [List.map_replicate, hlt, Γ.ofBool]
  · have he : i = v := by omega
    subst i
    rw [List.getElem?_append_right (by simp)]
    simp [Γ.ofBool]

theorem headerRegTM_bits {k : Nat} (q : Fin k) (pre tail : List Bool) (v : Nat)
    (work : Fin k → Tape) (ys : List Bool)
    (hw : ∀ i, Parked (work i)) (hq : work q = regTape 0) :
    (headerRegTM q).HoareTime
      (EmitPred (advanceInput (parkedInput (pre ++ (List.replicate v true ++ false :: tail)))
        pre.length) work ys)
      (EmitPred (advanceInput (parkedInput (pre ++ (List.replicate v true ++ false :: tail)))
        (pre.length+v+1)) (Function.update work q (regTape v)) ys)
      (2*v+2) := by
  have h := headerRegTM_correct q v
    (advanceInput (parkedInput (pre ++ (List.replicate v true ++ false :: tail))) pre.length)
    work ys (advanceInput_parked _ _ (parkedInput_parked _)) hw hq
    (by
      intro i hi
      have hc := unary_header_cell pre tail v i (by omega)
      simpa [advanceInput, parkedInput, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hi] using hc)
    (by
      have hc := unary_header_cell pre tail v v le_rfl
      simpa [advanceInput, parkedInput, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc)
  simpa only [advanceInput, Nat.add_assoc] using h

def dimensionRegsTM {k : Nat} (rn rm : Fin k) : TM k :=
  seqTM (headerRegTM rn) (headerRegTM rm)

theorem dimensionRegsTM_correct {n m k : Nat} (Φ : Fin m → Finset (Choice n))
    (rn rm : Fin k) (hne : rm ≠ rn) (work : Fin k → Tape) (ys : List Bool)
    (hw : ∀ i, Parked (work i)) (hn : work rn = regTape 0) (hm : work rm = regTape 0) :
    (dimensionRegsTM rn rm).HoareTime (EmitPred (parkedInput (cnfBits Φ)) work ys)
      (EmitPred (advanceInput (parkedInput (cnfBits Φ)) (n+m+2))
        (Function.update (Function.update work rn (regTape n)) rm (regTape m)) ys)
      (2*n+2*m+5) := by
  let W := Function.update work rn (regTape n)
  have hw' : ∀ i, Parked (W i) := updateReg_parked work hw rn n
  have h₁ := headerRegTM_bits rn []
    (List.replicate m true ++ false :: cnfBody Φ) n work ys hw hn
  have h₂ := headerRegTM_bits rm (List.replicate n true ++ [false]) (cnfBody Φ)
    m W ys hw' (by simpa [W, Function.update_of_ne hne] using hm)
  have he₁ : [] ++ (List.replicate n true ++ false :: (List.replicate m true ++ false :: cnfBody Φ)) =
      cnfBits Φ := by simp [cnfBits, List.append_assoc]
  have he₂ : (List.replicate n true ++ [false]) ++ (List.replicate m true ++ false :: cnfBody Φ) =
      cnfBits Φ := by simp [cnfBits, List.append_assoc]
  rw [he₁] at h₁
  rw [he₂] at h₂
  simp only [List.length_nil, Nat.zero_add, List.length_append, List.length_replicate,
    List.length_singleton] at h₁ h₂
  have hall := seqTM_hoareTime _ _ h₁
    (emitPred_transition (advanceInput_parked _ _ (parkedInput_parked _)) hw' ys) h₂
  have hpos : n+1+m+1 = n+m+2 := by omega
  have htime : (2*n+2)+1+(2*m+2) = 2*n+2*m+5 := by omega
  rw [hpos, htime] at hall
  exact hall

end IrrRAFEnumeration.SATSource
