module

public import proofs.IrrRAFEnumeration.CompletionMaskScan

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def headerBits (g d r : Nat) : List Bool :=
  List.replicate g true ++ [false] ++ List.replicate d true ++ [false] ++
    List.replicate r true ++ [false]

theorem headerBits_length (g d r : Nat) : (headerBits g d r).length = g+d+r+3 := by
  simp [headerBits]
  omega

theorem headers_eq_headerBits (g d r : Nat) (tail : List Bool) :
    headers g d r tail = headerBits g d r ++ tail := by
  simp [headers,headerBits,List.append_assoc]

theorem block_cell {n : Nat} (pre tail : List Bool) (f : Fin n → Bool) (i : Fin n) :
    (parkedInput (pre++(List.ofFn f++tail))).cells (pre.length+i.val+1) = Γ.ofBool (f i) := by
  change (Tape.init ((pre++(List.ofFn f++tail)).map Γ.ofBool)).cells
    (pre.length+i.val+1) = Γ.ofBool (f i)
  rw [Tape.init_ofBool_cells_lt _ _ (by simp; omega)]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by simp)]
  simp

theorem incidence_cell {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) (s : Slot d r) :
    (parkedInput (bits Q C G U)).cells
      (G.length+d+r+3+(slotCode d r s).val+1) =
      Γ.ofBool (incidence Q C (Equiv.refl _) (Equiv.refl _) s) := by
  have h := block_cell (headerBits G.length d r)
    (outputBody (Equiv.refl _) [U]++outputBody (Equiv.refl _) G)
    (fun i => incidence Q C (Equiv.refl _) (Equiv.refl _) ((slotCode d r).symm i))
    (slotCode d r s)
  have hb := bits_headers Q C G U
  rw [hb, headers_eq_headerBits]
  unfold body
  rw [List.append_assoc]
  rw [headerBits_length] at h
  rw [Equiv.symm_apply_apply] at h
  exact h

def foodStart (g d r : Nat) := g+d+r+4
def containerStart (g d r : Nat) := g+d+r+4+(d+r*(3*d))

theorem food_cell {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) (x : Fin d) :
    (parkedInput (bits Q C G U)).cells (foodStart G.length d r+x.val) =
      Γ.ofBool (decide (x ∈ Q.food)) := by
  have h := incidence_cell Q C G U (.inl x)
  have hc : (slotCode d r (.inl x)).val = x.val := by simp [slotCode,finSumFinEquiv]
  rw [hc] at h
  convert h using 1
  · congr 1
    unfold foodStart
    omega
  · rfl

theorem container_cell {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) (j : Fin r) :
    (parkedInput (bits Q C G U)).cells (containerStart G.length d r+j.val) =
      Γ.ofBool (decide (j ∈ U)) := by
  let pre := headerBits G.length d r ++ List.ofFn (fun i =>
    incidence Q C (Equiv.refl _) (Equiv.refl _) ((slotCode d r).symm i))
  have h := block_cell pre (outputBody (Equiv.refl _) G) (fun i : Fin r => decide (i ∈ U)) j
  have hb : bits Q C G U = pre ++ (List.ofFn (fun i : Fin r => decide (i ∈ U)) ++
      outputBody (Equiv.refl _) G) := by
    have hheaders := bits_headers Q C G U
    rw [hheaders, headers_eq_headerBits]
    unfold pre body
    have hU : outputBody (Equiv.refl (Fin r)) [U] =
        List.ofFn (fun i : Fin r => decide (i ∈ U)) := by
      unfold outputBody
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      apply congrArg List.ofFn
      funext i
      exact decide_eq_decide.mpr Iff.rfl
    rw [hU, List.append_assoc, List.append_assoc]
  rw [hb]
  convert h using 1
  congr 1
  have hpre : pre.length = G.length+d+r+3+(d+r*(3*d)) := by
    unfold pre
    rw [List.length_append, List.length_ofFn, headerBits_length]
  rw [hpre]
  unfold containerStart
  omega

theorem container_maskClauses {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) :
    maskClauses (parkedInput (bits Q C G U)) (containerStart G.length d r) 0 r =
      PositiveCompletionCNF.each r (fun j => if j ∈ U then [] else
        [PositiveCompletionCNF.negative [PositiveCompletionCNF.selectVar j]]) := by
  have h := maskClauses_eq_each (parkedInput (bits Q C G U))
    (containerStart G.length d r) 0 r (fun j => decide (j ∈ U)) (container_cell Q C G U)
  have hf :
      (fun j : Fin r => if decide (j ∈ U) then [] else [[⟨false, 0+j.val⟩]]) =
      (fun j : Fin r => if j ∈ U then [] else
        [PositiveCompletionCNF.negative [PositiveCompletionCNF.selectVar j]]) := by
    funext j
    by_cases hj : j ∈ U <;>
      simp [hj, PositiveCompletionCNF.negative, PositiveCompletionCNF.selectVar]
  rw [hf] at h
  exact h

theorem food_maskClauses {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) :
    maskClauses (parkedInput (bits Q C G U)) (foodStart G.length d r) r d =
      PositiveCompletionCNF.each d (fun x => if x ∈ Q.food then [] else
        [PositiveCompletionCNF.negative [PositiveCompletionCNF.rowVar r ⟨0,by omega⟩ x]]) := by
  have h := maskClauses_eq_each (parkedInput (bits Q C G U))
    (foodStart G.length d r) r d (fun x => decide (x ∈ Q.food)) (food_cell Q C G U)
  have hf :
      (fun x : Fin d => if decide (x ∈ Q.food) then [] else [[⟨false, r+x.val⟩]]) =
      (fun x : Fin d => if x ∈ Q.food then [] else
        [PositiveCompletionCNF.negative [PositiveCompletionCNF.rowVar r ⟨0,by omega⟩ x]]) := by
    funext x
    by_cases hx : x ∈ Q.food <;>
      simp [hx, PositiveCompletionCNF.negative, PositiveCompletionCNF.rowVar]
  rw [hf] at h
  exact h

theorem containerScan_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) (ys : List Bool) :
    maskScanTM.HoareTime
      (EmitPred (parkedInput (bits Q C G U))
        (maskWork (regTape r) (containerStart G.length d r) 0 0) ys)
      (EmitPred (parkedInput (bits Q C G U))
        (maskWork (regTape r) (containerStart G.length d r+r) r 0)
        (ys++SAT.CNF.encode (PositiveCompletionCNF.each r (fun j =>
          if j ∈ U then [] else [PositiveCompletionCNF.negative [PositiveCompletionCNF.selectVar j]]))))
      (r*(5*containerStart G.length d r+10*r+53)+r+2) := by
  have h := maskScanTM_correct (parkedInput (bits Q C G U))
    (containerStart G.length d r) 0 r ys (parkedInput_parked _) rfl rfl
  rw [container_maskClauses Q C G U] at h
  rw [Nat.zero_add, Nat.mul_zero, Nat.add_zero] at h
  exact h

theorem foodScan_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) (ys : List Bool) :
    maskScanTM.HoareTime
      (EmitPred (parkedInput (bits Q C G U))
        (maskWork (regTape d) (foodStart G.length d r) r 0) ys)
      (EmitPred (parkedInput (bits Q C G U))
        (maskWork (regTape d) (foodStart G.length d r+d) (r+d) 0)
        (ys++SAT.CNF.encode (PositiveCompletionCNF.each d (fun x =>
          if x ∈ Q.food then [] else
            [PositiveCompletionCNF.negative [PositiveCompletionCNF.rowVar r ⟨0,by omega⟩ x]]))))
      (d*(5*foodStart G.length d r+5*r+10*d+53)+d+2) := by
  have h := maskScanTM_correct (parkedInput (bits Q C G U))
    (foodStart G.length d r) r d ys (parkedInput_parked _) rfl rfl
  rw [food_maskClauses Q C G U] at h
  exact h

end IrrRAFEnumeration.CompletionQuery
