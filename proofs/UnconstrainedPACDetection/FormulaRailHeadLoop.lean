module

public import proofs.UnconstrainedPACDetection.FormulaRailCursor
public import proofs.Complexitylib.Models.TuringMachine.Registers.ForReg

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailHeadLoop
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning place_hoare)

def bank (i v j r a b : Nat) (fuel : Tape) : Fin 15 → Tape :=
  ![regTape i,word [],word [],word [],word [],regTape v,regTape j,word [],word [true],
    regTape r,regTape a,regTape b,word [],word [true],fuel]

theorem parked (i v j r a b : Nat) (fuel : Tape) (hf : Parked fuel) :
    ∀ t, Parked (bank i v j r a b fuel t) := by
  intro t; fin_cases t
  all_goals first | exact parked_regTape _ | exact word_parked _ | exact hf

def round (p : ControlSwitch.V) (s right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 15 :=
  placeWorkTM 0 1 (FormulaSwitchRailPair.machine p s right plan)

def advance : TM 15 := seqTM (incRegTM 6) (incRegTM 11)

theorem advance_hoare (i v j r a b : Nat) (fuel : Tape) (hf : Parked fuel)
    (inp : Tape) (hi : Parked inp) (ys : List Bool) : advance.HoareTime
    (EmitPred inp (bank i v j r a b fuel) ys)
    (EmitPred inp (bank i v (j+1) r a (b+1) fuel) ys) (2*j+2*b+9) := by
  have h1 := incRegTM_hoareTime (6 : Fin 15) j inp (bank i v j r a b fuel) ys hi
    (fun t _ => parked i v j r a b fuel hf t) rfl
  have he1 : Function.update (bank i v j r a b fuel) 6 (regTape (j+1)) =
      bank i v (j+1) r a b fuel := by
    funext t; fin_cases t <;> simp [bank]
  rw [he1] at h1
  have h2 := incRegTM_hoareTime (11 : Fin 15) b inp (bank i v (j+1) r a b fuel) ys hi
    (fun t _ => parked i v (j+1) r a b fuel hf t) rfl
  have he2 : Function.update (bank i v (j+1) r a b fuel) 11 (regTape (b+1)) =
      bank i v (j+1) r a (b+1) fuel := by
    funext t; fin_cases t <;> simp [bank]
  rw [he2] at h2
  exact (seqTM_hoareTime _ _ h1 (emitPred_transition hi (parked _ _ _ _ _ _ _ hf) _) h2).mono_bound (by omega)

def body (p : ControlSwitch.V) (s right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 15 :=
  seqTM (round p s right plan) advance

def machine (p : ControlSwitch.V) (s right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 15 :=
  forRegTM (body p s right plan) 14

def field (φ : SAT.CNF) (v : Fin (varCount φ)) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (j : Nat) : List Bool :=
  if hj : j < levels φ+1 then
    let b := FormulaRailCursor.port φ v s ⟨j,hj⟩
    if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ) (FormulaIndexedGraph.terminals φ) (a,b)
    then BinaryFields.encodeField (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits
    else []
  else []

def bits (φ : SAT.CNF) (v : Fin (varCount φ)) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  (List.range k).flatMap (field φ v s right r a)

/-- Actual canonical fields over one entire rail-head block. The loop advances both
    indices, retains the caller prefix, and restores its independent fuel register. -/
theorem canonical_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (v : Fin (varCount φ))
    (p : ControlSwitch.V) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p)
    (pre post : List (FormulaWiring.Vertex φ))
    (hblock : pre ++ FormulaRailCursor.block φ v s ++ post = FormulaIndexedGraph.labels φ)
    (ys : List Bool) :
    (machine p s right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode)
        (bank i.val v.val 0 (index r) (index a) pre.length (regTape (levels φ+1))) ys)
      (EmitPred (word φ.encode)
        (bank i.val v.val (levels φ+1) (index r) (index a) (pre.length+(levels φ+1))
          (regTape (levels φ+1)))
        (ys ++ bits φ v s right r a (levels φ+1)))
      ((levels φ+1) * (24*φ.encode.length+26*v.val+4*i.val+
        3*max (i.val+1) (levels φ+1)+5*(FormulaIndexedGraph.labels φ).length+
        2*(levels φ+1)+264) + (levels φ+3)) := by
  let L := levels φ+1
  let N := (FormulaIndexedGraph.labels φ).length
  let w := fun k => bank i.val v.val k (index r) (index a) (pre.length+k) (regTape L)
  let zs := fun k => ys ++ bits φ v s right r a k
  have h := forRegTM_hoareTime (body p s right (choose right (tag r) (tag a) none))
    (14 : Fin 15) L (word φ.encode) w zs
    (24*φ.encode.length+26*v.val+4*i.val+3*max (i.val+1) L+5*N+2*L+262)
    (word_parked _) (by intro k; rfl)
    (by intro k t _; exact parked _ _ _ _ _ _ _ (parked_regTape L) t) (by
      intro k hk
      let fuel : Tape := ⟨k+2,regCells L⟩
      have hf : Parked fuel := parked_regCells (by omega)
      have he (t : Nat) : Function.update (w t) 14 fuel =
          bank i.val v.val t (index r) (index a) (pre.length+t) fuel := by
        funext q; fin_cases q <;> simp [w,bank]
      let b := FormulaRailCursor.port φ v s ⟨k,hk⟩
      have hb : index b = pre.length+k := FormulaRailCursor.port_index φ v s pre post hblock ⟨k,hk⟩
      have ht : tag b = none := rfl
      have hq := FormulaSwitchRailPair.canonical_hoare φ i v ⟨k,hk⟩ p s right r a b ha
        (FormulaRailCursor.port_meaning φ v s ⟨k,hk⟩) (zs k)
      rw [hb,ht] at hq
      have hround := place_hoare _ 0 1 _ _
        (bank i.val v.val k (index r) (index a) (pre.length+k) fuel) _ _ _
        (parked _ _ _ _ _ _ _ hf) (by intro t; fin_cases t <;> rfl) hq
      have hfield : field φ v s right r a k =
          if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
            (FormulaIndexedGraph.terminals φ) (a,b) then BinaryFields.encodeField
              (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits
          else [] := by
        unfold field
        split
        · rfl
        · next hn => exact (hn hk).elim
      rw [← hfield] at hround
      have hstep := seqTM_hoareTime _ _ hround
        (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ hf) _)
        (advance_hoare i.val v.val k (index r) (index a) (pre.length+k) fuel hf
          (word φ.encode) (word_parked _) (zs k ++ field φ v s right r a k))
      have hy : zs (k+1) = zs k ++ field φ v s right r a k := by
        simp [zs,bits,List.range_succ,List.flatMap_append,List.append_assoc]
      rw [he,he,hy]
      have hbn := FormulaCoefficientRound.index_bound b
      rw [hb] at hbn
      have hs : pre.length+k+1 = pre.length+(k+1) := by omega
      rw [hs] at hstep
      exact hstep.mono_bound (by dsimp only [N,L] at *; omega))
  simpa only [machine,w,zs,bits,List.range_zero,List.flatMap_nil,List.append_nil,
    Nat.add_zero,L,N,Nat.add_assoc] using h

theorem polynomial_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (v : Fin (varCount φ))
    (p : ControlSwitch.V) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p)
    (pre post : List (FormulaWiring.Vertex φ))
    (hblock : pre ++ FormulaRailCursor.block φ v s ++ post = FormulaIndexedGraph.labels φ)
    (ys : List Bool) :
    (machine p s right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode)
        (bank i.val v.val 0 (index r) (index a) pre.length (regTape (levels φ+1))) ys)
      (EmitPred (word φ.encode)
        (bank i.val v.val (levels φ+1) (index r) (index a) (pre.length+(levels φ+1))
          (regTape (levels φ+1))) (ys ++ bits φ v s right r a (levels φ+1)))
      (500*(φ.encode.length+2)^3) := by
  apply (canonical_hoare φ i v p s right r a ha pre post hblock ys).mono_bound
  obtain ⟨hL,hV,_⟩ := FormulaEnumeration.parameter_bounds φ
  have hN := FormulaIndexedGraph.labels_bound φ
  have hi := i.isLt
  have hv := v.isLt
  have hm : max (i.val+1) (levels φ+1) ≤ φ.encode.length+2 := by omega
  have hb : 24*φ.encode.length+26*v.val+4*i.val+
      3*max (i.val+1) (levels φ+1)+5*(FormulaIndexedGraph.labels φ).length+
      2*(levels φ+1)+264 ≤ 400*(φ.encode.length+2)^2 := by nlinarith
  have hp := Nat.mul_le_mul (show levels φ+1 ≤ φ.encode.length+2 by omega) hb
  nlinarith [sq_nonneg (φ.encode.length : Int)]

end UnconstrainedPACDetection.FormulaRailHeadLoop
