module

public import proofs.UnconstrainedPACDetection.FormulaAllSwitchHeads
public import proofs.UnconstrainedPACDetection.FormulaMergedHeads

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchTailHeads
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open FormulaSwitchVariableHeads (bank parked)
open FormulaChangingFrame (extend)

def frame (i v j r a b f L V g C h : Nat) : Fin 21 → Tape :=
  extend (bank i v j r a b f L V g C) (regTape h)

theorem frame_parked (i v j r a b f L V g C h : Nat) : ∀ t, Parked (frame i v j r a b f L V g C h t) :=
  FormulaChangingFrame.parked _ _ (parked _ _ _ _ _ _ _ _ _ _ _) (parked_regTape _)

def recycleBank (i r a L V C : Nat) : Fin 21 → Tape :=
  extend (FormulaSwitchVariableHeads.extend (FormulaClauseHeadLoop.bank i C r a
    (FormulaRailBase.value L V V false+C) L V C (regTape C))) (regTape (L-1))

theorem recycle_hoare (i r a L V C : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    (clearRegTM (3 : Fin 21)).HoareTime (EmitPred inp (recycleBank i r a L V C) ys)
      (EmitPred inp (frame i V (L+1) r a (FormulaRailBase.value L V V false+C) (L+1) L V C C (L-1)) ys)
      (2*C+4) := by
  have hp : ∀ t, Parked (recycleBank i r a L V C t) :=
    FormulaChangingFrame.parked _ _ (FormulaSwitchVariableHeads.extend_parked _
      (FormulaClauseHeadLoop.parked _ _ _ _ _ _ _ _ _ (parked_regTape _))) (parked_regTape _)
  have h := clearRegTM_hoareTime (3 : Fin 21) C inp (recycleBank i r a L V C) ys hi (fun t _ => hp t) rfl
  have he : Function.update (recycleBank i r a L V C) 3 (regTape 0) =
      frame i V (L+1) r a (FormulaRailBase.value L V V false+C) (L+1) L V C C (L-1) := by
    funext t; fin_cases t <;> simp [recycleBank,frame,extend,bank,FormulaSwitchVariableHeads.extend,
      FormulaClauseHeadLoop.bank,FormulaRailClauseHeads.extend,FormulaAllRailHeads.raw,
      FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
    exact (FormulaEndpointRegisters.unary_word 0).symm
  rw [he] at h
  exact h

def machine (p : ControlSwitch.V) (right : Bool) (rt ta : Option Bool) : TM 21 :=
  seqTM (clearRegTM 11)
    (seqTM (placeWorkTM 0 1 (FormulaMergedHeads.machine p right rt ta))
      (seqTM (FormulaAllSwitchHeads.machine p right (choose right rt ta none))
        (seqTM (placeWorkTM 0 1 (FormulaSwitchVariableHeads.machine p right (choose right rt ta none)))
          (clearRegTM 3))))

def bits (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) : List Bool :=
  FormulaMergedHeads.field φ right r a false ++ FormulaMergedHeads.field φ right r a true ++
  FormulaAllSwitchHeads.bits φ i p right (choose right (tag r) (tag a) none) (index r) (index a) ++
  FormulaSwitchVariableHeads.field φ right r a 0 ++
  FormulaRailHeadVariables.bits φ right r a (varCount φ) ++ FormulaClauseHeadLoop.bits φ right r a φ.length

def budget (φ : SAT.CNF) (i v j b h : Nat) : Nat :=
  (2*b+4)+1+
  (2*φ.length^2+15*φ.length+20*φ.encode.length+7*i+6*(FormulaIndexedGraph.labels φ).length+247)+1+
  (2*(levels φ)^2+9*levels φ+2*h+2*j+18+FormulaAllSwitchHeads.readyBudget φ)+1+
  (2*v+4*i+3*levels φ+3*(FormulaIndexedGraph.labels φ).length+FormulaRailClauseHeads.budget φ+106)+1+
  (2*φ.length+4)

/-- One actual reentrant switch-tail head machine. The separate ordered-list docking
    identifies `bits` with the canonical head scan; this theorem proves execution. -/
theorem hoare (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (v j b f g h : Nat) (ys : List Bool)
    (hf : f ≤ 100*(φ.encode.length+2)^2) (hg : g ≤ 100*(φ.encode.length+2)^2) :
    (machine p right (tag r) (tag a)).HoareTime
      (EmitPred (word φ.encode) (frame i.val v j (index r) (index a) b f (levels φ) (varCount φ) g φ.length h) ys)
      (EmitPred (word φ.encode)
        (frame i.val (varCount φ) (levels φ+1) (index r) (index a) (FormulaClauseCursor.base φ+φ.length)
          (levels φ+1) (levels φ) (varCount φ) φ.length φ.length (levels φ-1))
        (ys ++ bits φ i p right r a)) (budget φ i.val v j b h) := by
  have h0 := clearRegTM_hoareTime (11 : Fin 21) b (word φ.encode)
    (frame i.val v j (index r) (index a) b f (levels φ) (varCount φ) g φ.length h) ys
    (word_parked _) (fun t _ => frame_parked _ _ _ _ _ _ _ _ _ _ _ _ t) rfl
  have he : Function.update (frame i.val v j (index r) (index a) b f (levels φ) (varCount φ) g φ.length h) 11 (regTape 0) =
      frame i.val v j (index r) (index a) 0 f (levels φ) (varCount φ) g φ.length h := by
    funext t; fin_cases t <;> simp [frame,extend,bank,FormulaSwitchVariableHeads.extend,
      FormulaRailClauseHeads.extend,FormulaAllRailHeads.raw,FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he] at h0
  have hm := FormulaMergedHeads.canonical_hoare φ i p right r a ha v j f g ys
  have h1 := FormulaChangingFrame.append_hoare _ _ _ _ (regTape h) _ _ _
    (parked _ _ _ _ _ _ _ _ _ _ _) (parked_regTape _) hm
  let z1 := ys ++ FormulaMergedHeads.field φ right r a false ++ FormulaMergedHeads.field φ right r a true
  have h2 := FormulaAllSwitchHeads.hoare φ i p right (choose right (tag r) (tag a) none)
    v j (index r) (index a) f g h (FormulaCoefficientRound.index_bound r) (FormulaCoefficientRound.index_bound a) z1
  let z2 := z1 ++ FormulaAllSwitchHeads.bits φ i p right (choose right (tag r) (tag a) none) (index r) (index a)
  have hL := (FormulaEnumeration.parameter_bounds φ).1
  have hv := FormulaSwitchVariableHeads.canonical_hoare φ i p right r a ha v (levels φ) f g z2 (by nlinarith) hf hg
  have h3 := FormulaChangingFrame.append_hoare _ _ _ _ (regTape (levels φ-1)) _ _ _
    (parked _ _ _ _ _ _ _ _ _ _ _) (parked_regTape _) hv
  have h4 := recycle_hoare i.val (index r) (index a) (levels φ) (varCount φ) φ.length (word φ.encode) (word_parked _)
    (z2 ++ FormulaSwitchVariableHeads.field φ right r a 0 ++ FormulaRailHeadVariables.bits φ right r a (varCount φ) ++
      FormulaClauseHeadLoop.bits φ right r a φ.length)
  have h34 := seqTM_hoareTime _ _ h3 (emitPred_transition (word_parked _)
    (FormulaChangingFrame.parked _ _ (FormulaSwitchVariableHeads.extend_parked _
      (FormulaClauseHeadLoop.parked _ _ _ _ _ _ _ _ _ (parked_regTape _))) (parked_regTape _)) _) h4
  have h234 := seqTM_hoareTime _ _ h2 (emitPred_transition (word_parked _) (frame_parked _ _ _ _ _ _ _ _ _ _ _ _) _) h34
  have h1234 := seqTM_hoareTime _ _ h1 (emitPred_transition (word_parked _) (frame_parked _ _ _ _ _ _ _ _ _ _ _ _) _) h234
  have hx := seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _) (frame_parked _ _ _ _ _ _ _ _ _ _ _ _) _) h1234
  have hx' := hx.mono_bound (show _ ≤ budget φ i.val v j b h by unfold budget; omega)
  simpa only [machine,z1,z2,bits,FormulaClauseCursor.base,List.append_assoc] using hx'

end UnconstrainedPACDetection.FormulaSwitchTailHeads
