module

public import proofs.UnconstrainedPACDetection.FormulaRailBaseRegisters

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailHeadPrepare
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)

def bank (i v j r a b f L V : Nat) : Fin 17 → Tape :=
  ![regTape i,word [],word [],word [],word [],regTape v,regTape j,word [],word [true],
    regTape r,regTape a,regTape b,word [],word [true],regTape f,regTape L,regTape V]

theorem parked (i v j r a b f L V : Nat) : ∀ t, Parked (bank i v j r a b f L V t) := by
  intro t; fin_cases t
  all_goals first | exact parked_regTape _ | exact word_parked _

def reset : TM 17 := seqTM (clearRegTM 6) (seqTM (copyIntoTM 15 14) (incRegTM 14))

theorem reset_hoare (i v j r a b f L V M : Nat) (inp : Tape) (ys : List Bool)
    (hi : Parked inp) (hj : j ≤ M) (hf : f ≤ M) (hL : L ≤ M) :
    reset.HoareTime (EmitPred inp (bank i v j r a b f L V) ys)
      (EmitPred inp (bank i v 0 r a b (L+1) L V) ys) (3*opBudget M+2) := by
  have h1 := clearRegTM_hoareTime (6 : Fin 17) j inp (bank i v j r a b f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl
  have he1 : Function.update (bank i v j r a b f L V) 6 (regTape 0) =
      bank i v 0 r a b f L V := by funext t; fin_cases t <;> simp [bank]
  rw [he1] at h1
  have h1' := h1.mono_bound (clearRegTM_le_opBudget hj)
  have h2 := copyIntoTM_hoareTime (15 : Fin 17) 14 (by decide) L f inp
    (bank i v 0 r a b f L V) ys hi (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl rfl
  have he2 : Function.update (bank i v 0 r a b f L V) 14 (regTape L) =
      bank i v 0 r a b L L V := by funext t; fin_cases t <;> simp [bank]
  rw [he2] at h2
  have h2' := h2.mono_bound (copyIntoTM_le_opBudget hL hf)
  have h3 := incRegTM_hoareTime (14 : Fin 17) L inp (bank i v 0 r a b L L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl
  have he3 : Function.update (bank i v 0 r a b L L V) 14 (regTape (L+1)) =
      bank i v 0 r a b (L+1) L V := by funext t; fin_cases t <;> simp [bank]
  rw [he3] at h3
  have h3' := h3.mono_bound (incRegTM_le_opBudget hL)
  have h23 := seqTM_hoareTime _ _ h2' (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h3'
  exact (seqTM_hoareTime _ _ h1' (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h23).mono_bound (by omega)

def prepare (s : Bool) : TM 17 := seqTM (FormulaRailBaseRegisters.machine s) reset

/-- Cursor, base and fuel are physically prepared, including when stale values are present. -/
theorem prepare_hoare (i v j r a b f L V M : Nat) (s : Bool) (inp : Tape) (ys : List Bool)
    (hi : Parked inp) (hj : j ≤ M) (hb : b ≤ M) (hf : f ≤ M) (hL : L ≤ M)
    (hV : V ≤ M) (hv : v ≤ M) (hbase : FormulaRailBase.value L V v s ≤ M) :
    (prepare s).HoareTime (EmitPred inp (bank i v j r a b f L V) ys)
      (EmitPred inp (bank i v 0 r a (FormulaRailBase.value L V v s) (L+1) L V) ys)
      (44*(opBudget M+1)) := by
  have h1 := FormulaRailBaseRegisters.arithmetic_hoare L V v b M s inp
    (bank i v j r a b f L V) ys hi (parked _ _ _ _ _ _ _ _ _) rfl rfl rfl rfl hL hV hv hb hbase
  have he : FormulaRailBaseRegisters.bank (bank i v j r a b f L V) (FormulaRailBase.value L V v s) =
      bank i v j r a (FormulaRailBase.value L V v s) f L V := by
    funext t; fin_cases t <;> simp [FormulaRailBaseRegisters.bank,bank]
  rw [he] at h1
  have h2 := reset_hoare i v j r a (FormulaRailBase.value L V v s) f L V M inp ys hi hj hf hL
  exact (seqTM_hoareTime _ _ h1 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _) _) h2).mono_bound (by omega)

def scan (p : ControlSwitch.V) (s right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 17 :=
  placeWorkTM 0 2 (FormulaRailHeadLoop.machine p s right plan)

/-- Lift the whole changing cursor frame while preserving live dimensions. -/
theorem scan_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (v : Fin (varCount φ))
    (p : ControlSwitch.V) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (ys : List Bool) :
    (scan p s right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode)
        (bank i.val v.val 0 (index r) (index a) (FormulaRailBase.value (levels φ) (varCount φ) v.val s)
          (levels φ+1) (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode)
        (bank i.val v.val (levels φ+1) (index r) (index a)
          (FormulaRailBase.value (levels φ) (varCount φ) v.val s+(levels φ+1))
          (levels φ+1) (levels φ) (varCount φ))
        (ys ++ FormulaRailHeadLoop.bits φ v s right r a (levels φ+1)))
      (500*(φ.encode.length+2)^3) := by
  obtain ⟨pre,post,hblock,hbase⟩ := FormulaRailBase.factor φ v s
  have h := FormulaRailHeadLoop.polynomial_hoare φ i v p s right r a ha pre post hblock ys
  rw [hbase] at h
  let base := FormulaRailBase.value (levels φ) (varCount φ) v.val s
  let large := bank i.val v.val 0 (index r) (index a) base (levels φ+1) (levels φ) (varCount φ)
  rintro inp work out ⟨rfl,rfl,ho⟩
  obtain ⟨d,t,ht,hr,hh,hi,hw,hout⟩ := h _ _ out ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    (FormulaRailHeadLoop.machine p s right (choose right (tag r) (tag a) none))
    0 2 large hr (by intro q _; exact (parked _ _ _ _ _ _ _ _ _ q).read_ne_start)
  refine ⟨placeWorkCfg _ 0 2 large d,t,ht,?_,hh,hi,?_,hout⟩
  · unfold scan
    convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext q; fin_cases q <;> simp [placeWorkCfg,placeWorkInMiddle,large,bank,
        FormulaRailHeadLoop.bank,base] <;> rfl
    · rfl
  · funext q; fin_cases q <;> simp [placeWorkCfg,placeWorkInMiddle,large,bank,
      FormulaRailHeadLoop.bank,hw,base] <;> rfl

def machine (p : ControlSwitch.V) (s right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 17 :=
  seqTM (prepare s) (scan p s right plan)

/-- The rail-head scan consumes live dimensions and a variable counter; it no
    longer assumes the canonical base, cursor zero, or correct fuel at entry. -/
theorem staged_scan_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (v : Fin (varCount φ))
    (p : ControlSwitch.V) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (j b f : Nat) (ys : List Bool)
    (hj : j ≤ 100*(φ.encode.length+2)^2) (hb : b ≤ 100*(φ.encode.length+2)^2)
    (hf : f ≤ 100*(φ.encode.length+2)^2) :
    (machine p s right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode)
        (bank i.val v.val j (index r) (index a) b f (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode)
        (bank i.val v.val (levels φ+1) (index r) (index a)
          (FormulaRailBase.value (levels φ) (varCount φ) v.val s+(levels φ+1))
          (levels φ+1) (levels φ) (varCount φ))
        (ys ++ FormulaRailHeadLoop.bits φ v s right r a (levels φ+1)))
      (44*(opBudget (100*(φ.encode.length+2)^2)+1)+1+500*(φ.encode.length+2)^3) := by
  let M := 100*(φ.encode.length+2)^2
  obtain ⟨hL,hV,_⟩ := FormulaEnumeration.parameter_bounds φ
  have hv := v.isLt
  obtain ⟨pre,post,hblock,hbase⟩ := FormulaRailBase.factor φ v s
  have hidx := FormulaRailCursor.port_index φ v s pre post hblock ⟨0,by omega⟩
  have hn := FormulaCoefficientRound.index_bound (FormulaRailCursor.port φ v s ⟨0,by omega⟩)
  rw [hidx,Nat.add_zero,hbase] at hn
  have hN := FormulaIndexedGraph.labels_bound φ
  have hp := prepare_hoare i.val v.val j (index r) (index a) b f (levels φ) (varCount φ) M s
    (word φ.encode) ys (word_parked _) hj hb hf
    (by dsimp [M]; nlinarith) (by dsimp [M]; nlinarith) (by dsimp [M]; nlinarith)
    (by dsimp [M]; nlinarith)
  exact seqTM_hoareTime _ _ hp (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _) _)
    (scan_hoare φ i v p s right r a ha ys)

end UnconstrainedPACDetection.FormulaRailHeadPrepare
