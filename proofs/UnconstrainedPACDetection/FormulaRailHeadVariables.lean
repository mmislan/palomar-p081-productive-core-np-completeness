module

public import proofs.UnconstrainedPACDetection.FormulaRailHeadSigns

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailHeadVariables
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)

def extend (w : Fin 17 → Tape) (fuel : Tape) (t : Fin 18) : Tape :=
  if h : t.val < 17 then w ⟨t.val,h⟩ else fuel

theorem extend_parked (w : Fin 17 → Tape) (fuel : Tape)
    (hp : ∀ t, Parked (w t)) (hf : Parked fuel) : ∀ t, Parked (extend w fuel t) := by
  intro t; unfold extend; split
  · exact hp _
  · exact hf

/-- Placement of the changing inner frame preserves the parked outer-loop fuel. -/
theorem lift_hoare (m : TM 17) (inp : Tape) (w z : Fin 17 → Tape)
    (fuel : Tape) (ys zs : List Bool) (B : Nat)
    (hp : ∀ t, Parked (w t)) (hf : Parked fuel)
    (h : m.HoareTime (EmitPred inp w ys) (EmitPred inp z zs) B) :
    (placeWorkTM 0 1 m).HoareTime
      (EmitPred inp (extend w fuel) ys) (EmitPred inp (extend z fuel) zs) B := by
  rintro i work out ⟨rfl,rfl,ho⟩
  obtain ⟨d,t,ht,hr,hh,hi,hw,hout⟩ := h _ _ out ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal m 0 1 (extend w fuel) hr
    (by intro q _; exact (extend_parked w fuel hp hf q).read_ne_start)
  refine ⟨placeWorkCfg m 0 1 (extend w fuel) d,t,ht,?_,hh,hi,?_,hout⟩
  · convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext q; fin_cases q <;> simp [placeWorkCfg,placeWorkInMiddle,extend] <;> rfl
    · rfl
  · funext q; fin_cases q <;> simp [placeWorkCfg,placeWorkInMiddle,extend,hw] <;> rfl

def bank (i v r a L V : Nat) (fuel : Tape) : Fin 18 → Tape :=
  extend (FormulaRailHeadPrepare.bank i v (L+1) r a
    (FormulaRailBase.value L V v false) (L+1) L V) fuel

theorem parked (i v r a L V : Nat) (fuel : Tape) (hf : Parked fuel) :
    ∀ t, Parked (bank i v r a L V fuel t) :=
  extend_parked _ _ (FormulaRailHeadPrepare.parked _ _ _ _ _ _ _ _ _) hf

def body (p : ControlSwitch.V) (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 18 :=
  seqTM (placeWorkTM 0 1 (FormulaRailHeadSigns.machine p right plan)) (incRegTM 5)

theorem body_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (v : Fin (varCount φ))
    (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (fuel : Tape) (hf : Parked fuel) (ys : List Bool) :
    (body p right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank i.val v.val (index r) (index a) (levels φ) (varCount φ) fuel) ys)
      (EmitPred (word φ.encode) (bank i.val (v.val+1) (index r) (index a) (levels φ) (varCount φ) fuel)
        (ys ++ FormulaRailHeadSigns.bits φ v right r a))
      (2*FormulaRailHeadSigns.budget φ.encode.length+2*v.val+6) := by
  have hL : levels φ+1 ≤ 100*(φ.encode.length+2)^2 := by
    have h := (FormulaEnumeration.parameter_bounds φ).1
    nlinarith
  have hb : FormulaRailBase.value (levels φ) (varCount φ) v.val false ≤
      100*(φ.encode.length+2)^2 := by
    have h := FormulaRailHeadSigns.end_bound φ v false
    omega
  have hs := FormulaRailHeadSigns.canonical_hoare φ i v p right r a ha
    (levels φ+1) (FormulaRailBase.value (levels φ) (varCount φ) v.val false) (levels φ+1)
    ys hL hb hL
  have hl := lift_hoare _ _ _ _ fuel _ _ _
    (FormulaRailHeadPrepare.parked _ _ _ _ _ _ _ _ _) hf hs
  let mid := extend (FormulaRailHeadPrepare.bank i.val v.val (levels φ+1) (index r) (index a)
    (FormulaRailBase.value (levels φ) (varCount φ) (v.val+1) false) (levels φ+1) (levels φ) (varCount φ)) fuel
  have hmp : ∀ t, Parked (mid t) := extend_parked _ _ (FormulaRailHeadPrepare.parked _ _ _ _ _ _ _ _ _) hf
  have hi := incRegTM_hoareTime (5 : Fin 18) v.val (word φ.encode) mid
    (ys ++ FormulaRailHeadSigns.bits φ v right r a) (word_parked _) (fun t _ => hmp t) rfl
  have he : Function.update mid 5 (regTape (v.val+1)) =
      bank i.val (v.val+1) (index r) (index a) (levels φ) (varCount φ) fuel := by
    funext t; fin_cases t <;> simp [mid,bank,extend,FormulaRailHeadPrepare.bank]
  rw [he] at hi
  exact (seqTM_hoareTime _ _ hl (emitPred_transition (word_parked _) hmp _) hi).mono_bound (by omega)

def field (φ : SAT.CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  if h : k < varCount φ then FormulaRailHeadSigns.bits φ ⟨k,h⟩ right r a else []

def bits (φ : SAT.CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  (List.range k).flatMap (field φ right r a)

def machine (p : ControlSwitch.V) (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 18 :=
  forRegTM (body p right plan) 17

/-- All rail heads, across all variables and both signs, execute in canonical
    order. The variable counter advances physically; outer fuel is restored. -/
theorem canonical_hoare (φ : SAT.CNF) (i : Fin (levels φ))
    (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (ys : List Bool) :
    (machine p right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank i.val 0 (index r) (index a) (levels φ) (varCount φ) (regTape (varCount φ))) ys)
      (EmitPred (word φ.encode)
        (bank i.val (varCount φ) (index r) (index a) (levels φ) (varCount φ) (regTape (varCount φ)))
        (ys ++ bits φ right r a (varCount φ)))
      (varCount φ * (2*FormulaRailHeadSigns.budget φ.encode.length+2*varCount φ+8)+(varCount φ+2)) := by
  let V := varCount φ
  let w := fun k => bank i.val k (index r) (index a) (levels φ) V (regTape V)
  let zs := fun k => ys ++ bits φ right r a k
  have h := forRegTM_hoareTime (body p right (choose right (tag r) (tag a) none))
    (17 : Fin 18) V (word φ.encode) w zs
    (2*FormulaRailHeadSigns.budget φ.encode.length+2*V+6) (word_parked _)
    (by intro k; rfl) (by intro k t _; exact parked _ _ _ _ _ _ _ (parked_regTape V) t) (by
      intro k hk
      let fuel : Tape := ⟨k+2,regCells V⟩
      have hf : Parked fuel := parked_regCells (by omega)
      have he (z : Nat) : Function.update (w z) 17 fuel =
          bank i.val z (index r) (index a) (levels φ) V fuel := by
        funext t; fin_cases t <;> simp [w,bank,extend]
      have hb := body_hoare φ i ⟨k,hk⟩ p right r a ha fuel hf (zs k)
      have hfield : field φ right r a k = FormulaRailHeadSigns.bits φ ⟨k,hk⟩ right r a := by
        unfold field; split
        · rfl
        · next hn => exact (hn hk).elim
      have hy : zs (k+1) = zs k ++ FormulaRailHeadSigns.bits φ ⟨k,hk⟩ right r a := by
        simp [zs,bits,List.range_succ,List.flatMap_append,hfield,List.append_assoc]
      rw [he,he,hy]
      exact hb.mono_bound (by omega))
  simpa only [machine,w,zs,bits,List.range_zero,List.flatMap_nil,List.append_nil,Nat.add_assoc,V] using h

end UnconstrainedPACDetection.FormulaRailHeadVariables
