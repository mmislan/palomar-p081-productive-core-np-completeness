module

public import proofs.UnconstrainedPACDetection.FormulaSwitchTailBoundary
public import proofs.UnconstrainedPACDetection.FormulaRuntimeBranch

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchTailGate
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (tag index)
open FormulaSwitchTailReentrant (frame parked)
open FormulaVertexTailFields (vertex)

def guarded (last : Bool) (p : ControlSwitch.V) (right : Bool) (rt : Option Bool) : TM 21 :=
  seqTM (FormulaSwitchTailBoundary.query last)
    (FormulaNegativeGate.gate (FormulaSwitchTailReentrant.machine p right rt none))

def machine (p : ControlSwitch.V) (right : Bool) (rt : Option Bool) : TM 21 :=
  if p=0 then guarded true p right rt else
  if p=1 ∨ p=4 then guarded false p right rt else
  FormulaSwitchTailReentrant.machine p right rt none

def budget (φ : SAT.CNF) : Nat := FormulaSwitchTailReentrant.budget φ+7*levels φ+38

theorem guarded_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V)
    (last right : Bool) (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (hgood : ¬(i.val+(if last then 1 else 0)=(if last then levels φ else 0)) →
      FormulaSwitchTailPort.Admissible φ i p)
    (hbad : i.val+(if last then 1 else 0)=(if last then levels φ else 0) →
      vertex φ right r (SwitchStack.sw i p)=[]) (ys : List Bool) :
    (guarded last p right (tag r)).HoareTime
      (EmitPred (word φ.encode) (frame i.val (index r) (20*i.val+p.val) (levels φ) (varCount φ) φ.length) ys)
      (EmitPred (word φ.encode) (frame i.val (index r) (20*i.val+p.val) (levels φ) (varCount φ) φ.length)
        (ys ++ vertex φ right r (SwitchStack.sw i p))) (budget φ) := by
  have hp := parked i.val (index r) (20*i.val+p.val) (levels φ) (varCount φ) φ.length
  have hq := FormulaSwitchTailBoundary.query_hoare last i.val (index r) (20*i.val+p.val)
    (levels φ) (varCount φ) φ.length (word φ.encode) (word_parked _) ys
  have hib := i.isLt
  have hbound : 4*i.val+3*max (i.val+1) (if last then levels φ else 0)+32 ≤ 7*levels φ+35 := by
    cases last <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  by_cases hb : i.val+(if last then 1 else 0)=(if last then levels φ else 0)
  · simp only [hb,decide_true] at hq
    have hg := FormulaRuntimeBranch.negative_skip
      (FormulaSwitchTailReentrant.machine p right (tag r) none) (word φ.encode) _ ys (word_parked _) hp
    have h := seqTM_hoareTime _ _ hq (emitPred_transition (word_parked _) hp _) hg
    simpa only [guarded,hbad hb,List.append_nil] using h.mono_bound (show _ ≤ budget φ by unfold budget; omega)
  · simp only [hb,decide_false] at hq
    have hc := FormulaSwitchTailPort.hoare φ i p (hgood hb) right r ys
    have hg := FormulaNegativeGate.gate_hoare _ false _ _ ys _ _ (word_parked _) hp hc
    simp only [Bool.false_eq_true,ite_false] at hg
    have h := seqTM_hoareTime _ _ hq (emitPred_transition (word_parked _) hp _) hg
    exact h.mono_bound (by unfold budget; omega)

theorem hoare (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ys : List Bool) :
    (machine p right (tag r)).HoareTime
      (EmitPred (word φ.encode) (frame i.val (index r) (20*i.val+p.val) (levels φ) (varCount φ) φ.length) ys)
      (EmitPred (word φ.encode) (frame i.val (index r) (20*i.val+p.val) (levels φ) (varCount φ) φ.length)
        (ys ++ vertex φ right r (SwitchStack.sw i p))) (budget φ) := by
  by_cases h0 : p=0
  · subst p
    simpa only [machine,ite_eq_left rfl,ite_true] using guarded_hoare φ i 0 true right r
      (by intro h; exact ⟨fun _ => h,by simp,by simp [Fin.ext_iff]⟩)
      (by simpa using FormulaSwitchTailPort.last_source φ i (right := right) (r := r)) ys
  · by_cases h1 : p=1
    · subst p
      have hn : (1 : ControlSwitch.V) ≠ 0 := by decide
      simpa only [machine,ite_eq_right hn,ite_eq_left (Or.inl rfl),true_or,ite_true] using guarded_hoare φ i 1 false right r
        (by intro h; exact ⟨by simp,fun _ => h,by simp [Fin.ext_iff]⟩)
        (by simpa using FormulaSwitchTailPort.first_source φ i (right := right) (r := r)) ys
    · by_cases h4 : p=4
      · subst p
        have hn : (4 : ControlSwitch.V) ≠ 0 := by decide
        simpa only [machine,ite_eq_right hn,ite_eq_left (Or.inr rfl),or_true,ite_true] using guarded_hoare φ i 4 false right r
          (by intro h; exact ⟨by simp [Fin.ext_iff],by simp [Fin.ext_iff],fun _ => h⟩)
          (by simpa using FormulaSwitchTailPort.first_sink φ i (right := right) (r := r)) ys
      · have hc := FormulaSwitchTailPort.hoare φ i p
          ⟨fun h => False.elim (h0 h),fun h => False.elim (h1 h),fun h => False.elim (h4 h)⟩ right r ys
        simpa only [machine,ite_eq_right h0,ite_eq_right (not_or.mpr ⟨h1,h4⟩)] using
          hc.mono_bound (show FormulaSwitchTailReentrant.budget φ ≤ budget φ by unfold budget; omega)

end UnconstrainedPACDetection.FormulaSwitchTailGate
