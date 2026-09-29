module

public import proofs.UnconstrainedPACDetection.FormulaRailHeadVariables

@[expose] public section

namespace UnconstrainedPACDetection.FormulaAllRailHeads
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open FormulaRailHeadVariables (extend extend_parked lift_hoare)

def raw (i v j r a b f L V g : Nat) : Fin 18 → Tape :=
  extend (FormulaRailHeadPrepare.bank i v j r a b f L V) (regTape g)

theorem parked (i v j r a b f L V g : Nat) : ∀ t, Parked (raw i v j r a b f L V g t) :=
  extend_parked _ _ (FormulaRailHeadPrepare.parked _ _ _ _ _ _ _ _ _) (parked_regTape _)

def prepare : TM 18 := seqTM (clearRegTM 5)
  (seqTM (placeWorkTM 0 1 (FormulaRailHeadPrepare.prepare false))
    (seqTM (copyIntoTM 14 6) (copyIntoTM 16 17)))

/-- Initialize the whole variable loop from bounded stale counters, including
    its independent outer fuel. Dimensions and the caller row/tail survive. -/
theorem prepare_hoare (i v j r a b f L V g M : Nat) (inp : Tape) (ys : List Bool)
    (hi : Parked inp) (hv : v ≤ M) (hj : j ≤ M) (hb : b ≤ M) (hf : f ≤ M)
    (hL : L+1 ≤ M) (hV : V ≤ M) (hg : g ≤ M)
    (hbase : FormulaRailBase.value L V 0 false ≤ M) :
    prepare.HoareTime (EmitPred inp (raw i v j r a b f L V g) ys)
      (EmitPred inp (FormulaRailHeadVariables.bank i 0 r a L V (regTape V)) ys)
      (48*(opBudget M+1)) := by
  have h0 := clearRegTM_hoareTime (5 : Fin 18) v inp (raw i v j r a b f L V g) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ _ t) rfl
  have he0 : Function.update (raw i v j r a b f L V g) 5 (regTape 0) = raw i 0 j r a b f L V g := by
    funext t; fin_cases t <;> simp [raw,extend,FormulaRailHeadPrepare.bank]
  rw [he0] at h0
  have h0' := h0.mono_bound (clearRegTM_le_opBudget hv)
  have h1 := FormulaRailHeadPrepare.prepare_hoare i 0 j r a b f L V M false inp ys hi
    hj hb hf (by omega) hV (Nat.zero_le M) hbase
  have h1' := lift_hoare _ _ _ _ (regTape g) _ _ _
    (FormulaRailHeadPrepare.parked _ _ _ _ _ _ _ _ _) (parked_regTape _) h1
  let base := FormulaRailBase.value L V 0 false
  have h2 := copyIntoTM_hoareTime (14 : Fin 18) 6 (by decide) (L+1) 0 inp
    (raw i 0 0 r a base (L+1) L V g) ys hi (fun t _ => parked _ _ _ _ _ _ _ _ _ _ t) rfl rfl
  have he2 : Function.update (raw i 0 0 r a base (L+1) L V g) 6 (regTape (L+1)) =
      raw i 0 (L+1) r a base (L+1) L V g := by
    funext t; fin_cases t <;> simp [raw,extend,FormulaRailHeadPrepare.bank]
  rw [he2] at h2
  have h2' := h2.mono_bound (copyIntoTM_le_opBudget hL (Nat.zero_le M))
  have h3 := copyIntoTM_hoareTime (16 : Fin 18) 17 (by decide) V g inp
    (raw i 0 (L+1) r a base (L+1) L V g) ys hi (fun t _ => parked _ _ _ _ _ _ _ _ _ _ t) rfl rfl
  have he3 : Function.update (raw i 0 (L+1) r a base (L+1) L V g) 17 (regTape V) =
      FormulaRailHeadVariables.bank i 0 r a L V (regTape V) := by
    funext t; fin_cases t <;> simp [raw,extend,FormulaRailHeadPrepare.bank,
      FormulaRailHeadVariables.bank,base]
  rw [he3] at h3
  have h3' := h3.mono_bound (copyIntoTM_le_opBudget hV hg)
  have h23 := seqTM_hoareTime _ _ h2' (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _ _) _) h3'
  have h123 := seqTM_hoareTime _ _ h1' (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _ _) _) h23
  exact (seqTM_hoareTime _ _ h0' (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _ _) _) h123).mono_bound (by omega)

def budget (n : Nat) : Nat := 48*(opBudget (100*(n+2)^2)+1)+1+
  (n+1)*(2*FormulaRailHeadSigns.budget n+2*(n+1)+8)+(n+3)

def machine (p : ControlSwitch.V) (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 18 :=
  seqTM prepare (FormulaRailHeadVariables.machine p right plan)

/-- A single fixed machine stages and executes every rail head for a switch tail.
    None of its initial query, variable or fuel counters need their correct values. -/
theorem canonical_hoare (φ : SAT.CNF) (i : Fin (levels φ))
    (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (v j b f g : Nat) (ys : List Bool)
    (hv : v ≤ 100*(φ.encode.length+2)^2) (hj : j ≤ 100*(φ.encode.length+2)^2)
    (hb : b ≤ 100*(φ.encode.length+2)^2) (hf : f ≤ 100*(φ.encode.length+2)^2)
    (hg : g ≤ 100*(φ.encode.length+2)^2) :
    (machine p right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (raw i.val v j (index r) (index a) b f (levels φ) (varCount φ) g) ys)
      (EmitPred (word φ.encode)
        (FormulaRailHeadVariables.bank i.val (varCount φ) (index r) (index a) (levels φ) (varCount φ)
          (regTape (varCount φ))) (ys ++ FormulaRailHeadVariables.bits φ right r a (varCount φ)))
      (budget φ.encode.length) := by
  have hpv : 0 < varCount φ := by unfold varCount; omega
  obtain ⟨hL,hV,_⟩ := FormulaEnumeration.parameter_bounds φ
  have hbase := FormulaRailHeadSigns.end_bound φ ⟨0,hpv⟩ false
  change FormulaRailBase.value (levels φ) (varCount φ) 0 false+(levels φ+1) ≤
    100*(φ.encode.length+2)^2 at hbase
  have hprep := prepare_hoare i.val v j (index r) (index a) b f (levels φ) (varCount φ) g
    (100*(φ.encode.length+2)^2) (word φ.encode) ys (word_parked _) hv hj hb hf
    (by nlinarith) (by nlinarith) hg (by omega)
  have hs := FormulaRailHeadVariables.canonical_hoare φ i p right r a ha ys
  have h := seqTM_hoareTime _ _ hprep (emitPred_transition (word_parked _)
    (FormulaRailHeadVariables.parked _ _ _ _ _ _ _ (parked_regTape _)) _) hs
  apply h.mono_bound
  have hmul := Nat.mul_le_mul hV
    (show 2*FormulaRailHeadSigns.budget φ.encode.length+2*varCount φ+8 ≤
      2*FormulaRailHeadSigns.budget φ.encode.length+2*(φ.encode.length+1)+8 by omega)
  unfold budget
  omega

end UnconstrainedPACDetection.FormulaAllRailHeads
