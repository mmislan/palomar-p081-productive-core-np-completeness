module

public import proofs.UnconstrainedPACDetection.FormulaRailHeadPrepare

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailHeadSigns
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open FormulaRailHeadPrepare (bank parked)

def budget (n : Nat) : Nat := 44*(opBudget (100*(n+2)^2)+1)+1+500*(n+2)^3

private theorem cap (n : Nat) : 30*(n+1)^2 ≤ 100*(n+2)^2 := by
  gcongr <;> omega

theorem end_bound (φ : SAT.CNF) (v : Fin (varCount φ)) (s : Bool) :
    FormulaRailBase.value (levels φ) (varCount φ) v.val s+(levels φ+1) ≤
      100*(φ.encode.length+2)^2 := by
  obtain ⟨pre,post,hblock,hbase⟩ := FormulaRailBase.factor φ v s
  have hl := congrArg List.length hblock
  simp only [List.length_append,FormulaRailCursor.block,List.length_map,List.length_finRange] at hl
  rw [hbase] at hl
  have hn := FormulaIndexedGraph.labels_bound φ
  exact (show FormulaRailBase.value (levels φ) (varCount φ) v.val s+(levels φ+1) ≤
    (FormulaIndexedGraph.labels φ).length by omega).trans (hn.trans (cap φ.encode.length))

theorem true_end (L V v : Nat) :
    FormulaRailBase.value L V v true+(L+1) = FormulaRailBase.value L V (v+1) false := by
  simp [FormulaRailBase.value]; ring

def bits (φ : SAT.CNF) (v : Fin (varCount φ)) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) : List Bool :=
  FormulaRailHeadLoop.bits φ v false right r a (levels φ+1) ++
    FormulaRailHeadLoop.bits φ v true right r a (levels φ+1)

def machine (p : ControlSwitch.V) (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 17 :=
  seqTM (FormulaRailHeadPrepare.machine p false right plan)
    (FormulaRailHeadPrepare.machine p true right plan)

/-- Both signs are executed consecutively, in canonical order, using the actual
    returned frame. No second caller initialization is assumed. -/
theorem canonical_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (v : Fin (varCount φ))
    (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (j b f : Nat) (ys : List Bool)
    (hj : j ≤ 100*(φ.encode.length+2)^2) (hb : b ≤ 100*(φ.encode.length+2)^2)
    (hf : f ≤ 100*(φ.encode.length+2)^2) :
    (machine p right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank i.val v.val j (index r) (index a) b f (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode)
        (bank i.val v.val (levels φ+1) (index r) (index a)
          (FormulaRailBase.value (levels φ) (varCount φ) (v.val+1) false)
          (levels φ+1) (levels φ) (varCount φ)) (ys ++ bits φ v right r a))
      (2*budget φ.encode.length+1) := by
  have h1 := FormulaRailHeadPrepare.staged_scan_hoare φ i v p false right r a ha j b f ys hj hb hf
  have hL : levels φ+1 ≤ 100*(φ.encode.length+2)^2 := by
    have h := (FormulaEnumeration.parameter_bounds φ).1
    nlinarith
  have h2 := FormulaRailHeadPrepare.staged_scan_hoare φ i v p true right r a ha
    (levels φ+1) (FormulaRailBase.value (levels φ) (varCount φ) v.val false+(levels φ+1))
    (levels φ+1) (ys ++ FormulaRailHeadLoop.bits φ v false right r a (levels φ+1))
    hL (end_bound φ v false) hL
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _) _) h2
  rw [true_end] at h
  have h' := h.mono_bound (show budget φ.encode.length+1+budget φ.encode.length ≤
      2*budget φ.encode.length+1 by omega)
  simpa only [machine,bits,List.append_assoc] using h'

end UnconstrainedPACDetection.FormulaRailHeadSigns
