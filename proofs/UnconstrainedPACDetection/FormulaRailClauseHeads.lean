module

public import proofs.UnconstrainedPACDetection.FormulaClauseHeadLoop

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailClauseHeads
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)

def extend (w : Fin 18 → Tape) (C : Nat) (t : Fin 19) : Tape :=
  if h : t.val < 18 then w ⟨t.val,h⟩ else regTape C

theorem extend_parked (w : Fin 18 → Tape) (C : Nat) (hp : ∀ t, Parked (w t)) :
    ∀ t, Parked (extend w C t) := by
  intro t; unfold extend; split
  · exact hp _
  · exact parked_regTape _

theorem lift_hoare (m : TM 18) (inp : Tape) (w z : Fin 18 → Tape)
    (C : Nat) (ys zs : List Bool) (B : Nat) (hp : ∀ t, Parked (w t))
    (h : m.HoareTime (EmitPred inp w ys) (EmitPred inp z zs) B) :
    (placeWorkTM 0 1 m).HoareTime
      (EmitPred inp (extend w C) ys) (EmitPred inp (extend z C) zs) B := by
  rintro i work out ⟨rfl,rfl,ho⟩
  obtain ⟨d,t,ht,hr,hh,hi,hw,hout⟩ := h _ _ out ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal m 0 1 (extend w C) hr
    (by intro q _; exact (extend_parked w C hp q).read_ne_start)
  refine ⟨placeWorkCfg m 0 1 (extend w C) d,t,ht,?_,hh,hi,?_,hout⟩
  · convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext q; fin_cases q <;> simp [placeWorkCfg,placeWorkInMiddle,extend] <;> rfl
    · rfl
  · funext q; fin_cases q <;> simp [placeWorkCfg,placeWorkInMiddle,extend,hw] <;> rfl

theorem seam (i r a L V C : Nat) :
    extend (FormulaRailHeadVariables.bank i V r a L V (regTape V)) C =
      FormulaClauseHeadLoop.bank i 0 r a (FormulaRailBase.value L V V false) L V C (regTape V) := by
  funext t; fin_cases t <;>
    simp [extend,FormulaRailHeadVariables.bank,FormulaRailHeadVariables.extend,
      FormulaRailHeadPrepare.bank,FormulaClauseHeadLoop.bank]
  exact FormulaEndpointRegisters.unary_word 0

def machine (p : ControlSwitch.V) (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 19 :=
  seqTM (placeWorkTM 0 1 (FormulaAllRailHeads.machine p right plan))
    (seqTM (copyIntoTM 18 17) (FormulaClauseHeadLoop.machine p right plan))

def budget (φ : SAT.CNF) : Nat := FormulaAllRailHeads.budget φ.encode.length+
  (2*φ.length^2+7*φ.length+2*varCount φ+7)+
  (φ.length*(20*φ.encode.length+8*φ.length+5*(FormulaIndexedGraph.labels φ).length+142)+(φ.length+2))+2

/-- The whole rail phase hands its actual returned frame to the clause phase.
    Clause fuel is copied from the preserved live dimension, never supplied by an oracle. -/
theorem canonical_hoare (φ : SAT.CNF) (i : Fin (levels φ))
    (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (v j b f g : Nat) (ys : List Bool)
    (hv : v ≤ 100*(φ.encode.length+2)^2) (hj : j ≤ 100*(φ.encode.length+2)^2)
    (hb : b ≤ 100*(φ.encode.length+2)^2) (hf : f ≤ 100*(φ.encode.length+2)^2)
    (hg : g ≤ 100*(φ.encode.length+2)^2) :
    (machine p right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode)
        (extend (FormulaAllRailHeads.raw i.val v j (index r) (index a) b f (levels φ) (varCount φ) g) φ.length) ys)
      (EmitPred (word φ.encode)
        (FormulaClauseHeadLoop.bank i.val φ.length (index r) (index a)
          (FormulaClauseCursor.base φ+φ.length) (levels φ) (varCount φ) φ.length (regTape φ.length))
        (ys ++ FormulaRailHeadVariables.bits φ right r a (varCount φ) ++
          FormulaClauseHeadLoop.bits φ right r a φ.length))
      (budget φ) := by
  have hr := FormulaAllRailHeads.canonical_hoare φ i p right r a ha v j b f g ys hv hj hb hf hg
  have hl := lift_hoare _ _ _ _ φ.length _ _ _ (FormulaAllRailHeads.parked _ _ _ _ _ _ _ _ _ _) hr
  rw [seam] at hl
  let w := FormulaClauseHeadLoop.bank i.val 0 (index r) (index a)
    (FormulaClauseCursor.base φ) (levels φ) (varCount φ) φ.length (regTape (varCount φ))
  let zs := ys ++ FormulaRailHeadVariables.bits φ right r a (varCount φ)
  have hc := copyIntoTM_hoareTime (18 : Fin 19) 17 (by decide) φ.length (varCount φ)
    (word φ.encode) w zs (word_parked _) (fun t _ => FormulaClauseHeadLoop.parked _ _ _ _ _ _ _ _ _ (parked_regTape _) t) rfl rfl
  have he : Function.update w 17 (regTape φ.length) =
      FormulaClauseHeadLoop.bank i.val 0 (index r) (index a) (FormulaClauseCursor.base φ)
        (levels φ) (varCount φ) φ.length (regTape φ.length) := by
    funext t; fin_cases t <;> simp [w,FormulaClauseHeadLoop.bank]
  rw [he] at hc
  have hs := FormulaClauseHeadLoop.canonical_hoare φ i p right r a ha zs
  have hcs := seqTM_hoareTime _ _ hc (emitPred_transition (word_parked _)
    (FormulaClauseHeadLoop.parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) _) hs
  have h := seqTM_hoareTime _ _ hl (emitPred_transition (word_parked _)
    (FormulaClauseHeadLoop.parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) _) hcs
  exact h.mono_bound (by unfold budget; nlinarith)

end UnconstrainedPACDetection.FormulaRailClauseHeads
