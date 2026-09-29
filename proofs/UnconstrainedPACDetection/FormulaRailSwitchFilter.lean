module

public import proofs.UnconstrainedPACDetection.FormulaBlockingRound
public import proofs.UnconstrainedPACDetection.FormulaCoefficientGate

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailSwitchFilter
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def bank (i v j : Nat) : Fin 9 → Tape :=
  ![regTape i,word [],word [],word [],word [],regTape v,regTape j,word [],word [true]]

theorem parked (i v j : Nat) : ∀ t, Parked (bank i v j t) := by
  intro t; fin_cases t
  all_goals first | exact parked_regTape _ | exact word_parked _

def permutation : Equiv.Perm (Fin 9) :=
  ((Equiv.swap 1 6).trans (Equiv.swap 2 7)).trans (Equiv.swap 3 8)

def comparisonBase : TM 9 := placeWorkTM 0 5 FormulaClauseCompare.machine
def comparison : TM 9 := VerifierWorkPermutation.machine comparisonBase permutation

theorem comparison_hoare (i v j : Nat) (ys : List Bool) (inp : Tape) (hi : Parked inp) :
    comparison.HoareTime (EmitPred inp (bank i v j) ys)
      (EmitPred inp (bank i v j) (ys ++ [decide (i = j)])) (3*max i j+20) := by
  rintro inp' w out ⟨hin,hw,ho⟩
  subst inp'; subst w
  let base : Fin 9 → Tape := fun t => bank i v j (permutation t)
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ :=
    FormulaClauseCompare.compare_hoare i j [true] ys inp hi inp
      (FormulaClauseCompare.bank i j [true]) out ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal FormulaClauseCompare.machine
    0 5 base hr (by intro t _; exact (parked i v j (permutation t)).read_ne_start)
  have routed := VerifierWorkPermutation.run_commute comparisonBase permutation hs
  refine ⟨VerifierWorkPermutation.wrap comparisonBase permutation
    (placeWorkCfg _ 0 5 base d),t,ht,?_,hh,hdi,?_,?_⟩
  · unfold comparison
    convert routed using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext t; fin_cases t <;>
        simp [VerifierWorkPermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
          base,permutation,Equiv.trans_apply,Equiv.swap_apply_def,bank,FormulaClauseCompare.bank]
    · rfl
  · funext t; fin_cases t <;>
      simp [VerifierWorkPermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
        base,permutation,Equiv.trans_apply,Equiv.swap_apply_def,bank,FormulaClauseCompare.bank,hdw]
  · change OutAcc (ys ++ [decide (i = j)]) d.output
    simpa using hdo

def blocking (b : Bool) : TM 9 := placeWorkTM 0 3 (FormulaBlockingRound.machine b)

theorem blocking_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (j : Nat) (b : Bool) (ys : List Bool) :
    (blocking b).HoareTime (EmitPred (word φ.encode) (bank i.val v.val j) ys)
      (EmitPred (word φ.encode) (bank i.val v.val j)
        (ys ++ [FormulaWiring.blocked φ i v b])) (24*φ.encode.length+26*v.val+187) := by
  rintro inp w out ⟨hin,hw,ho⟩
  subst inp; subst w
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := FormulaBlockingRound.round_hoare φ i v b ys
    (word φ.encode) (FormulaComparisonPrepare.initialWork i.val v.val) out ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal (FormulaBlockingRound.machine b)
    0 3 (bank i.val v.val j) hr (by intro t _; exact (parked i.val v.val j t).read_ne_start)
  refine ⟨placeWorkCfg _ 0 3 (bank i.val v.val j) d,t,ht,?_,hh,hdi,?_,hdo⟩
  · unfold blocking
    convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext t; fin_cases t <;>
        simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,bank,
          FormulaComparisonPrepare.initialWork,FormulaEndpointRegisters.unary_word]
    · rfl
  · funext t; fin_cases t <;>
      simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,bank,
        FormulaComparisonPrepare.initialWork,FormulaEndpointRegisters.unary_word,hdw]

/-- Short-circuit index equality and blocking; emit a fixed field only on admission. -/
def machine (b : Bool) (bits : List Bool) : TM 9 :=
  seqTM comparison (FormulaCoefficientGate.gate
    (seqTM (blocking b) (FormulaCoefficientGate.gate (emitBitsTM bits))))

theorem filter_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (j : Nat) (b : Bool) (ys bits : List Bool) :
    (machine b bits).HoareTime (EmitPred (word φ.encode) (bank i.val v.val j) ys)
      (EmitPred (word φ.encode) (bank i.val v.val j)
        (ys ++ if i.val = j ∧ FormulaWiring.blocked φ i v b = true then bits else []))
      (24*φ.encode.length+26*v.val+3*max i.val j+bits.length+220) := by
  have hi := word_parked φ.encode
  have hp := parked i.val v.val j
  have he := emitBitsTM_hoareTime bits (word φ.encode) (bank i.val v.val j) ys hi hp
  have hg := FormulaCoefficientGate.gate_hoare (emitBitsTM bits)
    (FormulaWiring.blocked φ i v b) (word φ.encode) (bank i.val v.val j) ys bits
    bits.length hi hp he
  have hb := seqTM_hoareTime _ _ (blocking_hoare φ i v j b ys)
    (emitPred_transition hi hp _) hg
  have ho := FormulaCoefficientGate.gate_hoare _ (decide (i.val = j)) (word φ.encode)
    (bank i.val v.val j) ys (if FormulaWiring.blocked φ i v b then bits else [])
    _ hi hp hb
  have h := seqTM_hoareTime _ _ (comparison_hoare i.val v.val j ys _ hi)
    (emitPred_transition hi hp _) ho
  have hh := h.mono_bound (show (3*max i.val j+20)+1+
      ((24*φ.encode.length+26*v.val+187)+1+(bits.length+2)+2) ≤
      24*φ.encode.length+26*v.val+3*max i.val j+bits.length+220 by omega)
  by_cases hij : i.val = j <;> cases hz : FormulaWiring.blocked φ i v b <;>
    simpa [machine,hij,hz] using hh

/-- The switch port is a finite control case, never an unbounded hard-coded index. -/
def portMachine (a : ControlSwitch.V) (b : Bool) (bits : List Bool) : TM 9 :=
  if a = 3 then machine b bits else emitBitsTM []

/-- The complete rail-to-switch graph test, including every switch port and dummy level. -/
theorem adjacency_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (j : Fin (FormulaWiring.levels φ+1))
    (a : ControlSwitch.V) (b : Bool) (ys bits : List Bool) :
    (portMachine a b bits).HoareTime (EmitPred (word φ.encode) (bank i.val v.val j.val) ys)
      (EmitPred (word φ.encode) (bank i.val v.val j.val)
        (ys ++ if FormulaWiring.adjacency φ (Sum.inr (.rail v b j)) (SwitchStack.sw i a)
          then bits else []))
      (24*φ.encode.length+26*v.val+3*max i.val j.val+bits.length+220) := by
  by_cases ha : a = 3
  · subst a
    have h := filter_hoare φ i v j.val b ys bits
    have he : FormulaWiring.adjacency φ (Sum.inr (.rail v b j)) (SwitchStack.sw i 3) ↔
        i.val = j.val ∧ FormulaWiring.blocked φ i v b = true := by
      change ((3 : ControlSwitch.V) = 2 ∨ 3 = 3) ∧ 3 = 3 ∧
        j.val = i.val ∧ FormulaWiring.blocked φ i v b = true ↔ _
      constructor
      · rintro ⟨_,_,hj,hb⟩; exact ⟨hj.symm,hb⟩
      · rintro ⟨hj,hb⟩; exact ⟨Or.inr rfl,rfl,hj.symm,hb⟩
    simpa only [portMachine,ite_eq_left rfl,he,ite_true] using h
  · have h := emitBitsTM_hoareTime ([] : List Bool) (word φ.encode)
      (bank i.val v.val j.val) ys (word_parked _) (parked _ _ _)
    have h' := h.mono_bound (show ([] : List Bool).length ≤
      24*φ.encode.length+26*v.val+3*max i.val j.val+bits.length+220 by simp)
    have hn : ¬FormulaWiring.adjacency φ (Sum.inr (.rail v b j)) (SwitchStack.sw i a) := by
      intro he
      exact ha he.2.1
    unfold EmitPred
    simpa only [portMachine,ite_eq_right ha,ite_eq_right hn,List.append_nil] using h'

end UnconstrainedPACDetection.FormulaRailSwitchFilter
