module

public import proofs.UnconstrainedPACDetection.FormulaLookupRouting
public import proofs.UnconstrainedPACDetection.FormulaBlockingCleanup
public import proofs.UnconstrainedPACDetection.FormulaEndpointRegisters

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseLookup
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def result (src : List Bool) (i : Nat) := FormulaLookupScan.run none i src
def bank (i c : Nat) (raw : List Bool) : Fin 3 → Tape :=
  ![regTape i,regTape c,word raw]

theorem bank_parked (i c : Nat) (raw : List Bool) : ∀ j, Parked (bank i c raw j) := by
  intro j; fin_cases j
  · exact parked_regTape _
  · exact parked_regTape _
  · exact word_parked _

def restore : TM 3 := seqTM (rewindWorkTM 1) (rewindWorkTM 2)

theorem restore_hoare (src : List Bool) (i : Nat) (raw ys : List Bool) :
    restore.HoareTime (FormulaLookupRouting.result src i raw ys)
      (EmitPred (word src) (bank i (result src i).clauses raw) ys)
      ((result src i).clauses+raw.length+7) := by
  rintro inp w out ⟨rfl,hq,hc,hl,ho⟩
  have hp : ∀ j, Parked (w j) := by
    intro j; fin_cases j
    · change Parked (w 0); rw [hq]; exact word_parked _
    · exact hc.parked
    · exact hl.parked
  obtain ⟨d,t,ht,hd,hh,hi,hw,hout⟩ := VerifierPairRestore.restore_pair (1 : Fin 3) 2
    (by decide) (List.replicate (result src i).clauses true) raw ys (word src) w
    (word_parked src) hp hc hl _ _ _ ⟨rfl,rfl,ho⟩
  refine ⟨d,t,?_,hd,hh,hi,?_,hout⟩
  · simpa only [List.length_replicate] using ht
  · rw [hw]
    funext j; fin_cases j
    · simpa [bank,FormulaEndpointRegisters.unary_word] using hq
    · simp [bank,FormulaEndpointRegisters.unary_word]
    · simp [bank]

def machine : TM 3 := seqTM FormulaLookupRouting.routed restore

/-- One scan returns both original occurrence data and its restored clause register. -/
theorem lookup_hoare (src : List Bool) (i : Nat) (ys : List Bool) :
    machine.HoareTime (EmitPred (word src) (bank i 0 []) ys)
      (EmitPred (word src) (bank i (result src i).clauses (result src i).raw) ys)
      (5*src.length+21) := by
  have he : bank i 0 [] = FormulaLookupRouting.initialWork i := by
    funext j; fin_cases j <;>
      simp [bank,FormulaLookupRouting.initialWork,FormulaEndpointRegisters.unary_word]
    all_goals exact (FormulaEndpointRegisters.unary_word 0).symm
  have h := seqTM_hoareTime _ _ (FormulaLookupRouting.routed_hoare src i ys)
    (FormulaLookupRouting.result_stable src i _ ys)
    (restore_hoare src i (result src i).raw ys)
  rw [← he] at h
  have hc := FormulaBlockingCleanup.count_bound src i
  have hl := FormulaLookupRouting.raw_length_bound src i
  exact h.mono_bound (by dsimp [result]; omega)

def clauseMatch (r : FormulaLookupScan.Result) (target : Nat) (exit : Bool) : Bool :=
  match FormulaLookupScan.decode r with
  | none => false
  | some (c,_) => target == c + if exit then 1 else 0

theorem matches_lookup (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (c : Nat) (exit : Bool) :
    clauseMatch (result φ.encode i.val) c exit =
      match FormulaWiring.lookup φ i with
      | none => false
      | some (j,_) => c == j + if exit then 1 else 0 := by
  have h := FormulaLookupScan.decoded_lookup φ.encode φ (SAT.CNF.decode?_encode φ) i.val
  simp only [clauseMatch,result,h,FormulaWiring.lookup]

theorem clause_index_of_lookup (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (c : Nat) (l : SAT.Lit) (h : FormulaWiring.lookup φ i = some (c,l)) :
    (result φ.encode i.val).clauses = c := by
  have hd := FormulaLookupScan.decoded_lookup φ.encode φ (SAT.CNF.decode?_encode φ) i.val
  change FormulaLookupScan.decode (result φ.encode i.val) = FormulaWiring.lookup φ i at hd
  rw [h] at hd
  unfold FormulaLookupScan.decode at hd
  cases he : SAT.Lit.decodeRaw? (result φ.encode i.val).raw with
  | none => simp [he] at hd
  | some k =>
    simp only [he,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hd
    exact hd.1

theorem raw_lookup (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ)) :
    (result φ.encode i.val).raw =
      ((FormulaWiring.lookup φ i).map (fun z => z.2.encodeRaw)).getD [] := by
  simpa only [result,FormulaOccurrenceLookup.occurrences_eq,FormulaWiring.lookup]
    using FormulaLookupMatching.raw_lookup φ i.val 0

/-- Literal presence is necessary even when the restored clause count matches. -/
theorem guarded_match (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (c : Nat) (exit : Bool) :
    clauseMatch (result φ.encode i.val) c exit =
      (!(result φ.encode i.val).raw.isEmpty &&
        (c == (result φ.encode i.val).clauses + if exit then 1 else 0)) := by
  rw [matches_lookup,raw_lookup]
  cases h : FormulaWiring.lookup φ i with
  | none => simp
  | some z =>
    obtain ⟨j,l⟩ := z
    rw [clause_index_of_lookup φ i j l h]
    simp [SAT.Lit.encodeRaw]

/-- Actual metadata consumer for both clause-to-switch and switch-to-clause tests.
The Boolean test is semantic here; its physical comparison remains separate. -/
theorem decoded_lookup (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (ys : List Bool) :
    machine.HoareTime (EmitPred (word φ.encode) (bank i.val 0 []) ys)
      (fun inp work out => ∃ r : FormulaLookupScan.Result,
        EmitPred (word φ.encode) (bank i.val r.clauses r.raw) ys inp work out ∧
        FormulaLookupScan.decode r = FormulaWiring.lookup φ i)
      (5*φ.encode.length+21) := by
  apply (lookup_hoare φ.encode i.val ys).consequence
  · intro inp work out h; exact h
  · intro inp work out h
    exact ⟨result φ.encode i.val,h,
      FormulaLookupScan.decoded_lookup φ.encode φ (SAT.CNF.decode?_encode φ) i.val⟩
  · omega

end UnconstrainedPACDetection.FormulaClauseLookup
