module

public import proofs.IrrRAFEnumeration.CompletionBasePhases
public import proofs.Complexitylib.Models.TuringMachine.OutputBounds

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def baseRunCap (d r : Nat) := d*d+5*d+r+3+3*d*r

theorem baseRunCap_le (d r N : Nat) (hd : d ≤ N) (hr : r ≤ N) :
    baseRunCap d r ≤ 10*(N+1)^2 := by
  have hdd := Nat.mul_le_mul hd hd
  have hdr := Nat.mul_le_mul hd hr
  unfold baseRunCap
  nlinarith

set_option maxHeartbeats 800000 in
theorem basePhasePost_bound (d r : Nat) (p : Fin 6) (q : Fin 23) :
    basePhasePost d r p q ≤ baseRunCap d r := by
  fin_cases p <;> fin_cases q <;>
    norm_num [basePhasePost,basePhaseScratch,baseBankValues,firingBase,baseRunCap] <;> nlinarith

theorem basePhaseTime_le (d r N : Nat) (hd : d ≤ N) (hr : r ≤ N) (p : Fin 6) :
    basePhaseTime d r p ≤ 65536*(N+1)^6 := by
  fin_cases p
  · change r*(5*r+16)+r+5 ≤ _
    calc
      _ ≤ N*(5*N+16)+N+5 := by gcongr
      _ ≤ _ := by ring_nf; omega
  · change d*(5*(d+r+3)+5*r+10*d+53)+d+2 ≤ _
    calc
      _ ≤ N*(5*(N+N+3)+5*N+10*N+53)+N+2 := by gcongr
      _ ≤ _ := by ring_nf; omega
  · exact (firingFamilyTime_le d r N hd hr).trans (by omega)
  · exact supportFamilyTime_le d r N hd hr
  · exact (reactantFamilyTime_le d r N hd hr).trans (by ring_nf; omega)
  · exact (catalystFamilyTime_le d r N hd hr).trans (by ring_nf; omega)

def baseRunState (d r : Nat) : Nat → Fin 23 → Nat
  | 0 => baseBankValues d r
  | 1 => basePhasePost d r 0
  | 2 => basePhasePost d r 1
  | 3 => basePhasePost d r 2
  | 4 => basePhasePost d r 3
  | 5 => basePhasePost d r 4
  | _ => basePhasePost d r 5

theorem baseRunState_bound (d r k : Nat) (q : Fin 23) :
    baseRunState d r k q ≤ baseRunCap d r := by
  unfold baseRunState
  split
  · have h := baseBankStage_bound d r 19 (by decide) q
    rw [baseBankStage_final] at h
    exact h.trans (by unfold baseBankCap baseRunCap; omega)
  all_goals exact basePhasePost_bound d r _ q

theorem baseRunState_bank (d r k : Nat) (q : Fin 23) (hq : 12 ≤ q.val) :
    baseRunState d r k q = baseBankValues d r q := by
  unfold baseRunState
  split
  · rfl
  all_goals simp [basePhasePost,Nat.not_lt.mpr hq]

theorem baseRunState_load (d r k : Nat) (p : Fin 6) :
    baseLoadStage (baseRunState d r k) (baseLoadSources p) 12 = basePhasePre d r p := by
  funext q
  by_cases hq : q.val < 12
  · simp only [basePhasePre,baseLoadStage,hq,and_self,dite_eq_left]
    unfold baseLoadValue
    split
    · rfl
    · apply baseRunState_bank
      dsimp [bankSource]
      omega
  · simp [basePhasePre,baseLoadStage,hq,baseRunState_bank d r k q (by omega)]

def baseRunPhaseTM (p : Fin 6) : TM 23 :=
  seqTM (baseLoadTM (baseLoadSources p)) (basePhaseTM p)

def baseRunPhaseTime (N : Nat) := 12*(opBudget (10*(N+1)^2)+1)+2+65536*(N+1)^6

theorem baseRunPhaseTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (p : Fin 6) (ys : List Bool) :
    (baseRunPhaseTM p).HoareTime
      (EmitPred (parkedInput (inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)))
        (baseRegWork (baseRunState d r p.val)) ys)
      (EmitPred (parkedInput (inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)))
        (baseRegWork (baseRunState d r (p.val+1)))
        (ys++SAT.CNF.encode (basePhaseClauses (decC := decC) Q C p)))
      (baseRunPhaseTime (inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)).length) := by
  let z := inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)
  have hd : d ≤ z.length := by
    dsimp [z]
    unfold inputBits
    repeat rw [List.length_append]
    repeat rw [List.length_replicate]
    omega
  have hr : r ≤ z.length := by
    dsimp [z]
    unfold inputBits
    repeat rw [List.length_append]
    repeat rw [List.length_replicate]
    omega
  have hv : ∀ q, baseRunState d r p.val q ≤ 10*(z.length+1)^2 :=
    fun q => (baseRunState_bound d r p.val q).trans (baseRunCap_le d r z.length hd hr)
  have h₁ := baseLoadTM_correct (baseRunState d r p.val) (baseLoadSources p)
    (10*(z.length+1)^2) hv (parkedInput z) ys (parkedInput_parked z)
  rw [baseRunState_load] at h₁
  have h₂ := basePhaseTM_correct (decC := decC) Q C p ys
  have he : basePhasePost d r p = baseRunState d r (p.val+1) := by fin_cases p <;> rfl
  rw [he] at h₂
  have h := seqTM_hoareTime _ _ h₁
    (emitPred_transition (parkedInput_parked z) (fun _ => parked_regTape _) ys) h₂
  apply h.mono_bound
  have hb := basePhaseTime_le d r z.length hd hr p
  change 12*(opBudget (10*(z.length+1)^2)+1)+1+1+basePhaseTime d r p ≤ baseRunPhaseTime z.length
  unfold baseRunPhaseTime
  omega

def baseRunOutput {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (k : Nat) : List Bool :=
  SAT.CNF.encode (((List.finRange 6).take k).flatMap (basePhaseClauses (decC := decC) Q C))

theorem baseRunOutput_succ {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (p : Fin 6) :
    baseRunOutput (decC := decC) Q C p.val ++
        SAT.CNF.encode (basePhaseClauses (decC := decC) Q C p) =
      baseRunOutput (decC := decC) Q C (p.val+1) := by
  let f : Fin 6 → SAT.CNF := @basePhaseClauses d r Q C decC
  change SAT.CNF.encode (((List.finRange 6).take p.val).flatMap f) ++
      SAT.CNF.encode (f p) =
    SAT.CNF.encode (((List.finRange 6).take (p.val+1)).flatMap f)
  rcases p with ⟨p,hp⟩
  rw [List.take_succ_eq_append_getElem (by exact hp),List.flatMap_append,
    SAT.CNF.encode_append]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hfin : (⟨p,hp⟩ : Fin 6) = (List.finRange 6)[p] := by
    apply Fin.ext
    interval_cases p <;> rfl
  rw [hfin]

def baseEmitTM : TM 23 := bigSeqTM ((List.finRange 6).map baseRunPhaseTM)
def baseCompilerTM : TM 23 := seqTM basePreparationTM baseEmitTM

def baseCompilerTime (N : Nat) := basePreparationTime N+1+(6*(baseRunPhaseTime N+1)+1)

/-- Complete original-input to base-CNF run, including initialization and every reload. -/
theorem baseCompilerTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] :
    baseCompilerTM.HoareTime
      (fun inp work out =>
        inp = Tape.init ((inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (parkedInput (inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)))
        (baseRegWork (baseRunState d r 6))
        (SAT.CNF.encode (assembledBase (decC := decC) Q C)))
      (baseCompilerTime (inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)).length) := by
  let z := inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)
  let Y : Nat → List Bool := @baseRunOutput d r Q C decC
  let A : List Bool := SAT.CNF.encode (assembledBase (decC := decC) Q C)
  have h := bigSeqTM_hoareTime ((List.finRange 6).map baseRunPhaseTM)
    (parkedInput z) (fun k => baseRegWork (baseRunState d r k))
    Y
    (baseRunPhaseTime z.length) (parkedInput_parked z) (fun _ _ => parked_regTape _) (by
      intro k hk
      have hk6 : k < 6 := by simpa using hk
      have hh := baseRunPhaseTM_correct (decC := decC) Q C ⟨k,hk6⟩
        (Y k)
      have hy := baseRunOutput_succ (decC := decC) Q C ⟨k,hk6⟩
      change Y k ++ SAT.CNF.encode (basePhaseClauses (decC := decC) Q C ⟨k,hk6⟩) =
        Y (k+1) at hy
      rw [hy] at hh
      have hfin : (List.finRange 6)[k]'(List.length_map baseRunPhaseTM ▸ hk) =
          (⟨k,hk6⟩ : Fin 6) := by
        apply Fin.ext
        interval_cases k <;> rfl
      have hm : ((List.finRange 6).map baseRunPhaseTM)[k]'hk =
          baseRunPhaseTM ⟨k,hk6⟩ := by
        rw [List.getElem_map]
        exact congrArg baseRunPhaseTM hfin
      rw [hm]
      exact hh)
  have hfull : Y 6 = A := by
    let f : Fin 6 → SAT.CNF := @basePhaseClauses d r Q C decC
    change SAT.CNF.encode (((List.finRange 6).take 6).flatMap f) =
      SAT.CNF.encode
        ([PositiveCompletionCNF.positive ((List.finRange r).map PositiveCompletionCNF.selectVar)] ++
          initialFoodClauses Q ++
          (List.finRange d).flatMap (firingLayerClauses Q) ++
          (List.finRange d).flatMap (supportLayerClauses Q) ++
          (List.finRange r).flatMap (reactantClauses Q) ++
          (List.finRange r).map (@catalystClause d r C decC))
    rw [show List.finRange 6 = [0,1,2,3,4,5] by decide]
    rw [show List.take 6 ([0,1,2,3,4,5] : List (Fin 6)) = [0,1,2,3,4,5] by rfl]
    have hflat : List.flatMap f ([0,1,2,3,4,5] : List (Fin 6)) =
        f 0 ++ (f 1 ++ (f 2 ++ (f 3 ++ (f 4 ++ (f 5 ++ []))))) := by
      simp only [List.flatMap_cons,List.flatMap_nil]
    have h0 : f 0 =
        [PositiveCompletionCNF.positive ((List.finRange r).map PositiveCompletionCNF.selectVar)] := rfl
    have h1 : f 1 = initialFoodClauses Q := rfl
    have h2 : f 2 = (List.finRange d).flatMap (firingLayerClauses Q) := rfl
    have h3 : f 3 = (List.finRange d).flatMap (supportLayerClauses Q) := rfl
    have h4 : f 4 = (List.finRange r).flatMap (reactantClauses Q) := rfl
    have h5 : f 5 = (List.finRange r).map (@catalystClause d r C decC) := rfl
    have hassoc (a b c d e g : SAT.CNF) :
        a ++ (b ++ (c ++ (d ++ (e ++ g)))) = ((((a ++ b) ++ c) ++ d) ++ e) ++ g := by
      simp only [List.append_assoc]
    rw [hflat,h0,h1,h2,h3,h4,h5,List.append_nil]
    exact congrArg SAT.CNF.encode (hassoc _ _ _ _ _ _)
  have hz : Y 0 = [] := by
    unfold Y baseRunOutput
    rfl
  simp only [List.length_map,List.length_finRange,hfull,hz] at h
  have hp := basePreparationTM_correct (decC := decC) Q C
  have hall := seqTM_hoareTime _ _ hp
    (emitPred_transition (parkedInput_parked z) (fun _ => parked_regTape _) []) h
  exact hall


theorem baseCompilerTime_le (N : Nat) : baseCompilerTime N ≤ 10000000*(N+1)^6 := by
  unfold baseCompilerTime basePreparationTime baseRunPhaseTime opBudget
  ring_nf
  omega


/-- Pointwise executable interface consumed by the existing composition machinery. -/
theorem baseCompiler_run {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] :
    ∃ (c : Cfg 23 baseCompilerTM.Q) (t : Nat),
      t ≤ 10000000*((inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)).length+1)^6 ∧
      baseCompilerTM.reachesIn t (baseCompilerTM.initCfg
        (inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _))) c ∧
      baseCompilerTM.halted c ∧
      c.output.HasOutput (SAT.CNF.encode (assembledBase (decC := decC) Q C)) := by
  obtain ⟨c,t,ht,hr,hh,_,_,ho⟩ := baseCompilerTM_correct (decC := decC) Q C
    (Tape.init ((inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)).map Γ.ofBool))
    (fun _ => Tape.init []) (Tape.init []) ⟨rfl,fun _ => rfl,rfl⟩
  exact ⟨c,t,ht.trans (baseCompilerTime_le _),hr,hh,ho.hasOutput⟩

/-- Output-size control follows from the costed run; no separate clause counting is assumed. -/
theorem assembledBase_encode_length_le {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] :
    (SAT.CNF.encode (assembledBase (decC := decC) Q C)).length ≤
      10000000*((inputBits (decC := decC) Q C (Equiv.refl _) (Equiv.refl _)).length+1)^6 := by
  obtain ⟨c,t,ht,hr,_,ho⟩ := baseCompiler_run (decC := decC) Q C
  exact (output_length_le_of_reachesIn hr ho).trans ht

end IrrRAFEnumeration.CompletionQuery
