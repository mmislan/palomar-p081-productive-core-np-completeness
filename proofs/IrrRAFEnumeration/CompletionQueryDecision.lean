module

public import proofs.IrrRAFEnumeration.CompletionQueryRouting

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def queryPrefix {r : Nat} (k : Nat) (U : Finset (Fin r)) (pos index : Nat)
    (base blocks : List Bool) : Fin (7+k) → Tape :=
  frameWork (m := k) (dynamicWork U pos index base blocks) (fun _ => regTape 0)

def queryDecisionWork {r : Nat} (k : Nat) (U : Finset (Fin r)) (pos index : Nat)
    (base blocks query : List Bool) : Fin (7+k+1) → Tape :=
  frameWork (m := 1) (queryPrefix k U pos index base blocks) (fun _ => parkedInput query)

def queryWriteTM (k : Nat) : TM (7+k+1) :=
  (dynamicQueryTM.liftTM k).retargetOutput

def queryPrepareTM (k : Nat) : TM (7+k+1) :=
  seqTM (queryWriteTM k) (rewindWorkTM (Fin.last (7+k)))

theorem queryPrepareTM_correct {d r : Nat} (k : Nat) (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)
    (queryPrepareTM k).HoareTime
      (EmitPred inp (queryDecisionWork k U 1 0 base blocks []) [])
      (EmitPred inp (queryDecisionWork k U (1+r) r base blocks query) [])
      (dynamicQueryTime base.length blocks.length r+query.length+4) := by
  dsimp only
  let base := SAT.CNF.encode (assembledBase Q C)
  let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
  let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
    PositiveCompletionCNF.containerExclusions U)
  have h := dynamicQueryTM_correct Q C G U inp hp
  have hl := liftTM_frame_correct dynamicQueryTM k (fun _ => regTape 0)
    (fun _ _ => parked_regTape _) inp inp _ _ _ _ _ h
  have hd := redirectEmitter_correct (dynamicQueryTM.liftTM k) inp inp _ _ _ _ _ hl
  have hw : ∀ i, Parked (queryPrefix k U (1+r) r base blocks i) := by
    intro i
    unfold queryPrefix frameWork
    split
    · exact dynamicWork_parked _ _ _ _ _ _
    · exact parked_regTape _
  have hr := rewindQuery_correct (queryPrefix k U (1+r) r base blocks) inp query hp hw
  have hm : ∀ i, Parked (frameWork (m := 1) (queryPrefix k U (1+r) r base blocks)
      (fun _ => accumulatorTape query) i) := by
    intro i
    unfold frameWork
    split
    · exact hw _
    · exact (accumulatorTape_outAcc query).parked
  have hall := seqTM_hoareTime _ _ hd (emitPred_transition hp hm []) hr
  exact hall.mono_bound (by dsimp [query]; omega)

def queryDecisionTM {k : Nat} (M : TM k) : TM (7+k+1) :=
  seqTM (queryPrepareTM k) (placeWorkTM 7 0 (retargetInputStarted M))

theorem placedSAT_preserves_real {k : Nat} (M : TM k)
    {c c' : Cfg (7+k+1) (placeWorkTM 7 0 (retargetInputStarted M)).Q} {t : Nat}
    (hr : (placeWorkTM 7 0 (retargetInputStarted M)).reachesIn t c c')
    (hp : Parked c.input) : c'.input = c.input := by
  induction hr with
  | zero => rfl
  | @step a b c t hs _ ih =>
    have he : b.input = a.input := by
      simp only [TM.step] at hs
      split at hs
      · contradiction
      · cases hs
        exact hp.move_idle
    exact (ih (he.symm ▸ hp)).trans he

/-- Query construction, direct virtual-input routing, and actual SAT execution.
Solver scratch cleanup for another call is not part of this theorem. -/
theorem queryDecisionTM_correct {d r k : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r))
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)
    (queryDecisionTM M).HoareTime
      (EmitPred inp (queryDecisionWork k U 1 0 base blocks []) [])
      (fun a w out => a = inp ∧
        (∀ i : Fin 7, w (Fin.castAdd (k+1) i) = dynamicWork U (1+r) r base blocks i) ∧
        (out.cells 1 = Γ.one ↔ PositiveCompletion.Available (IsRAF Q C) G.toFinset U))
      (dynamicQueryTime base.length blocks.length r+query.length+5+T query.length) := by
  dsimp only
  let base := SAT.CNF.encode (assembledBase Q C)
  let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
  let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
    PositiveCompletionCNF.containerExclusions U)
  let W := queryDecisionWork k U (1+r) r base blocks query
  have hw : ∀ i, Parked (W i) := by
    intro i
    unfold W queryDecisionWork queryPrefix frameWork
    split
    · split
      · exact dynamicWork_parked _ _ _ _ _ _
      · exact parked_regTape _
    · exact parkedInput_parked _
  have hs : (placeWorkTM 7 0 (retargetInputStarted M)).HoareTime
      (EmitPred inp W [])
      (fun a w out => a = inp ∧
        (∀ i : Fin 7, w (Fin.castAdd (k+1) i) = dynamicWork U (1+r) r base blocks i) ∧
        (out.cells 1 = Γ.one ↔ PositiveCompletion.Available (IsRAF Q C) G.toFinset U))
      (T query.length) := by
    rintro a w out ⟨ha,hww,ho⟩
    subst a
    subst w
    have hout : out = (Tape.init []).move Dir3.right := ho.eq outAcc_nil_init
    subst out
    have hinv : ∀ i : Fin (7+k+1), ¬placeWorkInMiddle (post := 0) 7 (k+1) i → (W i).StartInvariant := by
      intro i hi
      have hi7 : i.val < 7 := by unfold placeWorkInMiddle at hi; omega
      have hzall : ∀ j : Fin 7, (dynamicWork U (1+r) r base blocks j).cells 0 = Γ.start := by
        intro j
        fin_cases j <;> rfl
      have hik : i.val < 7+k := by omega
      have hz : (W i).cells 0 = Γ.start := by
        simpa [W,queryDecisionWork,queryPrefix,frameWork,hik,hi7] using hzall ⟨i.val,hi7⟩
      exact ⟨hz,(hw i).2⟩
    obtain ⟨c,t,ht,hr,hh,hframe,hverdict⟩ := completionSAT_run Q C G U M T hM 7 0 W
      hinv (fun i _ => (hw i).1) inp
    have hentry : placeWorkCfg (retargetInputStarted M) 7 0 W
        (retargetInputStartedCfg M query inp) =
        (⟨(placeWorkTM 7 0 (retargetInputStarted M)).qstart,inp,W,
          (Tape.init []).move Dir3.right⟩ : Cfg (7+k+1) M.Q) := by
      refine Cfg.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · funext i
        by_cases hi : placeWorkInMiddle (post := 0) 7 (k+1) i
        · have hlo : ¬i.val < 7 := by unfold placeWorkInMiddle at hi; omega
          by_cases hik : i.val < 7+k
          · have hsub : i.val-7 < k := by unfold placeWorkInMiddle at hi; omega
            simp [placeWorkCfg,hi,retargetInputStartedCfg,placeWorkCoord,
              W,queryDecisionWork,queryPrefix,frameWork,hik,hlo,hsub,regTape,
              Tape.init,Tape.move]
            funext j
            by_cases hj : j = 0 <;> simp [regCells,hj]
          · have hsub : ¬i.val-7 < k := by omega
            simp [placeWorkCfg,hi,retargetInputStartedCfg,placeWorkCoord,
              W,queryDecisionWork,frameWork,hik,hsub,parkedInput]
            rfl
        · exact placeWorkCfg_work_extra _ _ _ _ _ i hi
      · rfl
    rw [hentry] at hr
    refine ⟨c,t,ht,hr,hh,placedSAT_preserves_real M hr hp,?_,hverdict⟩
    intro i
    have hnot : ¬placeWorkInMiddle (post := 0) 7 (k+1) (Fin.castAdd (k+1) i) := by
      simp [placeWorkInMiddle]
    rw [hframe _ hnot]
    have hik : i.val < 7+k := by have := i.isLt; omega
    simp [W,queryDecisionWork,queryPrefix,frameWork,i.isLt,hik]
  have h := queryPrepareTM_correct k Q C G U inp hp
  exact (seqTM_hoareTime _ _ h (emitPred_transition hp hw []) hs).mono_bound (by dsimp [query]; omega)

end IrrRAFEnumeration.CompletionQuery
