module

public import proofs.IrrRAFEnumeration.CompletionDynamicQuery
public import proofs.Complexitylib.Models.TuringMachine.Combinators.RetargetCompute
public import proofs.Complexitylib.SAT.CookLevin

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

/-- Actual SAT execution on a prepared query, with a preserved enumeration frame.
The query-to-entry copy and scratch reset are separate explicit obligations. -/
theorem completionSAT_run {d r k : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r))
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (pre post : Nat) (extras : Fin (pre+(k+1)+post) → Tape)
    (hinv : ∀ i, ¬placeWorkInMiddle pre (k+1) i → (extras i).StartInvariant)
    (hhead : ∀ i, ¬placeWorkInMiddle pre (k+1) i → 1 ≤ (extras i).head)
    (real : Tape) :
    let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)
    ∃ (c : Cfg (pre+(k+1)+post) M.Q) (t : Nat),
      t ≤ T query.length ∧
      (placeWorkTM pre post (retargetInputStarted M)).reachesIn t
        (placeWorkCfg (retargetInputStarted M) pre post extras
          (retargetInputStartedCfg M query real)) c ∧
      (placeWorkTM pre post (retargetInputStarted M)).halted c ∧
      (∀ i, ¬placeWorkInMiddle pre (k+1) i → c.work i = extras i) ∧
      (c.output.cells 1 = Γ.one ↔ PositiveCompletion.Available (IsRAF Q C) G.toFinset U) := by
  dsimp only
  let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
    PositiveCompletionCNF.containerExclusions U)
  obtain ⟨inner,c,t,ht,hr,he,hh,hy,hn⟩ :=
    placeWorkTM_retargetInputStarted_decidesVirtual M pre post extras hM query real hinv hhead
  have hq : query ∈ SAT.language ↔ PositiveCompletion.Available (IsRAF Q C) G.toFinset U := by
    rw [SAT.encode_mem_LSAT_iff,assembledQuery_satisfiable_iff]
  refine ⟨c,t,ht,hr,hh,?_,?_⟩
  · intro i hi
    rw [he]
    simp [placeWorkCfg,hi]
  · constructor
    · intro hout
      by_contra hfalse
      have hzero := hn (fun hm => hfalse (hq.mp hm))
      rw [hzero] at hout
      contradiction
    · intro hav
      exact hy (hq.mpr hav)

end IrrRAFEnumeration.CompletionQuery
