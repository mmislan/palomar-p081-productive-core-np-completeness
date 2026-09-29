module

public import proofs.UnconstrainedPACDetection.VerifierTotalBranch

@[expose] public section

/-! Finite sign/side selection followed by an actual accumulation branch. -/
namespace UnconstrainedPACDetection.VerifierSignedAccumulate
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)

abbrev BQ := Fin 4 × Bool
abbrev Q := Option (Option (Bool × BQ))
def choose (isRight : Bool) (g : Γ) : Bool := xor isRight (decide (g = .one))
def running (b : Bool) (q : BQ) : Q := some (some (b,q))
def preserve (q : Q) (i : Γ) (w : Fin 9 → Γ) (o : Γ) :=
  (q, (fun j => readBackWrite (w j)), readBackWrite o, idleDir i,
    (fun j => idleDir (w j)), idleDir o)
def machine (isRight : Bool) : TM 9 where
  Q := Q
  qstart := some none
  qhalt := none
  δ := fun state i w o =>
    match state with
    | none => preserve none i w o
    | some none => preserve (running (choose isRight (w 3)) (0,false)) i w o
    | some (some (b,q)) =>
      if q = (3,false) then preserve none i w o
      else
        let r := (VerifierTotalBranch.machine b).δ q i w o
        (running b r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2)
  δ_right_of_start := by
    intro state i w o
    cases state with
    | none => exact rightOfStart_allIdle i w o
    | some state =>
      cases state with
      | none => exact rightOfStart_allIdle i w o
      | some state =>
        rcases state with ⟨b,q⟩
        dsimp only
        split
        · exact rightOfStart_allIdle i w o
        · exact (VerifierTotalBranch.machine b).δ_right_of_start q i w o

def liftCfg (isRight b : Bool) (c : Cfg 9 BQ) : Cfg 9 (machine isRight).Q :=
  ⟨running b c.state,c.input,c.work,c.output⟩
def idleCfg (isRight : Bool) (q : Q) (c : Cfg 9 Q) : Cfg 9 (machine isRight).Q :=
  ⟨q,c.input,c.work,c.output⟩

theorem lift_step (isRight b : Bool) {c d : Cfg 9 (VerifierTotalBranch.machine b).Q}
    (hs : (VerifierTotalBranch.machine b).step c = some d) :
    (machine isRight).step (liftCfg isRight b c) = some (liftCfg isRight b d) := by
  have hn := state_ne_qhalt_of_step hs
  have hn' : c.state ≠ (3,false) := hn
  let r := (VerifierTotalBranch.machine b).δ c.state c.input.read (fun j => (c.work j).read) c.output.read
  have hδ : (machine isRight).δ (running b c.state) c.input.read
      (fun j => (c.work j).read) c.output.read =
      (running b r.1,r.2) := by
    change (if c.state = (show (VerifierTotalBranch.machine b).Q from (3,false)) then
      preserve none c.input.read (fun j => (c.work j).read) c.output.read else _) = _
    exact ite_eq_right hn'
  have hnh : (liftCfg isRight b c).state ≠ (machine isRight).qhalt := by
    intro h
    cases h
  let nextSource : Cfg 9 BQ :=
    ⟨r.1, c.input.move r.2.2.2.1,
      fun j => (c.work j).writeAndMove (r.2.1 j) (r.2.2.2.2.1 j),
      c.output.writeAndMove r.2.2.1 r.2.2.2.2.2⟩
  let make : (Q × (Fin 9 → Γw) × Γw × Dir3 × (Fin 9 → Dir3) × Dir3) → Cfg 9 Q :=
    fun a => ⟨a.1, c.input.move a.2.2.2.1,
      fun j => (c.work j).writeAndMove (a.2.1 j) (a.2.2.2.2.1 j),
      c.output.writeAndMove a.2.2.1 a.2.2.2.2.2⟩
  have hsource : (VerifierTotalBranch.machine b).step c = some nextSource := ite_eq_right hn
  have hd : nextSource = d := Option.some.inj (hsource.symm.trans hs)
  have htarget : (machine isRight).step (liftCfg isRight b c) =
      some (make ((machine isRight).δ (running b c.state) c.input.read
        (fun j => (c.work j).read) c.output.read)) := ite_eq_right hnh
  calc
    (machine isRight).step (liftCfg isRight b c) = some (liftCfg isRight b nextSource) :=
      htarget.trans (congrArg (fun a => some (make a)) hδ)
    _ = some (liftCfg isRight b d) := by rw [hd]

theorem lift_run (isRight b : Bool) {t : ℕ} {c d : Cfg 9 (VerifierTotalBranch.machine b).Q}
    (h : (VerifierTotalBranch.machine b).reachesIn t c d) :
    (machine isRight).reachesIn t (liftCfg isRight b c) (liftCfg isRight b d) := by
  induction h with
  | zero => exact .zero
  | step hs _ ih => exact .step (lift_step isRight b hs) ih

theorem idle_step (isRight : Bool) (c : Cfg 9 Q) (q : Q)
    (hn : c.state ≠ none) (hi : c.input.read ≠ .start)
    (hw : ∀ j, (c.work j).read ≠ .start) (ho : c.output.read ≠ .start)
    (ha : (machine isRight).δ c.state c.input.read (fun j => (c.work j).read) c.output.read =
      preserve q c.input.read (fun j => (c.work j).read) c.output.read) :
    (machine isRight).step c = some (idleCfg isRight q c) := by
  obtain ⟨hin,hwork,hout⟩ := phaseTransition_eq_self_of_reads_ne_start hi hw ho
  unfold TM.step
  change (if c.state = none then none else _) = _
  rw [ite_eq_right hn, ha]
  dsimp only [preserve]
  congr 1
  apply Cfg.ext
  · rfl
  · exact hin
  · exact hwork
  · exact hout

/-- The selected total is positive iff right-side XOR negative-sign is true.
Both the initial choice and the final transition to halt are charged. -/
theorem accumulation_run (isRight sign : Bool) (term total : List Bool) (c : Cfg 9 Q)
    (hq : c.state = some none) (hsg : (c.work 3).HasBinaryString [sign])
    (hp : (c.work 5).HasBinaryString term) (hpm : (c.work 5).StartInvariant)
    (ht : (c.work (VerifierTotalBranch.target (xor isRight sign))).HasBinaryString total)
    (htm : (c.work (VerifierTotalBranch.target (xor isRight sign))).cells 0 = .start)
    (hf : ∀ j, (c.work j).read ≠ .start)
    (hi : c.input.read ≠ .start) (ho : c.output.read ≠ .start) :
    ∃ d, (machine isRight).reachesIn
        (max term.length total.length+term.length+(VerifierBinaryAdd.add false term total).length+7) c d ∧
      (machine isRight).halted d ∧
      d.work = Function.update c.work (VerifierTotalBranch.target (xor isRight sign))
        (wordTape (VerifierBinaryAdd.add false term total)) ∧
      d.input = c.input ∧ d.output = c.output := by
  let b := xor isRight sign
  let s : Cfg 9 BQ := ⟨(0,false),c.input,c.work,c.output⟩
  have hchoose : choose isRight (c.work 3).read = b := by
    have hr := hsg.hasBinarySuffix.read_cons
    cases sign <;> simp [choose, hr, Γ.ofBool, b]
  have hfirst : (machine isRight).step c = some (liftCfg isRight b s) := by
    apply idle_step isRight c (running b (0,false)) (by rw [hq]; decide) hi hf ho
    simp [machine, hq, hchoose]
  obtain ⟨d,hd,hh,hw,hin,hout⟩ := VerifierTotalBranch.accumulation_run b term total s rfl
    hp hpm ht htm (fun j _ _ => hf j) hi ho
  have hrun := lift_run isRight b hd
  have hdOff : ∀ j, (d.work j).read ≠ .start := by
    intro j
    rw [hw]
    by_cases hj : j = VerifierTotalBranch.target b
    · subst j
      rw [Function.update_self]
      exact (Tape.init_move_right_hasBinaryString _).hasBinarySuffix.read_ne_start
    · rw [Function.update_of_ne hj]
      exact hf j
  have hlast : (machine isRight).step (liftCfg isRight b d) =
      some (idleCfg isRight none (liftCfg isRight b d)) := by
    apply idle_step isRight _ none (by simp [liftCfg, running])
      (by simpa only [liftCfg, hin] using hi) hdOff (by simpa only [liftCfg, hout] using ho)
    have hstate : d.state = (3,false) := hh
    simp [machine, liftCfg, running, hstate]
  refine ⟨idleCfg isRight none (liftCfg isRight b d), ?_, rfl, hw, hin, hout⟩
  have h := (machine isRight).reachesIn_trans (.step hfirst hrun) (.step hlast .zero)
  convert h using 1

end UnconstrainedPACDetection.VerifierSignedAccumulate
