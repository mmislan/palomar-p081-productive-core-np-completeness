module

public import proofs.UnconstrainedPACDetection.VerifierFieldMachine
public import proofs.UnconstrainedPACDetection.VerifierPairRestore
public import proofs.Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget

@[expose] public section

namespace UnconstrainedPACDetection.FormulaFieldEmission
open Complexity Complexity.TM
open VerifierFieldMachine (Phase)
open VerifierPairRestore (word word_parked)

/-- The existing encoder preserves source cells and appends to a real accumulator. -/
theorem scan_exact (xs : List Bool) : ∀ (c : Cfg 0 VerifierFieldMachine.machine.Q)
    (ys : List Bool), c.state = Phase.scan → c.input.HasBinarySuffix xs →
    OutAcc ys c.output →
    ∃ d, VerifierFieldMachine.machine.reachesIn (2*xs.length+1) c d ∧
      VerifierFieldMachine.machine.halted d ∧ d.input.cells = c.input.cells ∧
      d.input.head = c.input.head+xs.length ∧
      OutAcc (ys ++ BinaryFields.encodeField xs) d.output := by
  induction xs with
  | nil =>
    intro c ys hs hi ho
    let d : Cfg 0 VerifierFieldMachine.machine.Q :=
      ⟨.done,c.input,(fun j => nomatch j),c.output.writeAndMove Γ.zero .right⟩
    have step : VerifierFieldMachine.machine.step c = some d := by
      simp [TM.step,VerifierFieldMachine.machine,hs,hi.read_nil,d,idleDir,Tape.move]
      funext j; exact Fin.elim0 j
    refine ⟨d,.step step .zero,rfl,rfl,by simp [d],?_⟩
    exact outAcc_append_bit ho false
  | cons b xs ih =>
    intro c ys hs hi ho
    let c₁ : Cfg 0 VerifierFieldMachine.machine.Q :=
      ⟨.payload,c.input,(fun j => nomatch j),c.output.writeAndMove Γ.one .right⟩
    let c₂ : Cfg 0 VerifierFieldMachine.machine.Q :=
      ⟨.scan,c.input.move .right,(fun j => nomatch j),
        c₁.output.writeAndMove (Γ.ofBool b) .right⟩
    have step₁ : VerifierFieldMachine.machine.step c = some c₁ := by
      have hr := hi.read_cons
      cases b <;> simp [TM.step,VerifierFieldMachine.machine,hs,hr,Γ.ofBool,c₁,idleDir,Tape.move]
      all_goals funext j; exact Fin.elim0 j
    have step₂ : VerifierFieldMachine.machine.step c₁ = some c₂ := by
      have hr := hi.read_cons
      cases b <;> simp [TM.step,VerifierFieldMachine.machine,c₁,c₂,hr,Γ.ofBool,readBackWrite]
      all_goals funext j; exact Fin.elim0 j
    have ho₁ : OutAcc (ys ++ [true]) c₁.output := outAcc_append_bit ho true
    have ho₂ : OutAcc ((ys ++ [true]) ++ [b]) c₂.output := outAcc_append_bit ho₁ b
    obtain ⟨d,hd,hh,hc,hhead,hout⟩ := ih c₂ _ rfl hi.move_right_cons ho₂
    refine ⟨d,?_,hh,?_,?_,?_⟩
    · convert TM.reachesIn.step step₁ (TM.reachesIn.step step₂ hd) using 1
    · exact hc
    · simpa [c₂,Tape.move,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hhead
    · simpa [BinaryFields.encodeField,List.append_assoc] using hout

private theorem route_run (M : TM 0) (inp : Tape) (hi : Parked inp)
    {c d : Cfg 0 M.Q} {t : Nat} (h : M.reachesIn t c d)
    (hc : Tape.StartInvariant c.input) (ho : Tape.StartInvariant c.output) :
    (retargetInput M).reachesIn t (retargetWrap M inp c) (retargetWrap M inp d) := by
  induction h with
  | zero => exact .zero
  | @step c₀ c₁ _ _ hs _ ih =>
    obtain ⟨hc',_,ho'⟩ := Tape.StartInvariant.step M hs hc (fun j => Fin.elim0 j) ho
    have hstep := retargetInput_step_commute M hs inp hc
    have he : inp.move (idleDir inp.read) = inp := by
      simp [idleDir,hi.read_ne_start,Tape.move]
    rw [he] at hstep
    exact .step hstep (ih hc' ho')

def scan : TM 1 := retargetInput VerifierFieldMachine.machine

theorem scan_hoare (xs ys : List Bool) (inp : Tape) (hi : Parked inp) :
    scan.HoareTime (EmitPred inp (fun _ => word xs) ys)
      (fun i w o => i = inp ∧ OutAcc xs (w 0) ∧
        OutAcc (ys ++ BinaryFields.encodeField xs) o) (2*xs.length+1) := by
  rintro i w o ⟨hin,hw,ho⟩
  subst i; subst w
  let c : Cfg 0 VerifierFieldMachine.machine.Q := ⟨.scan,word xs,(fun j => nomatch j),o⟩
  obtain ⟨d,hr,hh,hcells,hhead,hout⟩ := scan_exact xs c ys rfl
    (Tape.init_move_right_hasBinarySuffix xs) ho
  have hs := route_run VerifierFieldMachine.machine inp hi hr
    ((Tape.StartInvariant.init_ofBool xs).move .right) ⟨ho.2.1,ho.parked.2⟩
  refine ⟨retargetWrap _ inp d,2*xs.length+1,le_rfl,?_,hh,rfl,?_,hout⟩
  · unfold scan
    convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j
      simp [retargetWrap,c]
    · rfl
  · change OutAcc xs d.input
    have hx := (Tape.init_move_right_hasBinaryString xs)
    refine ⟨?_,?_,?_,?_⟩
    · simpa [c,word,Tape.move,Tape.init,Nat.add_comm] using hhead
    · rw [hcells]; rfl
    · intro j hj; rw [hcells]; exact hx.2.1 j hj
    · intro j hj
      rw [hcells]
      obtain ⟨k,rfl⟩ : ∃ k, j = k+1 := ⟨j-1,by omega⟩
      exact hx.2.2 k (by omega)

def machine : TM 1 := seqTM scan (rewindWorkTM 0)

/-- One complete reusable field append; the word and the actual input are restored. -/
theorem field_hoare (xs ys : List Bool) (inp : Tape) (hi : Parked inp) :
    machine.HoareTime (EmitPred inp (fun _ => word xs) ys)
      (EmitPred inp (fun _ => word xs) (ys ++ BinaryFields.encodeField xs))
      (3*xs.length+5) := by
  let post : Complexity.TM.TapePred 1 := fun i w o =>
    i = inp ∧ OutAcc xs (w 0) ∧ OutAcc (ys ++ BinaryFields.encodeField xs) o
  have stable : ∀ i w o, post i w o → post (transitionInput i)
      (fun j => transitionTape (w j)) (transitionTape o) := by
    rintro i w o ⟨hin,hw,ho⟩
    subst i
    obtain ⟨he,hws,heo⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start
      (by intro j; have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
          rw [hj]; exact hw.parked.read_ne_start) ho.parked.read_ne_start
    simpa only [he,hws,heo] using (show post inp w o from ⟨rfl,hw,ho⟩)
  have restore : (rewindWorkTM (0 : Fin 1)).HoareTime post
      (EmitPred inp (fun _ => word xs) (ys ++ BinaryFields.encodeField xs)) (xs.length+3) := by
    rintro i w o ⟨hin,hw,ho⟩
    subst i
    have hp : ∀ j, Parked (w j) := by intro j; fin_cases j; exact hw.parked
    obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := VerifierPairRestore.restore_word
      (0 : Fin 1) xs _ inp w hi hp hw inp w o ⟨rfl,rfl,ho⟩
    refine ⟨d,t,ht,hr,hh,hdi,?_,hdo⟩
    rw [hdw]
    funext j; fin_cases j; simp
  have h := seqTM_hoareTime _ _ (scan_hoare xs ys inp hi) stable restore
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.FormulaFieldEmission
