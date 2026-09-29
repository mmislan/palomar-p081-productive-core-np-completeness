module

public import proofs.UnconstrainedPACDetection.FormulaLookupBoundary
public import proofs.UnconstrainedPACDetection.VerifierPairRestore

@[expose] public section

namespace UnconstrainedPACDetection.FormulaLookupFrame
open Complexity Complexity.TM
open FormulaLookupScan
open VerifierPairRestore (word)

theorem start_frame {n : Nat} (M : TM n) {c d : Cfg n M.Q} {t : Nat}
    (hr : M.reachesIn t c d) (hi : c.input.StartInvariant)
    (hw : ∀ j, (c.work j).StartInvariant) (ho : c.output.StartInvariant) :
    d.input.StartInvariant ∧ (∀ j, (d.work j).StartInvariant) ∧ d.output.StartInvariant := by
  induction hr with
  | zero => exact ⟨hi,hw,ho⟩
  | step hs _ ih =>
    obtain ⟨hi',hw',ho'⟩ := Tape.StartInvariant.step M hs hi hw ho
    exact ih hi' hw' ho'

theorem prefix_acc (bits : List Bool) (t : Tape)
    (h : t.HasBinaryPrefix bits) (h0 : t.cells 0 = Γ.start) : OutAcc bits t := by
  refine ⟨h.1,h0,h.2.1,?_⟩
  intro j hj
  obtain ⟨i,rfl⟩ : ∃ i, j = i+1 := ⟨j-1,by omega⟩
  exact h.2.2 i (by omega)

theorem query_step {c d : Cfg 2 machine.Q} (hs : machine.step c = some d)
    (hw : (c.work 0).StartInvariant) : (d.work 0).cells = (c.work 0).cells := by
  have hp : (c.work 0).head = 0 ∨ (c.work 0).read ≠ Γ.start := by
    by_cases hz : (c.work 0).head = 0
    · exact Or.inl hz
    · exact Or.inr (hw.read_ne_start (by omega))
  cases hq : c.state with
  | none => simp [TM.step,machine,hq] at hs
  | some q =>
    have hwrites : (machine.δ c.state c.input.read (fun j => (c.work j).read)
        c.output.read).2.1 0 = readBackWrite (c.work 0).read := by
      simp only [machine,hq]
      split
      · rfl
      · split
        · rfl
        · simp
    unfold TM.step at hs
    split at hs
    · simp at hs
    · cases hs
      change ((c.work 0).writeAndMove
        ((machine.δ c.state c.input.read (fun j => (c.work j).read)
          c.output.read).2.1 0).toΓ _).cells = _
      rw [hwrites]
      exact tape_readBackWrite_preserves _ _ hp

theorem query_frame {c d : Cfg 2 machine.Q} {t : Nat}
    (hr : machine.reachesIn t c d) (hi : c.input.StartInvariant)
    (hw : ∀ j, (c.work j).StartInvariant) (ho : c.output.StartInvariant) :
    (d.work 0).cells = (c.work 0).cells := by
  induction hr with
  | zero => rfl
  | step hs _ ih =>
    obtain ⟨hi',hw',ho'⟩ := Tape.StartInvariant.step machine hs hi hw ho
    exact (ih hi' hw' ho').trans (query_step hs (hw 0))

def initial (src : List Bool) (i : Nat) : Cfg 2 machine.Q :=
  ⟨machine.qstart,word src,fun j => if j = 0 then word (List.replicate i true)
    else word [],word []⟩

/-- Exact accumulator and reusable query contents at the physical lookup exit. -/
theorem prepared_run (src : List Bool) (i : Nat) :
    ∃ d t, t ≤ src.length+1 ∧ machine.reachesIn t (initial src i) d ∧ machine.halted d ∧
      OutAcc (run none i src).raw d.output ∧
      OutAcc (List.replicate (run none i src).clauses true) (d.work 1) ∧
      (d.work 0).HasBinarySuffix (List.replicate (run none i src).remaining true) ∧
      (d.work 0).cells = (word (List.replicate i true)).cells ∧
      d.input.cells = (word src).cells ∧
      d.input.StartInvariant ∧ d.input.head ≤ src.length+2 ∧
      (d.work 0).head ≤ src.length+2 := by
  have hi : (initial src i).input.StartInvariant :=
    (Tape.StartInvariant.init_ofBool src).move .right
  have hw : ∀ j, ((initial src i).work j).StartInvariant := by
    intro j
    dsimp only [initial]
    split <;> exact (Tape.StartInvariant.init_ofBool _).move .right
  have ho : (initial src i).output.StartInvariant :=
    (Tape.StartInvariant.init_ofBool []).move .right
  obtain ⟨d,t,ht,hr,hh,hq,hc,hout⟩ := scan src none i (initial src i) [] [] rfl
    (Tape.init_move_right_hasBinaryString src).hasBinarySuffix
    (by simpa [initial,word] using
      (Tape.init_move_right_hasBinaryString (List.replicate i true)).hasBinarySuffix)
    (by simpa [initial,word] using Tape.init_nil_move_right_hasBinaryPrefix_nil)
    (by simpa [initial,word] using Tape.init_nil_move_right_hasBinaryPrefix_nil)
  obtain ⟨hid,hwd,hod⟩ := start_frame machine hr hi hw ho
  have heads := head_le_start_add_of_reachesIn machine hr
  refine ⟨d,t,ht,hr,hh,?_,?_,hq,?_,input_cells_eq_of_reachesIn hr,hid,?_,?_⟩
  · exact prefix_acc _ _ (by simpa using hout) hod.1
  · exact prefix_acc _ _ (by simpa using hc) (hwd 1).1
  · exact query_frame hr hi hw ho
  · have h := heads.1
    change d.input.head ≤ 1+t at h
    omega
  · have h := heads.2.2 0
    change (d.work 0).head ≤ 1+t at h
    omega

def exit (src : List Bool) (i : Nat) : Complexity.TM.TapePred 2 := fun inp work out =>
  OutAcc (run none i src).raw out ∧
  OutAcc (List.replicate (run none i src).clauses true) (work 1) ∧
  (work 0).HasBinarySuffix (List.replicate (run none i src).remaining true) ∧
  (work 0).cells = (word (List.replicate i true)).cells ∧
  inp.cells = (word src).cells ∧ inp.StartInvariant ∧
  inp.head ≤ src.length+2 ∧ (work 0).head ≤ src.length+2

/-- A composable physical lookup, with the cursor costs exposed for restoration. -/
theorem prepared_hoare (src : List Bool) (i : Nat) : machine.HoareTime
    (EmitPred (word src) (initial src i).work []) (exit src i) (src.length+1) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  have hout : out = word [] := ho.eq outAcc_nil_init
  subst out
  obtain ⟨d,t,ht,hr,hh,hrest⟩ := prepared_run src i
  exact ⟨d,t,ht,hr,hh,hrest⟩

end UnconstrainedPACDetection.FormulaLookupFrame
