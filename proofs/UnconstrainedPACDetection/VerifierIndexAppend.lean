module

public import proofs.UnconstrainedPACDetection.VerifierContributionIteration

@[expose] public section

/-! Actual scan-and-append of one unary index mark on a selected work tape. -/
namespace UnconstrainedPACDetection.VerifierIndexAppend
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)

def machine (idx : Fin 9) : TM 9 where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun _ i w o =>
    (decide (w idx = .blank),
      fun j => if j = idx ∧ w idx = .blank then .one else readBackWrite (w j),
      readBackWrite o,idleDir i,fun j => if j = idx then .right else idleDir (w j),idleDir o)
  δ_right_of_start := by
    intro q i w o
    refine ⟨idleDir_right_of_start,?_,idleDir_right_of_start⟩
    intro j hj
    by_cases he : j = idx
    · simp [he]
    · simp [he,idleDir_right_of_start hj]

def moved (idx : Fin 9) (c : Cfg 9 Bool) : Cfg 9 Bool :=
  ⟨false,c.input,Function.update c.work idx ((c.work idx).move .right),c.output⟩
def appended (idx : Fin 9) (c : Cfg 9 Bool) : Cfg 9 Bool :=
  ⟨true,c.input,Function.update c.work idx ((c.work idx).writeAndMove .one .right),c.output⟩

theorem scan_step (idx : Fin 9) (c : Cfg 9 Bool) (hq : c.state = false)
    (hb : (c.work idx).read ≠ .blank) (hf : ∀ j, (c.work j).read ≠ .start)
    (hi : c.input.read ≠ .start) (ho : c.output.read ≠ .start) :
    (machine idx).step c = some (moved idx c) := by
  obtain ⟨hin,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start hi hf ho
  simp only [TM.step,machine,hq,Bool.false_eq_true,↓reduceIte,decide_eq_false hb]
  congr 1
  apply Cfg.ext
  · rfl
  · exact hin
  · funext j
    by_cases hj : j = idx
    · subst j
      simpa [moved,hb] using writeAndMove_readBack (c.work idx) (hf idx) .right
    · have ht := congrFun hw j
      unfold transitionTape at ht
      simpa [moved,hj] using ht
  · exact hout

theorem append_step (idx : Fin 9) (c : Cfg 9 Bool) (hq : c.state = false)
    (hb : (c.work idx).read = .blank) (hf : ∀ j, (c.work j).read ≠ .start)
    (hi : c.input.read ≠ .start) (ho : c.output.read ≠ .start) :
    (machine idx).step c = some (appended idx c) := by
  obtain ⟨hin,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start hi hf ho
  simp only [TM.step,machine,hq,Bool.false_eq_true,↓reduceIte,hb,decide_true]
  congr 1
  apply Cfg.ext
  · rfl
  · exact hin
  · funext j
    by_cases hj : j = idx
    · subst j
      simp [appended]
    · have ht := congrFun hw j
      unfold transitionTape at ht
      simpa [appended,hj] using ht
  · exact hout

theorem scan_run (idx : Fin 9) (bits : List Bool) (c : Cfg 9 Bool)
    (hq : c.state = false) (hs : (c.work idx).HasBinarySuffix bits)
    (hf : ∀ j, j ≠ idx → (c.work j).read ≠ .start)
    (hi : c.input.read ≠ .start) (ho : c.output.read ≠ .start) :
    ∃ d, (machine idx).reachesIn bits.length c d ∧ d.state = false ∧
      (d.work idx).HasBinarySuffix [] ∧ (d.work idx).head = (c.work idx).head+bits.length ∧
      (d.work idx).cells = (c.work idx).cells ∧
      (∀ j, j ≠ idx → d.work j = c.work j) ∧ d.input = c.input ∧ d.output = c.output := by
  induction bits generalizing c with
  | nil => exact ⟨c,.zero,hq,hs,by simp,rfl,fun _ _ => rfl,rfl,rfl⟩
  | cons b bits ih =>
    have hall : ∀ j, (c.work j).read ≠ .start := by
      intro j
      by_cases hj : j = idx
      · subst j; exact hs.read_ne_start
      · exact hf j hj
    have hb : (c.work idx).read ≠ .blank := by
      cases b <;> simp [hs.read_cons,Γ.ofBool]
    have hstep := scan_step idx c hq hb hall hi ho
    have hs' : ((moved idx c).work idx).HasBinarySuffix bits := by
      simpa [moved] using hs.move_right_cons
    have hf' : ∀ j, j ≠ idx → ((moved idx c).work j).read ≠ .start := by
      intro j hj; simpa [moved,Function.update_of_ne hj] using hf j hj
    obtain ⟨d,hd,hh,hds,hdh,hdc,hdf,hin,hout⟩ := ih (moved idx c) rfl hs' hf' hi ho
    refine ⟨d,.step hstep hd,hh,hds,?_,?_,?_,hin,hout⟩
    · simpa [moved,Tape.move,Nat.add_assoc,Nat.add_comm] using hdh
    · simpa [moved,Tape.move] using hdc
    · intro j hj; simpa [moved,Function.update_of_ne hj] using hdf j hj

def atEnd (bits : List Bool) : Tape := ⟨bits.length+1,(wordTape bits).cells⟩

theorem append_run (idx : Fin 9) (bits : List Bool) (c : Cfg 9 Bool)
    (hq : c.state = false) (hs : (c.work idx).HasBinaryString bits)
    (hm : (c.work idx).cells 0 = .start)
    (hf : ∀ j, j ≠ idx → (c.work j).read ≠ .start)
    (hi : c.input.read ≠ .start) (ho : c.output.read ≠ .start) :
    ∃ d, (machine idx).reachesIn (bits.length+1) c d ∧ (machine idx).halted d ∧
      d.work = Function.update c.work idx (atEnd (bits ++ [true])) ∧
      d.input = c.input ∧ d.output = c.output := by
  obtain ⟨d,hd,hh,hds,hdh,hdc,hdf,hin,hout⟩ := scan_run idx bits c hq hs.hasBinarySuffix hf hi ho
  have hp : (d.work idx).HasBinaryPrefix bits := by
    refine ⟨by rw [hdh,hs.1]; omega,?_⟩
    rw [hdc]
    exact hs.2
  have hd0 : (d.work idx).cells 0 = .start := by rw [hdc]; exact hm
  have hall : ∀ j, (d.work j).read ≠ .start := by
    intro j
    by_cases hj : j = idx
    · subst j; exact hds.read_ne_start
    · rw [hdf j hj]; exact hf j hj
  have hstep := append_step idx d hh hds.read_nil hall (hin ▸ hi) (hout ▸ ho)
  have hpre := Tape.hasBinaryPrefix_write_bit true hp
  have hzero := Tape.hasBinaryPrefix_write_bit_cell0 true hp hd0
  have he : (d.work idx).writeAndMove .one .right = atEnd (bits ++ [true]) := by
    apply Tape.ext
    · exact hpre.1
    · exact hpre.cells_eq_init hzero
  refine ⟨appended idx d,?_,rfl,?_,hin,hout⟩
  · exact (machine idx).reachesIn_trans hd (.step hstep .zero)
  · funext j
    by_cases hj : j = idx
    · subst j; simpa [appended] using he
    · simpa [appended,Function.update_of_ne hj] using hdf j hj

end UnconstrainedPACDetection.VerifierIndexAppend
