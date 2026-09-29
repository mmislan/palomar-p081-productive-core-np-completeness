module

public import proofs.UnconstrainedPACDetection.VerifierIndexAppend

@[expose] public section

/-! A charged unary-index successor with all caller frames preserved. -/
namespace UnconstrainedPACDetection.VerifierIndexAdvance
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierContributionReset (safe frame stable)
open VerifierIndexAppend (atEnd)

def machine (idx : Fin 9) := seqTM (VerifierIndexAppend.machine idx) (rewindWorkTM idx)

theorem append_hoare (idx : Fin 9) (bits : List Bool) (w : Fin 9 → Tape) (inp₀ out₀ : Tape)
    (hx : w idx = wordTape bits) (hw : safe w) (hi : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) :
    (VerifierIndexAppend.machine idx).HoareTime (frame w inp₀ out₀)
      (frame (Function.update w idx (atEnd (bits ++ [true]))) inp₀ out₀) (bits.length+1) := by
  rintro inp work out ⟨hin,hwork,hout⟩
  subst inp
  subst work
  subst out
  let c : Cfg 9 Bool := ⟨false,inp₀,w,out₀⟩
  have hs : (c.work idx).HasBinaryString bits := by
    change (w idx).HasBinaryString bits
    rw [hx]
    exact Tape.init_move_right_hasBinaryString bits
  have hm : (c.work idx).cells 0 = .start := by change (w idx).cells 0 = .start; rw [hx]; rfl
  obtain ⟨d,hd,hh,hdw,hin,hout⟩ := VerifierIndexAppend.append_run idx bits c rfl hs hm
    (fun j _ => (hw j).1) hi ho
  exact ⟨d,_,le_rfl,hd,hh,hin,hdw,hout⟩

theorem advance_hoare (idx : Fin 9) (bits : List Bool) (w : Fin 9 → Tape) (inp₀ out₀ : Tape)
    (hx : w idx = wordTape bits) (hw : safe w) (hi : inp₀.read ≠ .start)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (machine idx).HoareTime (frame w inp₀ out₀)
      (frame (Function.update w idx (wordTape (bits ++ [true]))) inp₀ out₀) (2*bits.length+6) := by
  let w1 := Function.update w idx (atEnd (bits ++ [true]))
  have hp : (atEnd (bits ++ [true])).HasBinaryPrefix (bits ++ [true]) :=
    ⟨rfl,(Tape.init_move_right_hasBinaryString _).2⟩
  have hs : safe w1 := by
    intro j
    by_cases hj : j = idx
    · subst j
      simp only [w1,Function.update_self]
      exact ⟨by rw [hp.read_blank]; decide,by simp [atEnd]⟩
    · simpa [w1,Function.update_of_ne hj] using hw j
  have hm : (w1 idx).cells 0 = .start := by simp [w1,atEnd,wordTape,Tape.move]
  have hn : ∀ q, 1 ≤ q → (w1 idx).cells q ≠ .start := by
    simpa [w1,atEnd,wordTape,Tape.move] using (Tape.StartInvariant.init_ofBool (bits ++ [true])).2
  have hr := VerifierContributionRewind.rewind_hoare idx w1 inp₀ out₀ hm hn hs hi ho hoh
  have h := seqTM_hoareTime _ _ (append_hoare idx bits w inp₀ out₀ hx hw hi ho)
    (stable w1 inp₀ out₀ hs hi ho) hr
  have he : VerifierContributionRewind.restored w1 idx = Function.update w idx (wordTape (bits ++ [true])) := by
    funext j
    by_cases hj : j = idx
    · subst j
      simp only [VerifierContributionRewind.restored,Function.update_self,w1]
      exact Tape.ext (by rfl) rfl
    · simp [VerifierContributionRewind.restored,w1,Function.update_of_ne hj]
  have h' := h.mono_bound (show bits.length+1+1+((w1 idx).head+2) ≤ 2*bits.length+6 by
    simp [w1,atEnd]; omega)
  simpa only [machine,he] using h'

/-- The same fixed machine advances an index from k to k+1, including k=0. -/
theorem successor_hoare (idx : Fin 9) (k : ℕ) (w : Fin 9 → Tape) (inp₀ out₀ : Tape)
    (hx : w idx = VerifierIndexedField.counter k) (hw : safe w) (hi : inp₀.read ≠ .start)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (machine idx).HoareTime (frame w inp₀ out₀)
      (frame (Function.update w idx (VerifierIndexedField.counter (k+1))) inp₀ out₀) (2*k+6) := by
  have h := advance_hoare idx (List.replicate k true) w inp₀ out₀ hx hw hi ho hoh
  simpa [VerifierIndexedField.counter,List.replicate_add] using h

end UnconstrainedPACDetection.VerifierIndexAdvance
