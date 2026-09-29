module

public import proofs.UnconstrainedPACDetection.VerifierEntityReuse

@[expose] public section

namespace UnconstrainedPACDetection.VerifierCursorReset
open Complexity Complexity.TM
open VerifierReactionLoop (frame sourcePred)
open VerifierBufferedProduct (wordTape)

theorem clear_frame (k stride fuel : ℕ) (wit : Tape) (pos neg : List Bool) :
    Function.update (frame k stride fuel wit pos neg) 1 (wordTape []) =
      frame 0 stride fuel wit pos neg := by
  funext j
  fin_cases j <;> simp [frame,VerifierTraversalContribution.extend,
    VerifierCoefficientIteration.layout,VerifierSignedContribution.extend,
    VerifierWitnessProduct.initial,VerifierIndexedField.counter]

def pred (emitted : List Bool) (k stride fuel : ℕ) (wit : Tape) (pos neg suffix : List Bool) :
    Tape → (Fin 11 → Tape) → Tape → Prop :=
  fun inp work out => sourcePred suffix inp ∧ work = frame k stride fuel wit pos neg ∧ out.HasBinaryPrefix emitted

theorem stable (emitted : List Bool) (k stride fuel : ℕ) (wit : Tape) (pos neg suffix : List Bool) (hw : Parked wit) :
    ∀ inp work out, pred emitted k stride fuel wit pos neg suffix inp work out →
      pred emitted k stride fuel wit pos neg suffix (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have hf : ∀ j, (work j).read ≠ .start := by
    intro j
    rw [h.2.1]
    exact (VerifierReactionLoop.frame_parked _ _ _ _ _ _ hw j).read_ne_start
  obtain ⟨hi,hw',ho⟩ := phaseTransition_eq_self_of_reads_ne_start h.1.read_ne_start hf (by rw [h.2.2.read_blank]; decide)
  simpa only [hi,hw',ho] using h

theorem clear_hoare (emitted : List Bool) (k stride fuel : ℕ) (wit : Tape) (pos neg suffix : List Bool) (hw : Parked wit) :
    (clearWorkTM (1 : Fin 11)).HoareTime (pred emitted k stride fuel wit pos neg suffix)
      (pred emitted 0 stride fuel wit pos neg suffix) (2*k+5) := by
  intro inp work out h
  let P : Tape → (Fin 11 → Tape) → Tape → Prop := fun inp' work' out' =>
    inp' = inp ∧ (∀ j, j ≠ 1 → work' j = work j) ∧ out' = out
  have hc := clearWorkTM_hoareTime_frame_of_binaryString (1 : Fin 11) (List.replicate k true)
    (P := P) (by
      rintro inp₁ work₁ out₁ inp₂ work₂ out₂ ⟨hi,hf,ho⟩ _ hi' ho' hf'
      exact ⟨hi'.trans hi,fun j hj => (hf' j hj).trans (hf j hj),ho'.trans ho⟩)
  obtain ⟨c,t,ht,hr,hh,hc₁,hin,hwork,hout⟩ := hc inp work out
    ⟨by rw [h.2.1]; rfl,h.1.read_ne_start,(by rw [h.2.2.read_blank]; decide),(by rw [h.2.2.1]; omega),
      fun j _ => by
        rw [h.2.1]
        exact ⟨(VerifierReactionLoop.frame_parked _ _ _ _ _ _ hw j).read_ne_start,
          (VerifierReactionLoop.frame_parked _ _ _ _ _ _ hw j).1⟩,
      rfl,fun _ _ => rfl,rfl⟩
  refine ⟨c,t,by simp only [List.length_replicate] at ht; omega,hr,hh,?_,?_,?_⟩
  · rw [hin]; exact h.1
  · rw [← clear_frame k stride fuel wit pos neg]
    funext j
    by_cases hj : j = 1
    · subst j
      simpa only [Function.update_self,wordTape,List.map_nil] using hc₁
    · rw [Function.update_of_ne hj,hwork j hj,h.2.1]
  · rw [hout]; exact h.2.2

theorem one_hoare (emitted : List Bool) (stride fuel : ℕ) (wit : Tape) (pos neg suffix : List Bool)
    (hw : Parked wit) (hh : wit.head = 1) :
    VerifierTraversalAdvance.machine.HoareTime (pred emitted 0 stride fuel wit pos neg suffix)
      (pred emitted 1 stride fuel wit pos neg suffix) 6 := by
  intro inp work out h
  have ha := VerifierTraversalAdvance.advance_hoare 0 wit pos neg suffix
    (VerifierIndexedField.counter stride) (regTape fuel) out hw.read_ne_start hh
    (VerifierReactionLoop.word_parked _).read_ne_start (parked_regTape _).read_ne_start
    (by rw [h.2.2.read_blank]; decide) (by rw [h.2.2.1]; omega)
  obtain ⟨c,t,ht,hr,hh',hi,hwork,hout⟩ := ha inp work out ⟨h.1,h.2.1,rfl⟩
  exact ⟨c,t,by simpa using ht,hr,hh',hi,hwork,by rw [hout]; exact h.2.2⟩

def machine : TM 11 := seqTM (clearWorkTM 1) VerifierTraversalAdvance.machine

theorem reset_hoare (emitted : List Bool) (k stride fuel : ℕ) (wit : Tape) (pos neg suffix : List Bool)
    (hw : Parked wit) (hh : wit.head = 1) :
    machine.HoareTime (pred emitted k stride fuel wit pos neg suffix)
      (pred emitted 1 stride fuel wit pos neg suffix) (2*k+12) := by
  have h := seqTM_hoareTime _ _ (clear_hoare emitted k stride fuel wit pos neg suffix hw)
    (stable emitted 0 stride fuel wit pos neg suffix hw) (one_hoare emitted stride fuel wit pos neg suffix hw hh)
  exact h.mono_bound (by omega)


theorem rewind_source (src : List Bool) (inp₀ out₀ : Tape) (w : Fin 11 → Tape)
    (hc : inp₀.cells = (wordTape src).cells) (hw : VerifierTapeCleanup.safe w)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (rewindInputTM (n := 11)).HoareTime
      (VerifierTapeCleanup.frame w inp₀ out₀)
      (VerifierTapeCleanup.frame w (wordTape src) out₀) (inp₀.head+2) := by
  let P : Tape → (Fin 11 → Tape) → Tape → Prop := fun inp work out =>
    inp.cells = inp₀.cells ∧ work = w ∧ out = out₀
  have hm := (Tape.StartInvariant.init_ofBool src).move .right
  change (wordTape src).StartInvariant at hm
  have hr := rewindInputTM_hoareTime_frame (n := 11) inp₀.head (P := P) (by
    rintro inp work out inp' work' out' ⟨hi,hwork,hout⟩ hi' _ hw' ho'
    exact ⟨hi'.trans hi,hw'.trans hwork,ho'.trans hout⟩)
  rintro inp work out ⟨hin,hwork,hout⟩
  subst inp; subst work; subst out
  obtain ⟨d,t,ht,hd,hh,hh1,hcells,hw',ho'⟩ := hr inp₀ w out₀
    ⟨by rw [hc]; exact hm.1,by intro j hj; rw [hc]; exact hm.2 j hj,
      le_rfl,ho,hoh,hw,rfl,rfl,rfl⟩
  refine ⟨d,t,ht,hd,hh,?_,hw',ho'⟩
  exact Tape.ext hh1 (hcells.trans hc)

def restart : TM 11 := seqTM rewindInputTM machine

theorem restart_hoare (emitted src : List Bool) (k stride fuel : ℕ)
    (wit inp₀ out₀ : Tape) (pos neg : List Bool)
    (hc : inp₀.cells = (wordTape src).cells) (hw : Parked wit) (hh : wit.head = 1)
    (ho : out₀.HasBinaryPrefix emitted) :
    restart.HoareTime
      (VerifierTapeCleanup.frame (frame k stride fuel wit pos neg) inp₀ out₀)
      (pred emitted 1 stride fuel wit pos neg src) (inp₀.head+2*k+15) := by
  have hsafe : VerifierTapeCleanup.safe (frame k stride fuel wit pos neg) := by
    intro j
    have h := VerifierReactionLoop.frame_parked k stride fuel wit pos neg hw j
    exact ⟨h.read_ne_start,h.1⟩
  have hr := rewind_source src inp₀ out₀ (frame k stride fuel wit pos neg) hc hsafe
    (by rw [ho.read_blank]; decide) (by rw [ho.1]; omega)
  have ht : ∀ inp work out,
      VerifierTapeCleanup.frame (frame k stride fuel wit pos neg) (wordTape src) out₀ inp work out →
      pred emitted k stride fuel wit pos neg src (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
    intro inp work out h
    apply stable emitted k stride fuel wit pos neg src hw
    refine ⟨?_,h.2.1,?_⟩
    · rw [h.1]; exact (Tape.init_move_right_hasBinaryString src).hasBinarySuffix
    · rw [h.2.2]; exact ho
  have h := seqTM_hoareTime _ _ hr ht (reset_hoare emitted k stride fuel wit pos neg src hw hh)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierCursorReset
