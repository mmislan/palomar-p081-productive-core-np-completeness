module

public import proofs.UnconstrainedPACDetection.VerifierSizedPhase

@[expose] public section

namespace UnconstrainedPACDetection.VerifierFlowReset
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

def pred (k stride fuel : ℕ) (wit : Tape) (pos neg suffix : List Bool) :
    Tape → (Fin 11 → Tape) → Tape → Prop :=
  fun inp work out => sourcePred suffix inp ∧ work = frame k stride fuel wit pos neg ∧ OutAcc [] out

theorem stable (k stride fuel : ℕ) (wit : Tape) (pos neg suffix : List Bool) (hw : Parked wit) :
    ∀ inp work out, pred k stride fuel wit pos neg suffix inp work out →
      pred k stride fuel wit pos neg suffix (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have hf : ∀ j, (work j).read ≠ .start := by
    intro j
    rw [h.2.1]
    exact (VerifierReactionLoop.frame_parked _ _ _ _ _ _ hw j).read_ne_start
  obtain ⟨hi,hw',ho⟩ := phaseTransition_eq_self_of_reads_ne_start h.1.read_ne_start hf h.2.2.parked.read_ne_start
  simpa only [hi,hw',ho] using h

theorem clear_hoare (k stride fuel : ℕ) (wit : Tape) (pos neg suffix : List Bool) (hw : Parked wit) :
    (clearWorkTM (1 : Fin 11)).HoareTime (pred k stride fuel wit pos neg suffix)
      (pred 0 stride fuel wit pos neg suffix) (2*k+5) := by
  intro inp work out h
  let P : Tape → (Fin 11 → Tape) → Tape → Prop := fun inp' work' out' =>
    inp' = inp ∧ (∀ j, j ≠ 1 → work' j = work j) ∧ out' = out
  have hc := clearWorkTM_hoareTime_frame_of_binaryString (1 : Fin 11) (List.replicate k true)
    (P := P) (by
      rintro inp₁ work₁ out₁ inp₂ work₂ out₂ ⟨hi,hf,ho⟩ _ hi' ho' hf'
      exact ⟨hi'.trans hi,fun j hj => (hf' j hj).trans (hf j hj),ho'.trans ho⟩)
  obtain ⟨c,t,ht,hr,hh,hc₁,hin,hwork,hout⟩ := hc inp work out
    ⟨by rw [h.2.1]; rfl,h.1.read_ne_start,h.2.2.parked.read_ne_start,h.2.2.parked.1,
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

theorem one_hoare (stride fuel : ℕ) (wit : Tape) (pos neg suffix : List Bool)
    (hw : Parked wit) (hh : wit.head = 1) :
    VerifierTraversalAdvance.machine.HoareTime (pred 0 stride fuel wit pos neg suffix)
      (pred 1 stride fuel wit pos neg suffix) 6 := by
  intro inp work out h
  have ha := VerifierTraversalAdvance.advance_hoare 0 wit pos neg suffix
    (VerifierIndexedField.counter stride) (regTape fuel) out hw.read_ne_start hh
    (VerifierReactionLoop.word_parked _).read_ne_start (parked_regTape _).read_ne_start
    h.2.2.parked.read_ne_start h.2.2.parked.1
  obtain ⟨c,t,ht,hr,hh',hi,hwork,hout⟩ := ha inp work out ⟨h.1,h.2.1,rfl⟩
  exact ⟨c,t,by simpa using ht,hr,hh',hi,hwork,by rw [hout]; exact h.2.2⟩

def machine : TM 11 := seqTM (clearWorkTM 1) VerifierTraversalAdvance.machine

theorem reset_hoare (k stride fuel : ℕ) (wit : Tape) (pos neg suffix : List Bool)
    (hw : Parked wit) (hh : wit.head = 1) :
    machine.HoareTime (pred k stride fuel wit pos neg suffix)
      (pred 1 stride fuel wit pos neg suffix) (2*k+12) := by
  have h := seqTM_hoareTime _ _ (clear_hoare k stride fuel wit pos neg suffix hw)
    (stable 0 stride fuel wit pos neg suffix hw) (one_hoare stride fuel wit pos neg suffix hw hh)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierFlowReset
