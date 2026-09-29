module

public import proofs.UnconstrainedPACDetection.VerifierMaskReader

@[expose] public section

namespace UnconstrainedPACDetection.VerifierMaskRestore
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierIndexedField (counter exhausted)

def fixed (inp₀ wt out₀ : Tape) : Complexity.TM.TapePred 1 :=
  fun inp work out => inp = inp₀ ∧ work = (fun _ => wt) ∧ out = out₀

theorem counter_hoare (k : ℕ) (inp₀ out₀ : Tape)
    (hi : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (rewindWorkTM (0 : Fin 1)).HoareTime
      (fixed inp₀ (exhausted k) out₀) (fixed inp₀ (counter k) out₀) (k+3) := by
  let P : Complexity.TM.TapePred 1 := fun inp work out =>
    inp = inp₀ ∧ (work 0).cells = (counter k).cells ∧ out = out₀
  have h := rewindWorkTM_hoareTime_frame (0 : Fin 1) (k+1) (P := P) (by
    rintro inp work out inp' work' out' ⟨hin,hc,hout⟩ hc' _ _ hin' hoc hoh'
    exact ⟨hin'.trans hin,hc'.trans hc,(Tape.ext hoh' hoc).trans hout⟩)
  rintro inp work out ⟨rfl,rfl,rfl⟩
  have hm := (Tape.StartInvariant.init_ofBool (List.replicate k true)).move .right
  obtain ⟨d,t,hb,hd,hh,hhead,hin,hcells,hout⟩ := h inp (fun _ => exhausted k) out
    ⟨hm.1,hm.2,le_rfl,hi,ho,hoh,(by intro j hj; exact (hj (Subsingleton.elim _ _)).elim),rfl,rfl,rfl⟩
  refine ⟨d,t,hb,hd,hh,hin,?_,hout⟩
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact Tape.ext hhead hcells

theorem input_hoare (src : List Bool) (k : ℕ) (inp₀ out₀ : Tape)
    (hc : inp₀.cells = (wordTape src).cells)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (rewindInputTM (n := 1)).HoareTime
      (fixed inp₀ (counter k) out₀) (fixed (wordTape src) (counter k) out₀) (inp₀.head+2) := by
  let P : Complexity.TM.TapePred 1 := fun inp work out =>
    inp.cells = inp₀.cells ∧ work = (fun _ => counter k) ∧ out = out₀
  have hm := (Tape.StartInvariant.init_ofBool src).move .right
  have hr := rewindInputTM_hoareTime_frame (n := 1) inp₀.head (P := P) (by
    rintro inp work out inp' work' out' ⟨hin,hwork,hout⟩ hin' _ hw' ho'
    exact ⟨hin'.trans hin,hw'.trans hwork,ho'.trans hout⟩)
  rintro inp work out ⟨rfl,rfl,rfl⟩
  obtain ⟨d,t,ht,hd,hh,hh1,hcells,hw',ho'⟩ := hr inp (fun _ => counter k) out
    ⟨by rw [hc]; exact hm.1,by intro j hj; rw [hc]; exact hm.2 j hj,
      le_rfl,ho,hoh,(by intro j; exact
        ⟨(Tape.init_move_right_hasBinaryString _).hasBinarySuffix.read_ne_start,le_rfl⟩),rfl,rfl,rfl⟩
  exact ⟨d,t,ht,hd,hh,Tape.ext hh1 (hcells.trans hc),hw',ho'⟩

def machine : TM 1 := seqTM (rewindWorkTM 0) rewindInputTM

theorem restore_hoare (src : List Bool) (k : ℕ) (inp₀ out₀ : Tape)
    (hc : inp₀.cells = (wordTape src).cells) (hi : inp₀.read ≠ .start)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    machine.HoareTime (fixed inp₀ (exhausted k) out₀)
      (fixed (wordTape src) (counter k) out₀) (inp₀.head+k+6) := by
  have stable : ∀ inp work out, fixed inp₀ (counter k) out₀ inp work out →
      fixed inp₀ (counter k) out₀ (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
    rintro inp work out ⟨rfl,rfl,rfl⟩
    exact phaseTransition_eq_self_of_reads_ne_start hi
      (fun _ => (Tape.init_move_right_hasBinaryString _).hasBinarySuffix.read_ne_start) ho
  have h := seqTM_hoareTime _ _ (counter_hoare k inp₀ out₀ hi ho hoh) stable
    (input_hoare src k inp₀ out₀ hc ho hoh)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierMaskRestore
