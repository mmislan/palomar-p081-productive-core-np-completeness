module

public import proofs.UnconstrainedPACDetection.VerifierSignedContribution

@[expose] public section

/-! Clear the contribution buffers while retaining arbitrary parked frames. -/
namespace UnconstrainedPACDetection.VerifierContributionReset
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)

def safe (w : Fin 9 → Tape) : Prop := ∀ j, (w j).read ≠ .start ∧ 1 ≤ (w j).head
def frame (w : Fin 9 → Tape) (inp₀ out₀ : Tape) : Tape → (Fin 9 → Tape) → Tape → Prop :=
  fun inp work out => inp = inp₀ ∧ work = w ∧ out = out₀
def cleared (w : Fin 9 → Tape) (j : Fin 9) := Function.update w j (wordTape [])

theorem safe_cleared (w : Fin 9 → Tape) (idx : Fin 9) (h : safe w) : safe (cleared w idx) := by
  intro j
  by_cases hj : j = idx
  · subst j
    simp only [cleared, Function.update_self]
    exact ⟨(Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start, by rfl⟩
  · simpa [cleared, Function.update_of_ne hj] using h j

theorem stable (w : Fin 9 → Tape) (inp₀ out₀ : Tape) (hw : safe w)
    (hi : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) :
    ∀ inp work out, frame w inp₀ out₀ inp work out →
      frame w inp₀ out₀ (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out ⟨rfl,rfl,rfl⟩
  exact phaseTransition_eq_self_of_reads_ne_start hi (fun j => (hw j).1) ho

theorem clear_hoare (idx : Fin 9) (x : List Bool) (w : Fin 9 → Tape) (inp₀ out₀ : Tape)
    (hx : w idx = wordTape x) (hw : safe w) (hi : inp₀.read ≠ .start)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (clearWorkTM idx).HoareTime (frame w inp₀ out₀) (frame (cleared w idx) inp₀ out₀)
      (2*x.length+5) := by
  let P : Tape → (Fin 9 → Tape) → Tape → Prop := fun inp work out =>
    inp = inp₀ ∧ (∀ j, j ≠ idx → work j = w j) ∧ out = out₀
  have h := clearWorkTM_hoareTime_frame_of_binaryString idx x (P := P) (by
    rintro inp work out inp' work' out' ⟨hin,hwork,hout⟩ _ hin' hout' hf
    exact ⟨hin'.trans hin,fun j hj => (hf j hj).trans (hwork j hj),hout'.trans hout⟩)
  rintro inp work out ⟨hin₀,hwork₀,hout₀⟩
  subst inp
  subst work
  subst out
  obtain ⟨d,t,hb,hd,hh,he,hin,hwd,hout⟩ := h inp₀ w out₀
    ⟨hx,hi,ho,hoh,fun j _ => hw j,rfl,fun _ _ => rfl,rfl⟩
  refine ⟨d,t,by omega,hd,hh,hin,?_,hout⟩
  funext j
  by_cases hj : j = idx
  · subst j
    simpa [cleared, wordTape] using he
  · simpa [cleared, Function.update_of_ne hj] using hwd j hj

def reset : TM 9 := seqTM (clearWorkTM 0)
  (seqTM (clearWorkTM 2) (seqTM (clearWorkTM 3) (clearWorkTM 5)))
def after (w : Fin 9 → Tape) := cleared (cleared (cleared (cleared w 0) 2) 3) 5

theorem reset_hoare (xs mag prod : List Bool) (sign : Bool) (w : Fin 9 → Tape) (inp₀ out₀ : Tape)
    (h0 : w 0 = wordTape xs) (h2 : w 2 = wordTape mag)
    (h3 : w 3 = wordTape [sign]) (h5 : w 5 = wordTape prod)
    (hw : safe w) (hi : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    reset.HoareTime (frame w inp₀ out₀) (frame (after w) inp₀ out₀)
      (2*xs.length+2*mag.length+2*prod.length+25) := by
  let w1 := cleared w 0
  let w2 := cleared w1 2
  let w3 := cleared w2 3
  have hs1 := safe_cleared w 0 hw
  have hs2 := safe_cleared w1 2 hs1
  have hs3 := safe_cleared w2 3 hs2
  have hfirst := clear_hoare 0 xs w inp₀ out₀ h0 hw hi ho hoh
  have hsecond := clear_hoare 2 mag w1 inp₀ out₀ (by simpa [w1,cleared] using h2) hs1 hi ho hoh
  have hthird := clear_hoare 3 [sign] w2 inp₀ out₀ (by simpa [w2,w1,cleared] using h3) hs2 hi ho hoh
  have hlast := clear_hoare 5 prod w3 inp₀ out₀ (by simpa [w3,w2,w1,cleared] using h5) hs3 hi ho hoh
  have ht := seqTM_hoareTime _ _ hthird (stable w3 inp₀ out₀ hs3 hi ho) hlast
  have hm := seqTM_hoareTime _ _ hsecond (stable w2 inp₀ out₀ hs2 hi ho) ht
  have hall := seqTM_hoareTime _ _ hfirst (stable w1 inp₀ out₀ hs1 hi ho) hm
  exact hall.mono_bound (by simp; omega)

end UnconstrainedPACDetection.VerifierContributionReset
