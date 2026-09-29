module

public import proofs.UnconstrainedPACDetection.VerifierTotalsCompare

@[expose] public section

namespace UnconstrainedPACDetection.VerifierTapeCleanup
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
variable {n : ℕ}

def safe (w : Fin n → Tape) : Prop := ∀ j, (w j).read ≠ .start ∧ 1 ≤ (w j).head
def frame (w : Fin n → Tape) (inp₀ out₀ : Tape) : Tape → (Fin n → Tape) → Tape → Prop :=
  fun inp work out => inp = inp₀ ∧ work = w ∧ out = out₀
def cleared (w : Fin n → Tape) (j : Fin n) := Function.update w j (wordTape [])

theorem safe_cleared (w : Fin n → Tape) (idx : Fin n) (h : safe w) : safe (cleared w idx) := by
  intro j
  by_cases hj : j = idx
  · subst j
    simp only [cleared, Function.update_self]
    exact ⟨(Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start, by rfl⟩
  · simpa [cleared, Function.update_of_ne hj] using h j

theorem stable (w : Fin n → Tape) (inp₀ out₀ : Tape) (hw : safe w)
    (hi : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) :
    ∀ inp work out, frame w inp₀ out₀ inp work out →
      frame w inp₀ out₀ (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out ⟨rfl,rfl,rfl⟩
  exact phaseTransition_eq_self_of_reads_ne_start hi (fun j => (hw j).1) ho

theorem clear_hoare (idx : Fin n) (x : List Bool) (w : Fin n → Tape) (inp₀ out₀ : Tape)
    (hx : w idx = wordTape x) (hw : safe w) (hi : inp₀.read ≠ .start)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (clearWorkTM idx).HoareTime (frame w inp₀ out₀) (frame (cleared w idx) inp₀ out₀)
      (2*x.length+5) := by
  let P : Tape → (Fin n → Tape) → Tape → Prop := fun inp work out =>
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

def restored (w : Fin n → Tape) (idx : Fin n) : Fin n → Tape :=
  Function.update w idx ⟨1,(w idx).cells⟩

theorem safe_restored (w : Fin n → Tape) (idx : Fin n) (hw : safe w)
    (hn : ∀ q, 1 ≤ q → (w idx).cells q ≠ .start) : safe (restored w idx) := by
  intro j
  by_cases hj : j = idx
  · subst j
    simp only [restored, Function.update_self]
    exact ⟨hn 1 le_rfl,le_rfl⟩
  · simpa [restored,Function.update_of_ne hj] using hw j

theorem rewind_hoare (idx : Fin n) (w : Fin n → Tape) (inp₀ out₀ : Tape)
    (hm : (w idx).cells 0 = .start) (hn : ∀ q, 1 ≤ q → (w idx).cells q ≠ .start)
    (hw : safe w) (hi : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (rewindWorkTM idx).HoareTime (frame w inp₀ out₀) (frame (restored w idx) inp₀ out₀)
      ((w idx).head+2) := by
  let P : Tape → (Fin n → Tape) → Tape → Prop := fun inp work out =>
    inp = inp₀ ∧ (work idx).cells = (w idx).cells ∧
      (∀ j, j ≠ idx → work j = w j) ∧ out = out₀
  have h := rewindWorkTM_hoareTime_frame idx (w idx).head (P := P) (by
    rintro inp work out inp' work' out' ⟨hin,hcells,hwork,hout⟩ hc _ hf hin' hoc hoh'
    refine ⟨hin'.trans hin,hc.trans hcells,fun j hj => (hf j hj).trans (hwork j hj),?_⟩
    exact (Tape.ext hoh' hoc).trans hout)
  rintro inp work out ⟨hin₀,hwork₀,hout₀⟩
  subst inp
  subst work
  subst out
  obtain ⟨d,t,hb,hd,hh,hhead,hin,hcells,hwork,hout⟩ := h inp₀ w out₀
    ⟨hm,hn,le_rfl,hi,ho,hoh,fun j _ => hw j,rfl,rfl,fun _ _ => rfl,rfl⟩
  refine ⟨d,t,hb,hd,hh,hin,?_,hout⟩
  funext j
  by_cases hj : j = idx
  · subst j
    simp only [restored,Function.update_self]
    exact Tape.ext hhead hcells
  · simpa [restored,Function.update_of_ne hj] using hwork j hj

def machine (idx : Fin n) : TM n := seqTM (rewindWorkTM idx) (clearWorkTM idx)

/-- Rewind a consumed binary word and erase it, preserving the other tapes. -/
theorem cleanup_hoare (idx : Fin n) (xs : List Bool) (w : Fin n → Tape) (inp₀ out₀ : Tape)
    (hc : (w idx).cells = (wordTape xs).cells) (hw : safe w)
    (hi : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (machine idx).HoareTime (frame w inp₀ out₀) (frame (cleared w idx) inp₀ out₀)
      ((w idx).head+2*xs.length+8) := by
  have hm := (Tape.StartInvariant.init_ofBool xs).move .right
  change (wordTape xs).StartInvariant at hm
  have hm0 : (w idx).cells 0 = .start := by rw [hc]; exact hm.1
  have hmn : ∀ q, 1 ≤ q → (w idx).cells q ≠ .start := by
    intro q hq; rw [hc]; exact hm.2 q hq
  have hs := safe_restored w idx hw hmn
  have he : restored w idx idx = wordTape xs := by
    apply Tape.ext
    · simp only [restored,Function.update_self]; rfl
    · simpa [restored] using hc
  have hr := rewind_hoare idx w inp₀ out₀ hm0 hmn hw hi ho hoh
  have hh := clear_hoare idx xs (restored w idx) inp₀ out₀ he hs hi ho hoh
  have h := seqTM_hoareTime _ _ hr (stable (restored w idx) inp₀ out₀ hs hi ho) hh
  have heq : cleared (restored w idx) idx = cleared w idx := by
    simp only [cleared,restored,Function.update_idem]
  rw [heq] at h
  exact h.mono_bound (by omega)

def totals : TM 11 := seqTM (machine 7) (machine 8)

theorem totals_hoare (xs ys : List Bool) (w : Fin 11 → Tape) (inp₀ out₀ : Tape)
    (hx : (w 7).cells = (wordTape xs).cells) (hy : (w 8).cells = (wordTape ys).cells)
    (hw : safe w) (hi : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    totals.HoareTime (frame w inp₀ out₀) (frame (cleared (cleared w 7) 8) inp₀ out₀)
      ((w 7).head+(w 8).head+2*xs.length+2*ys.length+17) := by
  have hs := safe_cleared w 7 hw
  have hfirst := cleanup_hoare 7 xs w inp₀ out₀ hx hw hi ho hoh
  have hsecond := cleanup_hoare 8 ys (cleared w 7) inp₀ out₀
    (by simpa [cleared] using hy) hs hi ho hoh
  have h := seqTM_hoareTime _ _ hfirst (stable (cleared w 7) inp₀ out₀ hs hi ho) hsecond
  exact h.mono_bound (by simp only [cleared,Function.update_of_ne (by decide : (8 : Fin 11) ≠ 7)]; omega)

end UnconstrainedPACDetection.VerifierTapeCleanup
