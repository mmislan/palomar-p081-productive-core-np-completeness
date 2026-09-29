module

public import proofs.UnconstrainedPACDetection.VerifierContributionReset

@[expose] public section

/-! Restore parked contribution cursors while retaining all tape cells. -/
namespace UnconstrainedPACDetection.VerifierContributionRewind
open Complexity
open Complexity.TM
open VerifierContributionReset (safe frame stable)

def restored (w : Fin 9 → Tape) (idx : Fin 9) : Fin 9 → Tape :=
  Function.update w idx ⟨1,(w idx).cells⟩

theorem safe_restored (w : Fin 9 → Tape) (idx : Fin 9) (hw : safe w)
    (hn : ∀ q, 1 ≤ q → (w idx).cells q ≠ .start) : safe (restored w idx) := by
  intro j
  by_cases hj : j = idx
  · subst j
    simp only [restored, Function.update_self]
    exact ⟨hn 1 le_rfl,le_rfl⟩
  · simpa [restored,Function.update_of_ne hj] using hw j

theorem rewind_hoare (idx : Fin 9) (w : Fin 9 → Tape) (inp₀ out₀ : Tape)
    (hm : (w idx).cells 0 = .start) (hn : ∀ q, 1 ≤ q → (w idx).cells q ≠ .start)
    (hw : safe w) (hi : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (rewindWorkTM idx).HoareTime (frame w inp₀ out₀) (frame (restored w idx) inp₀ out₀)
      ((w idx).head+2) := by
  let P : Tape → (Fin 9 → Tape) → Tape → Prop := fun inp work out =>
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

def machine : TM 9 := seqTM (rewindWorkTM 1) (rewindWorkTM 4)

theorem cursors_hoare (w : Fin 9 → Tape) (inp₀ out₀ : Tape)
    (hm1 : (w 1).cells 0 = .start) (hn1 : ∀ q, 1 ≤ q → (w 1).cells q ≠ .start)
    (hm4 : (w 4).cells 0 = .start) (hn4 : ∀ q, 1 ≤ q → (w 4).cells q ≠ .start)
    (hw : safe w) (hi : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    machine.HoareTime (frame w inp₀ out₀) (frame (restored (restored w 1) 4) inp₀ out₀)
      ((w 1).head+(w 4).head+5) := by
  have hs := safe_restored w 1 hw hn1
  have h1 := rewind_hoare 1 w inp₀ out₀ hm1 hn1 hw hi ho hoh
  have h4 := rewind_hoare 4 (restored w 1) inp₀ out₀
    (by simpa [restored] using hm4) (by simpa [restored] using hn4) hs hi ho hoh
  have h := seqTM_hoareTime _ _ h1 (stable (restored w 1) inp₀ out₀ hs hi ho) h4
  exact h.mono_bound (by simp [restored]; omega)

def reuse : TM 9 := seqTM VerifierContributionReset.reset machine

/-- All four temporary words are cleared and both saved cursors are restored;
the two totals and all remaining cells stay framed throughout. -/
theorem reuse_hoare (xs mag prod : List Bool) (sign : Bool) (w : Fin 9 → Tape) (inp₀ out₀ : Tape)
    (h0 : w 0 = VerifierBufferedProduct.wordTape xs)
    (h2 : w 2 = VerifierBufferedProduct.wordTape mag)
    (h3 : w 3 = VerifierBufferedProduct.wordTape [sign])
    (h5 : w 5 = VerifierBufferedProduct.wordTape prod)
    (hm1 : (w 1).cells 0 = .start) (hn1 : ∀ q, 1 ≤ q → (w 1).cells q ≠ .start)
    (hm4 : (w 4).cells 0 = .start) (hn4 : ∀ q, 1 ≤ q → (w 4).cells q ≠ .start)
    (hw : safe w) (hi : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    reuse.HoareTime (frame w inp₀ out₀)
      (frame (restored (restored (VerifierContributionReset.after w) 1) 4) inp₀ out₀)
      (2*xs.length+2*mag.length+2*prod.length+(w 1).head+(w 4).head+31) := by
  have hs : safe (VerifierContributionReset.after w) :=
    VerifierContributionReset.safe_cleared _ _ (VerifierContributionReset.safe_cleared _ _
      (VerifierContributionReset.safe_cleared _ _ (VerifierContributionReset.safe_cleared _ _ hw)))
  have hr := VerifierContributionReset.reset_hoare xs mag prod sign w inp₀ out₀ h0 h2 h3 h5 hw hi ho hoh
  have hc := cursors_hoare (VerifierContributionReset.after w) inp₀ out₀
    (by simpa [VerifierContributionReset.after,VerifierContributionReset.cleared] using hm1)
    (by simpa [VerifierContributionReset.after,VerifierContributionReset.cleared] using hn1)
    (by simpa [VerifierContributionReset.after,VerifierContributionReset.cleared] using hm4)
    (by simpa [VerifierContributionReset.after,VerifierContributionReset.cleared] using hn4)
    hs hi ho hoh
  have h := seqTM_hoareTime _ _ hr (stable _ inp₀ out₀ hs hi ho) hc
  exact h.mono_bound (by simp [VerifierContributionReset.after,VerifierContributionReset.cleared]; omega)

end UnconstrainedPACDetection.VerifierContributionRewind
