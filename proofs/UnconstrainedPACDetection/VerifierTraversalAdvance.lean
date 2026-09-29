module

public import proofs.UnconstrainedPACDetection.VerifierTraversalContribution
public import proofs.UnconstrainedPACDetection.VerifierIndexAdvance

@[expose] public section

/-! Advance the flow index while preserving persistent traversal tapes. -/
namespace UnconstrainedPACDetection.VerifierTraversalAdvance
open Complexity
open Complexity.TM
open VerifierTraversalContribution (extend pred)
open VerifierCoefficientIteration (layout layout_off)

private theorem extend_off (w : Fin 9 → Tape) (stride loop : Tape)
    (hw : ∀ j, (w j).read ≠ .start) (hst : stride.read ≠ .start) (hlp : loop.read ≠ .start) :
    ∀ j, (extend w stride loop j).read ≠ .start := by
  intro j
  fin_cases j
  · exact hw 0
  · exact hw 1
  · exact hw 2
  · exact hw 3
  · exact hw 4
  · exact hw 5
  · exact hw 6
  · exact hw 7
  · exact hw 8
  · exact hst
  · exact hlp

theorem frame_off (k : ℕ) (wit : Tape) (pos neg : List Bool) (stride loop : Tape)
    (hi : wit.read ≠ .start) (hst : stride.read ≠ .start) (hlp : loop.read ≠ .start) :
    ∀ j, (extend (layout [] k wit pos neg) stride loop j).read ≠ .start :=
  extend_off _ stride loop (layout_off [] k wit pos neg hi) hst hlp

theorem stable (k : ℕ) (wit : Tape) (pos neg suffix : List Bool) (stride loop out₀ : Tape)
    (hi : wit.read ≠ .start) (hst : stride.read ≠ .start) (hlp : loop.read ≠ .start) (ho : out₀.read ≠ .start) :
    ∀ inp work out, pred k wit pos neg suffix stride loop out₀ inp work out →
      pred k wit pos neg suffix stride loop out₀ (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out ⟨hs,rfl,rfl⟩
  obtain ⟨hin,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start hs.read_ne_start
    (frame_off k wit pos neg stride loop hi hst hlp) ho
  exact ⟨by simpa only [hin] using hs,hw,hout⟩

def machine : TM 11 := placeWorkTM 0 2 (VerifierIndexAdvance.machine 1)

theorem advance_hoare (k : ℕ) (wit : Tape) (pos neg suffix : List Bool) (stride loop out₀ : Tape)
    (hi : wit.read ≠ .start) (hwh : wit.head = 1)
    (hst : stride.read ≠ .start) (hlp : loop.read ≠ .start)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    machine.HoareTime (pred k wit pos neg suffix stride loop out₀)
      (pred (k+1) wit pos neg suffix stride loop out₀) (2*k+6) := by
  rintro inp work out ⟨hs,hw,hout⟩
  subst work
  subst out
  let w := layout [] k wit pos neg
  have hsafe : VerifierContributionReset.safe w := by
    intro j
    refine ⟨layout_off [] k wit pos neg hi j,?_⟩
    fin_cases j <;> first | exact Nat.le_of_eq hwh.symm | exact le_rfl
  obtain ⟨d,t,hb,hd,hh,hin,hdw,hout⟩ := VerifierIndexAdvance.successor_hoare 1 k w inp out₀ rfl hsafe
    hs.read_ne_start ho hoh inp w out₀ ⟨rfl,rfl,rfl⟩
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    (VerifierIndexAdvance.machine 1) 0 2 (extend w stride loop) hd (by
      intro j hj
      fin_cases j
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · exact hst
      · exact hlp)
  have he : placeWorkCfg (VerifierIndexAdvance.machine 1) 0 2 (extend w stride loop)
      ⟨(VerifierIndexAdvance.machine 1).qstart,inp,w,out₀⟩ =
      (⟨machine.qstart,inp,extend w stride loop,out₀⟩ : Cfg 11 machine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,extend]
    · rfl
  refine ⟨placeWorkCfg (VerifierIndexAdvance.machine 1) 0 2 (extend w stride loop) d,t,hb,?_,hh,?_,?_,hout⟩
  · change machine.reachesIn _ _ _ at hp
    simpa only [he] using hp
  · change d.input.HasBinarySuffix suffix
    simpa only [hin] using hs
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,extend,hdw,w,layout,
      VerifierSignedContribution.extend,VerifierWitnessProduct.initial]

end UnconstrainedPACDetection.VerifierTraversalAdvance
