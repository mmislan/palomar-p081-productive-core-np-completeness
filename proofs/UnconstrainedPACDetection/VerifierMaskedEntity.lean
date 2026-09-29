module

public import proofs.UnconstrainedPACDetection.VerifierMaskBranch

@[expose] public section

namespace UnconstrainedPACDetection.VerifierMaskedEntity
open Complexity Complexity.TM
open VerifierEntityLift (frame)
open VerifierIndexedField (counter)
open VerifierBufferedProduct (wordTape)

def ready (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (x : ℕ) (selected a : Bool) : Complexity.TM.TapePred 13 := fun inp work out =>
  inp.HasBinarySuffix s.encode ∧ inp.cells = (wordTape s.encode).cells ∧
  (∀ j, j ≠ 11 → work j = frame s w (counter (2+x)) j) ∧
  (work 11).HasBinaryPrefix [selected] ∧ (work 11).cells 0 = .start ∧ out.HasBinaryPrefix [a]

theorem read_hoare (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (x : ℕ) (hx : x < w.mask.length) (a : Bool) :
    VerifierMaskRouting.machine.HoareTime (VerifierEntityStep.pred s w (2+x) a)
      (ready s w x (w.mask.getD x false) a) (5*x+15) := by
  rintro inp work out ⟨hin,hcells,hwork,hout⟩
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hds,hdm,hdo⟩ :=
    VerifierMaskRouting.read_hoare w x hx (frame s w (counter (2+x))) inp out
      rfl rfl rfl (fun j => (VerifierEntityAdvance.frame_safe s w (2+x) j).1)
      hin.read_ne_start (by rw [hout.read_blank]; decide)
      inp work out ⟨rfl,hwork,rfl⟩
  refine ⟨d,t,ht,hd,hh,?_,?_,hdw,hds,hdm,?_⟩
  · rw [hdi]; exact hin
  · rw [hdi]; exact hcells
  · rw [hdo]; exact hout

theorem ready_work (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (x : ℕ) (b a : Bool) (inp : Tape) (work : Fin 13 → Tape) (out : Tape)
    (h : ready s w x b a inp work out) :
    work = Function.update (frame s w (counter (2+x))) 11 (VerifierVerdictAnd.one .start b) := by
  funext j
  by_cases hj : j = 11
  · subst j
    rw [Function.update_self,VerifierVerdictAnd.prefix_eq _ _ h.2.2.2.1,h.2.2.2.2.1]
  · rw [Function.update_of_ne hj]; exact h.2.2.1 j hj

def conditional : TM 13 := VerifierMaskBranch.machine VerifierEntityStep.checked VerifierEntityAdvance.machine

def bodyBound (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) (x : ℕ) : ℕ :=
  17000*(VerifierCanonicalBuffers.envelope s w [] []+1)^3+3*s.encode.length+2*x+24

theorem conditional_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) (b a : Bool) : conditional.HoareTime
      (ready s w x.val b a)
      (VerifierEntityStep.pred s w (2+x.val+1)
        (if b then VerifierEntityCheck.verdict s hn x w && a else a)) (bodyBound s w x.val+3) := by
  have branch : (if b then VerifierEntityStep.checked else VerifierEntityAdvance.machine).HoareTime
      (VerifierEntityStep.pred s w (2+x.val) a)
      (VerifierEntityStep.pred s w (2+x.val+1)
        (if b then VerifierEntityCheck.verdict s hn x w && a else a)) (bodyBound s w x.val) := by
    cases b
    · exact (VerifierEntityStep.skipped_hoare s w (2+x.val) a).mono_bound (by unfold bodyBound; omega)
    · exact VerifierEntityStep.checked_hoare s hs hn x w hw a
  intro inp work out h
  obtain ⟨d,t,ht,hd,hh,hdi,hdc,hdw,hdo⟩ := branch inp (frame s w (counter (2+x.val))) out
    ⟨h.1,h.2.1,rfl,h.2.2.2.2.2⟩
  have hr := VerifierMaskBranch.execute VerifierEntityStep.checked VerifierEntityAdvance.machine
    b inp out (frame s w (counter (2+x.val))) h.1.read_ne_start
    (by rw [h.2.2.2.2.2.read_blank]; decide)
    (fun j => (VerifierEntityAdvance.frame_safe s w (2+x.val) j).1) rfl hd hh
    hdi.read_ne_start (by intro j; rw [hdw]; exact (VerifierEntityAdvance.frame_safe s w _ j).1)
    (by rw [hdo.read_blank]; decide)
  rw [← ready_work s w x.val b a inp work out h] at hr
  exact ⟨⟨conditional.qhalt,d.input,d.work,d.output⟩,t+3,by omega,hr,rfl,hdi,hdc,hdw,hdo⟩

theorem ready_stable (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (x : ℕ) (b a : Bool) : ∀ inp work out, ready s w x b a inp work out →
      ready s w x b a (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have hwork : ∀ j, (work j).read ≠ .start := by
    intro j
    by_cases hj : j = 11
    · subst j; rw [h.2.2.2.1.read_blank]; decide
    · rw [h.2.2.1 j hj]; exact (VerifierEntityAdvance.frame_safe s w (2+x) j).1
  obtain ⟨hi,hw,ho⟩ := phaseTransition_eq_self_of_reads_ne_start h.1.read_ne_start hwork
    (by rw [h.2.2.2.2.2.read_blank]; decide)
  simpa only [hi,hw,ho] using h

def machine : TM 13 := seqTM VerifierMaskRouting.machine conditional

/-- One complete entity iteration is now selected by the actual witness mask.
An unselected entity preserves the accumulator; a selected one conjoins its
productivity verdict. Both branches advance and restore the same frame. -/
theorem entity_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) (hm : w.mask.length = s.entities) (a : Bool) :
    machine.HoareTime (VerifierEntityStep.pred s w (2+x.val) a)
      (VerifierEntityStep.pred s w (2+x.val+1)
        (if w.mask.getD x.val false then VerifierEntityCheck.verdict s hn x w && a else a))
      (bodyBound s w x.val+5*x.val+19) := by
  have h := seqTM_hoareTime _ _ (read_hoare s w x.val (by rw [hm]; exact x.isLt) a)
    (ready_stable s w x.val (w.mask.getD x.val false) a)
    (conditional_hoare s hs hn x w hw (w.mask.getD x.val false) a)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierMaskedEntity
