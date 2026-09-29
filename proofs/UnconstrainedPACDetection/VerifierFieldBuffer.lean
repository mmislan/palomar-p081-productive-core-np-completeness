module

public import proofs.UnconstrainedPACDetection.VerifierFieldPayload
public import proofs.Complexitylib.Models.TuringMachine.Internal
public import proofs.Complexitylib.Models.TuringMachine.Subroutines.Internal

@[expose] public section

/-! Read an actual PAC field into an operand work tape, preserving the real
output. This prepares the field decoder for arithmetic composition. -/
namespace UnconstrainedPACDetection.VerifierFieldBuffer
open Complexity
open Complexity.TM

def machine : TM 1 where
  Q := VerifierFieldPayload.machine.Q
  qstart := VerifierFieldPayload.machine.qstart
  qhalt := VerifierFieldPayload.machine.qhalt
  δ := fun q i w o =>
    let r := VerifierFieldPayload.machine.δ q i (fun j => Fin.elim0 j) (w 0)
    (r.1, fun _ => r.2.2.1, readBackWrite o, r.2.2.2.1,
      fun _ => r.2.2.2.2.2, idleDir o)
  δ_right_of_start := by
    intro q i w o
    have h := VerifierFieldPayload.machine.δ_right_of_start q i (fun j => Fin.elim0 j) (w 0)
    refine ⟨h.1, ?_, idleDir_right_of_start⟩
    intro j hj
    have hj0 : j = 0 := Subsingleton.elim _ _
    subst j
    exact h.2.2 hj

def wrap (out : Tape) (c : Cfg 0 VerifierFieldPayload.machine.Q) : Cfg 1 machine.Q :=
  { state := c.state, input := c.input, work := fun _ => c.output, output := out }

theorem wrap_step (out : Tape) (hout : out.read ≠ .start)
    {c d : Cfg 0 VerifierFieldPayload.machine.Q}
    (hs : VerifierFieldPayload.machine.step c = some d) :
    machine.step (wrap out c) = some (wrap out d) := by
  have hh : c.state ≠ VerifierFieldPayload.machine.qhalt := state_ne_qhalt_of_step hs
  have hw : (fun j : Fin 0 => (c.work j).read) = (fun j => Fin.elim0 j) := by
    funext j; exact Fin.elim0 j
  rcases hd : VerifierFieldPayload.machine.δ c.state c.input.read
      (fun j => Fin.elim0 j) c.output.read with ⟨q, ww, ow, idir, wdir, odir⟩
  simp only [TM.step, hh, ↓reduceIte, hw, hd] at hs
  cases hs
  have keep := transitionTape_eq_self hout
  simpa [TM.step, machine, wrap, hh, hd, transitionTape] using keep

theorem wrap_run (out : Tape) (hout : out.read ≠ .start)
    {c d : Cfg 0 VerifierFieldPayload.machine.Q} {t : ℕ}
    (h : VerifierFieldPayload.machine.reachesIn t c d) :
    machine.reachesIn t (wrap out c) (wrap out d) := by
  induction h with
  | zero => exact .zero
  | step hs _ ih => exact .step (wrap_step out hout hs) ih

theorem field_boundary (field suffix : List Bool) (inp buffer out : Tape)
    (hin : inp.HasBinarySuffix (BinaryFields.encodeField field ++ suffix))
    (hbuffer : buffer.HasBinaryPrefix []) (hzero : buffer.cells 0 = .start)
    (hout : out.read ≠ .start) :
    ∃ d, machine.reachesIn (2 * field.length + 1)
      { state := machine.qstart, input := inp, work := fun _ => buffer, output := out } d ∧
      machine.halted d ∧ d.input.HasBinarySuffix suffix ∧
      (d.work 0).HasBinaryPrefix field ∧ (d.work 0).cells 0 = .start ∧ d.output = out := by
  let c : Cfg 0 VerifierFieldPayload.machine.Q :=
    { state := VerifierFieldPayload.machine.qstart, input := inp,
      work := (fun j => Fin.elim0 j), output := buffer }
  obtain ⟨d, hd, hh, hi, ho⟩ := VerifierFieldPayload.field_boundary field suffix c [] rfl hin hbuffer
  refine ⟨wrap out d, wrap_run out hout hd, hh, hi, ?_, ?_, rfl⟩
  · simpa [wrap] using ho
  · exact output_cells_zero_eq_start_of_reachesIn hd hzero

def preparedMachine : TM 1 := seqTM machine (rewindWorkTM 0)

/-- Actual composed field-to-operand operation. Parsing, the phase transition,
and the work-head rewind are all charged; the input suffix and output survive. -/
theorem prepared_hoare (field suffix : List Bool) (out₀ : Tape)
    (hout : out₀.read ≠ .start) (houtHead : 1 ≤ out₀.head) :
    preparedMachine.HoareTime
      (fun inp work out =>
        inp.HasBinarySuffix (BinaryFields.encodeField field ++ suffix) ∧
        (work 0).HasBinaryPrefix [] ∧ (work 0).cells 0 = .start ∧ out = out₀)
      (fun inp work out => inp.HasBinarySuffix suffix ∧
        (work 0).HasBinaryString field ∧ (work 0).cells 0 = .start ∧ out = out₀)
      (3 * field.length + 5) := by
  let mid : TM.TapePred 1 := fun inp work out =>
    inp.HasBinarySuffix suffix ∧ (work 0).HasBinaryPrefix field ∧
      (work 0).cells 0 = .start ∧ out = out₀
  let invariant : TM.TapePred 1 := fun inp work out =>
    inp.HasBinarySuffix suffix ∧ (work 0).HasBinaryContent field ∧
      (work 0).cells 0 = .start ∧ out = out₀
  have first : machine.HoareTime
      (fun inp work out =>
        inp.HasBinarySuffix (BinaryFields.encodeField field ++ suffix) ∧
        (work 0).HasBinaryPrefix [] ∧ (work 0).cells 0 = .start ∧ out = out₀)
      mid (2 * field.length + 1) := by
    rintro inp work out ⟨hin, hb, hz, hoEq⟩
    subst out
    obtain ⟨d, hd, hh, hi, ho, hz', hout'⟩ := field_boundary field suffix inp (work 0) out₀ hin hb hz hout
    have hw : (fun _ : Fin 1 => work 0) = work := by
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j; rfl
    exact ⟨d, 2 * field.length + 1, le_rfl, by simpa only [hw] using hd,
      hh, hi, ho, hz', hout'⟩
  have stable : ∀ inp work out, mid inp work out →
      mid (transitionInput inp) (fun i => transitionTape (work i)) (transitionTape out) := by
    rintro inp work out h
    obtain ⟨hi, hb, hz, hoEq⟩ := h
    subst out
    have hw : ∀ j, (work j).read ≠ .start := by
      intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [hb.read_blank]; decide
    obtain ⟨hin, hwork, hout'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start hw hout
    simpa only [hin, hwork, hout'] using (show mid inp work out₀ from ⟨hi, hb, hz, rfl⟩)
  have rewind := rewindWorkTM_hoareTime_frame (n := 1) 0 (field.length + 1)
    (P := invariant) (by
      rintro inp work out inp' work' out' ⟨hi, hc, hz, ho⟩ hcells _hhead _hother hin houtCells houtHead'
      refine ⟨by simpa only [hin] using hi, ?_, ?_, ?_⟩
      · simpa only [Tape.HasBinaryContent, hcells] using hc
      · simpa only [hcells] using hz
      · exact (Tape.ext houtHead' houtCells).trans ho)
  have second : (rewindWorkTM (n := 1) 0).HoareTime mid
      (fun inp work out => inp.HasBinarySuffix suffix ∧
        (work 0).HasBinaryString field ∧ (work 0).cells 0 = .start ∧ out = out₀)
      (field.length + 3) := by
    apply rewind.consequence
    · rintro inp work out ⟨hi, hb, hz, hoEq⟩
      subst out
      have hc : (work 0).HasBinaryContent field := hb.2
      refine ⟨hz, hc.cells_ne_start, by rw [hb.1], hi.read_ne_start, hout, houtHead, ?_, hi, hc, hz, rfl⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · rintro inp work out ⟨hh, hi, hc, hz, ho⟩
      exact ⟨hi, hc.hasBinaryString hh, hz, ho⟩
    · omega
  have composed := seqTM_hoareTime machine (rewindWorkTM 0) first stable second
  exact composed.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierFieldBuffer
