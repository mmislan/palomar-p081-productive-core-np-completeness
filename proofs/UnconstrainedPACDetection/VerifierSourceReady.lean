module

public import proofs.UnconstrainedPACDetection.VerifierSourceHeaderValidation

@[expose] public section

namespace UnconstrainedPACDetection.VerifierSourceReady
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierWitnessRegisters (pair)

def registers (bits : List Bool) (work : Fin 2 → Tape) (out : Tape) : Prop :=
  ∃ count v, count ≤ bits.length ∧
    work = pair (VerifierSourceHeaderGuard.unary count) (wordTape []) ∧
    out = one .start v ∧ (v = true ↔ VerifierSourceHeaderValidation.HasHeaders bits) ∧
    (v = true → ∃ ns, VerifierSourceGrammar.wire ns = bits ∧ ns.length = count)

def scanned (bits : List Bool) : Complexity.TM.TapePred 2 :=
  fun inp work out => inp.HasBinarySuffix [] ∧ inp.cells = (wordTape bits).cells ∧
    inp.head ≤ 2*bits.length+9 ∧ registers bits work out

def ready (bits : List Bool) : Complexity.TM.TapePred 2 :=
  fun inp work out => inp = wordTape bits ∧ registers bits work out

theorem scan_hoare (bits : List Bool) : VerifierSourceHeaderValidation.machine.HoareTime
    (fun inp work out => inp = wordTape bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (scanned bits) (2*bits.length+8) := by
  rintro inp work out ⟨rfl,rfl,rfl⟩
  obtain ⟨d,t,ht,hd,hh,hi,hr⟩ := VerifierSourceHeaderValidation.checked_hoare bits
    (wordTape bits) (fun _ => wordTape []) (wordTape [])
    ⟨(Tape.init_move_right_hasBinaryString bits).hasBinarySuffix,rfl,rfl⟩
  have hc := input_cells_eq_of_reachesIn hd
  have hb := (head_le_start_add_of_reachesIn _ hd).1
  change d.input.head ≤ 1+t at hb
  exact ⟨d,t,ht,hd,hh,hi,hc,by omega,hr⟩

theorem register_parked (bits : List Bool) (work : Fin 2 → Tape) (out : Tape)
    (h : registers bits work out) : (∀ j, Parked (work j)) ∧ Parked out := by
  obtain ⟨count,v,_,hw,ho,_,_⟩ := h
  subst work; subst out
  constructor
  · intro j; fin_cases j
    all_goals exact VerifierReactionLoop.word_parked _
  · exact (VerifierEntityLoopBody.acc_of_prefix _ _
      (VerifierVerdictCommit.one_prefix _ _) rfl).parked

theorem scanned_stable (bits : List Bool) :
    ∀ inp work out, scanned bits inp work out →
      scanned bits (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  obtain ⟨hw,ho⟩ := register_parked bits work out h.2.2.2
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start h.1.read_ne_start
    (fun j => (hw j).read_ne_start) ho.read_ne_start
  simpa only [hi',hw',ho'] using h

theorem rewind_hoare (bits : List Bool) : (rewindInputTM (n := 2)).HoareTime
    (scanned bits) (ready bits) (2*bits.length+11) := by
  let P : Complexity.TM.TapePred 2 := fun inp work out =>
    inp.cells = (wordTape bits).cells ∧ registers bits work out
  have hr := rewindInputTM_hoareTime_frame (n := 2) (2*bits.length+9) (P := P) (by
    rintro inp work out inp' work' out' ⟨hc,hreg⟩ hc' _ hw' ho'
    exact ⟨hc'.trans hc,by simpa only [hw',ho'] using hreg⟩)
  rintro inp work out ⟨_,hc,hbound,hreg⟩
  obtain ⟨hw,ho⟩ := register_parked bits work out hreg
  have hm := (Tape.StartInvariant.init_ofBool bits).move .right
  obtain ⟨d,t,ht,hd,hh,hhead,hcells,hregs⟩ := hr inp work out
    ⟨by rw [hc]; exact hm.1,by intro j hj; rw [hc]; exact hm.2 j hj,
      hbound,ho.read_ne_start,ho.1,(fun j => ⟨(hw j).read_ne_start,(hw j).1⟩),hc,hreg⟩
  exact ⟨d,t,ht,hd,hh,Tape.ext hhead hcells,hregs⟩

def machine : TM 2 := seqTM VerifierSourceHeaderValidation.machine rewindInputTM

theorem validation_hoare (bits : List Bool) : machine.HoareTime
    (fun inp work out => inp = wordTape bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (ready bits) (4*bits.length+20) := by
  have h := seqTM_hoareTime _ _ (scan_hoare bits) (scanned_stable bits) (rewind_hoare bits)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierSourceReady
