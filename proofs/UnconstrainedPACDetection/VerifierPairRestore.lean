module

public import proofs.UnconstrainedPACDetection.VerifierPairTotal
public import proofs.Complexitylib.Models.TuringMachine.Subroutines.Internal

@[expose] public section

namespace UnconstrainedPACDetection.VerifierPairRestore
open Complexity Complexity.TM

def word (bits : List Bool) : Tape := (Tape.init (bits.map Γ.ofBool)).move .right

theorem word_parked (bits : List Bool) : Parked (word bits) :=
  ⟨by rfl,fun j hj => ((Tape.StartInvariant.init_ofBool bits).move .right).2 j hj⟩

theorem acc_cells (bits : List Bool) (t : Tape) (h : OutAcc bits t) :
    t.cells = (word bits).cells := by
  have hb : ({t with head := 1} : Tape).HasBinaryString bits :=
    ⟨rfl,h.2.2.1,fun i hi => h.2.2.2 (i+1) (by omega)⟩
  have he := Tape.eq_init_move_right_of_hasBinaryString
    (t := ({t with head := 1} : Tape)) hb (show ({t with head := 1} : Tape).cells 0 = .start from h.2.1)
  have hc := congrArg Tape.cells he
  exact hc

theorem updated_parked {n : Nat} (work : Fin n → Tape) (idx : Fin n) (bits : List Bool)
    (hw : ∀ j, Parked (work j)) : ∀ j, Parked (Function.update work idx (word bits) j) := by
  intro j
  by_cases hj : j = idx
  · subst j; simpa using word_parked bits
  · simpa only [Function.update_of_ne hj] using hw j

/-- Restore a parsed word to cell one, charging the actual append cursor.
All unrelated work tapes and the emitted verdict are preserved. -/
theorem restore_word {n : Nat} (idx : Fin n) (bits emitted : List Bool)
    (inp : Tape) (work : Fin n → Tape) (hi : Parked inp) (hw : ∀ j, Parked (work j))
    (hc : OutAcc bits (work idx)) :
    (rewindWorkTM idx).HoareTime (EmitPred inp work emitted)
      (EmitPred inp (Function.update work idx (word bits)) emitted) (bits.length+3) := by
  let P : Complexity.TM.TapePred n := fun a ws out => a = inp ∧
    (ws idx).cells = (word bits).cells ∧
    (∀ j, j ≠ idx → ws j = work j) ∧ OutAcc emitted out
  have h := rewindWorkTM_hoareTime_frame idx (bits.length+1) (P := P) (by
    rintro a ws out a' ws' out' ⟨ha,hcells,hother,ho⟩ hc' _ hw' hi' ho' hh'
    exact ⟨hi'.trans ha,hc'.trans hcells,fun j hj => (hw' j hj).trans (hother j hj),
      (Tape.ext hh' ho').symm ▸ ho⟩)
  apply h.consequence
  · rintro a ws out ⟨ha,hws,ho⟩
    subst a; subst ws
    exact ⟨hc.2.1,(hw idx).2,le_of_eq hc.1,hi.read_ne_start,ho.parked.read_ne_start,
      ho.parked.1,fun j _ => ⟨(hw j).read_ne_start,(hw j).1⟩,
      rfl,acc_cells bits _ hc,fun _ _ => rfl,ho⟩
  · rintro a ws out ⟨hh,ha,hcells,hother,ho⟩
    refine ⟨ha,?_,ho⟩
    funext j
    by_cases hj : j = idx
    · subst j
      simpa using Tape.ext hh hcells
    · simpa only [Function.update_of_ne hj] using hother j hj
  · omega

def machine {n : Nat} (srcIdx witIdx : Fin n) : TM n :=
  seqTM (rewindWorkTM srcIdx) (rewindWorkTM witIdx)

theorem restore_pair {n : Nat} (srcIdx witIdx : Fin n) (hne : witIdx ≠ srcIdx)
    (src wit emitted : List Bool) (inp : Tape) (work : Fin n → Tape)
    (hi : Parked inp) (hw : ∀ j, Parked (work j))
    (hs : OutAcc src (work srcIdx)) (hwit : OutAcc wit (work witIdx)) :
    (machine srcIdx witIdx).HoareTime (EmitPred inp work emitted)
      (EmitPred inp (Function.update (Function.update work srcIdx (word src))
        witIdx (word wit)) emitted) (src.length+wit.length+7) := by
  let W := Function.update work srcIdx (word src)
  have hpW : ∀ j, Parked (W j) := updated_parked work srcIdx src hw
  have hfirst := restore_word srcIdx src emitted inp work hi hw hs
  have hsecond := restore_word witIdx wit emitted inp W hi hpW (by
    simpa only [W,Function.update_of_ne hne] using hwit)
  have htotal := seqTM_hoareTime _ _ hfirst (emitPred_transition hi hpW emitted) hsecond
  exact htotal.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierPairRestore
