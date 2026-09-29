module

public import proofs.UnconstrainedPACDetection.VerifierActivationSemantics

@[expose] public section

namespace UnconstrainedPACDetection.VerifierActivationRow
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierActivationScan (flag)
open VerifierMaskRestore (fixed)

def parked (bits : List Bool) (k : ℕ) : Tape := ⟨k+1,(wordTape bits).cells⟩

theorem rewind_hoare (bits : List Bool) (k : ℕ) (inp out : Tape)
    (hi : inp.read ≠ .start) (ho : out.read ≠ .start) (hoh : 1 ≤ out.head) :
    (rewindWorkTM (0 : Fin 1)).HoareTime
      (fixed inp (parked bits k) out) (fixed inp (wordTape bits) out) (k+3) := by
  let P : Complexity.TM.TapePred 1 := fun i w o =>
    i = inp ∧ (w 0).cells = (wordTape bits).cells ∧ o = out
  have h := rewindWorkTM_hoareTime_frame (0 : Fin 1) (k+1) (P := P) (by
    rintro i w o i' w' o' ⟨hin,hc,hout⟩ hc' _ _ hin' hoc hoh'
    exact ⟨hin'.trans hin,hc'.trans hc,(Tape.ext hoh' hoc).trans hout⟩)
  rintro i w o ⟨hin,hw,ho'⟩
  subst i; subst w; subst o
  have hm := (Tape.StartInvariant.init_ofBool bits).move .right
  obtain ⟨d,t,ht,hd,hh,hhead,hin,hcells,hout⟩ := h inp (fun _ => parked bits k) out
    ⟨hm.1,hm.2,le_rfl,hi,ho,hoh,(by intro j hj; exact (hj (Subsingleton.elim _ _)).elim),rfl,rfl,rfl⟩
  refine ⟨d,t,ht,hd,hh,hin,?_,hout⟩
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact Tape.ext hhead hcells

def after (tail : List Bool) (orig wt out₀ : Tape) (n : ℕ) : Complexity.TM.TapePred 1 :=
  fun inp work out => inp.HasBinarySuffix tail ∧ inp.head = orig.head+n ∧
    inp.cells = orig.cells ∧ work = (fun _ => wt) ∧ out = out₀

theorem scan_hoare (es : List (List Bool × Bool)) (srcTail witTail : List Bool)
    (inp : Tape) (marker : Γ) (a : Bool)
    (hi : inp.HasBinarySuffix (BinaryFields.encode (es.map Prod.fst) ++ srcTail)) :
    VerifierActivationScan.machine.HoareTime
      (fixed inp (wordTape (BinaryFields.encodeField (es.map Prod.snd) ++ witTail)) (flag marker a))
      (after srcTail inp (parked (BinaryFields.encodeField (es.map Prod.snd) ++ witTail) (2*es.length))
        (VerifierVerdictAnd.one marker (VerifierActivationSide.hit es a))
        (BinaryFields.encode (es.map Prod.fst)).length)
      ((BinaryFields.encode (es.map Prod.fst)).length+2*es.length+1) := by
  rintro i w o ⟨hin,hw,ho'⟩
  subst i; subst w; subst o
  obtain ⟨d,hd,hh,hdi,hdh,hdc,_,hdwh,hdwc,hdo⟩ :=
    VerifierActivationSide.run es srcTail witTail
      ⟨(0 : Fin 5),inp,fun _ => wordTape (BinaryFields.encodeField (es.map Prod.snd) ++ witTail),flag marker a⟩
      marker a rfl hi (Tape.init_move_right_hasBinaryString _).hasBinarySuffix rfl
  refine ⟨d,_,le_rfl,hd,hh,hdi,hdh,hdc,?_,hdo⟩
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  apply Tape.ext
  · change (d.work 0).head = 2*es.length+1
    change (d.work 0).head = 1+2*es.length at hdwh
    omega
  · exact hdwc 0

def machine : TM 1 := seqTM VerifierActivationScan.machine (rewindWorkTM 0)

theorem row_hoare (es : List (List Bool × Bool)) (srcTail witTail : List Bool)
    (inp : Tape) (marker : Γ) (a : Bool)
    (hi : inp.HasBinarySuffix (BinaryFields.encode (es.map Prod.fst) ++ srcTail)) :
    machine.HoareTime
      (fixed inp (wordTape (BinaryFields.encodeField (es.map Prod.snd) ++ witTail)) (flag marker a))
      (after srcTail inp (wordTape (BinaryFields.encodeField (es.map Prod.snd) ++ witTail))
        (VerifierVerdictAnd.one marker (VerifierActivationSide.hit es a))
        (BinaryFields.encode (es.map Prod.fst)).length)
      ((BinaryFields.encode (es.map Prod.fst)).length+4*es.length+5) := by
  let bits := BinaryFields.encodeField (es.map Prod.snd) ++ witTail
  let res := VerifierVerdictAnd.one marker (VerifierActivationSide.hit es a)
  let n := (BinaryFields.encode (es.map Prod.fst)).length
  have hor : res.read ≠ .start := by change Γ.blank ≠ Γ.start; decide
  have stable : ∀ i w o, after srcTail inp (parked bits (2*es.length)) res n i w o →
      after srcTail inp (parked bits (2*es.length)) res n
        (transitionInput i) (fun j => transitionTape (w j)) (transitionTape o) := by
    rintro i w o ⟨his,hih,hic,rfl,rfl⟩
    have hm := (Tape.StartInvariant.init_ofBool bits).move .right
    have hwr : (parked bits (2*es.length)).read ≠ .start := hm.2 (2*es.length+1) (by omega)
    obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start his.read_ne_start (fun _ => hwr) hor
    exact ⟨by rwa [hi'],by rwa [hi'],by rwa [hi'],hw',ho'⟩
  have second : (rewindWorkTM (0 : Fin 1)).HoareTime
      (after srcTail inp (parked bits (2*es.length)) res n)
      (after srcTail inp (wordTape bits) res n) (2*es.length+3) := by
    rintro i w o ⟨his,hih,hic,rfl,rfl⟩
    obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := rewind_hoare bits (2*es.length) i res
      his.read_ne_start hor (by change 1 ≤ 2; decide) _ _ _ ⟨rfl,rfl,rfl⟩
    exact ⟨d,t,ht,hd,hh,by rwa [hdi],by rwa [hdi],by rwa [hdi],hdw,hdo⟩
  have h := seqTM_hoareTime _ _ (scan_hoare es srcTail witTail inp marker a hi) stable second
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierActivationRow
