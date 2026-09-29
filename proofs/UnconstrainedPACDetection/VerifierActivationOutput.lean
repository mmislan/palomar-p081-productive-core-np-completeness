module

public import proofs.UnconstrainedPACDetection.VerifierActivationEmit

@[expose] public section

namespace UnconstrainedPACDetection.VerifierActivationOutput
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one empty)
open VerifierActivationScan (flag)

def pair (wt scratch : Tape) : Fin 2 → Tape := fun j => if j = 0 then wt else scratch

theorem placed_eq (tm : TM 1) (q : tm.Q) (inp wt baseScratch scratch out : Tape) :
    placeWorkCfg tm 1 0 (pair wt baseScratch) ⟨q,inp,fun _ => scratch,out⟩ =
      ⟨q,inp,pair wt scratch,out⟩ := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext j; fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,pair]
  · rfl

theorem placed_run (tm : TM 1) (wt : Tape) (hw : wt.read ≠ .start)
    (q q' : tm.Q) (inp inp' scratch scratch' out out' : Tape) (t : ℕ)
    (h : tm.reachesIn t ⟨q,inp,fun _ => scratch,out⟩ ⟨q',inp',fun _ => scratch',out'⟩) :
    (placeWorkTM 1 0 tm).reachesIn t ⟨q,inp,pair wt scratch,out⟩
      ⟨q',inp',pair wt scratch',out'⟩ := by
  have hr := placeWorkTM_reachesIn_placeWorkCfg_stable_internal tm 1 0 (pair wt scratch) h (by
    intro j hj
    fin_cases j
    · exact hw
    · simp [placeWorkInMiddle] at hj)
  simpa only [placed_eq] using hr

def fixed (inp wt scratch out₀ : Tape) : Complexity.TM.TapePred 2 :=
  fun i w o => i = inp ∧ w = pair wt scratch ∧ o = out₀

def after (tail : List Bool) (orig wt scratch out₀ : Tape) (n : ℕ) : Complexity.TM.TapePred 2 :=
  fun i w o => i.HasBinarySuffix tail ∧ i.head = orig.head+n ∧ i.cells = orig.cells ∧
    w = pair wt scratch ∧ o = out₀

theorem seed_hoare (inp wt out : Tape) (hi : inp.read ≠ .start)
    (hw : wt.read ≠ .start) (ho : out.read ≠ .start) :
    (placeWorkTM 1 0 VerifierActivationEmit.seed).HoareTime
      (fixed inp wt (empty .start) out) (fixed inp wt (flag .start false) out) 1 := by
  rintro i w o ⟨hin,hwork,hout⟩
  subst i; subst w; subst o
  exact ⟨_,1,le_rfl,placed_run _ wt hw _ _ _ _ _ _ _ _ 1
    (VerifierActivationEmit.seed_run inp out hi ho .start),rfl,rfl,rfl,rfl⟩

theorem emit_hoare (inp wt out : Tape) (hi : inp.read ≠ .start)
    (hw : wt.read ≠ .start) (ho : out.read ≠ .start) (v : Bool) :
    (placeWorkTM 1 0 VerifierActivationEmit.machine).HoareTime
      (fixed inp wt (one .start v) out)
      (fixed inp wt (empty .start) (out.writeAndMove (Γ.ofBool v) .right)) 2 := by
  rintro i w o ⟨hin,hwork,hout⟩
  subst i; subst w; subst o
  exact ⟨_,2,le_rfl,placed_run _ wt hw _ _ _ _ _ _ _ _ 2
    (VerifierActivationEmit.run inp out hi ho .start v),rfl,rfl,rfl,rfl⟩

theorem scan_hoare (es : List (List Bool × Bool)) (srcTail witTail : List Bool)
    (inp out : Tape) (hi : inp.HasBinarySuffix (BinaryFields.encode (es.map Prod.fst) ++ srcTail))
    (ho : out.read ≠ .start) :
    VerifierActivationRow.machine.retargetOutput.HoareTime
      (fixed inp (wordTape (BinaryFields.encodeField (es.map Prod.snd) ++ witTail)) (flag .start false) out)
      (after srcTail inp (wordTape (BinaryFields.encodeField (es.map Prod.snd) ++ witTail))
        (one .start (VerifierActivationSide.hit es false)) out (BinaryFields.encode (es.map Prod.fst)).length)
      ((BinaryFields.encode (es.map Prod.fst)).length+4*es.length+5) := by
  rintro i w o ⟨hin,hwork,hout⟩
  subst i; subst w; subst o
  obtain ⟨d,t,ht,hd,hh,hdi,hdh,hdc,hdw,hdo⟩ := VerifierActivationRow.row_hoare es srcTail witTail inp .start false hi
    _ _ _ ⟨rfl,rfl,rfl⟩
  have hr := VerifierOutputRouting.run_frame _ out ho hd
  refine ⟨VerifierOutputRouting.wrap _ out d,t,ht,?_,hh,hdi,hdh,hdc,?_,rfl⟩
  · unfold retargetOutput at hr ⊢
    convert hr using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  · funext j
    fin_cases j <;> simp [VerifierOutputRouting.wrap,TM.retargetCfg,pair,hdw,hdo]

theorem pair_off (wt scratch : Tape) (hw : wt.read ≠ .start) (hs : scratch.read ≠ .start) :
    ∀ j, (pair wt scratch j).read ≠ .start := by
  intro j; fin_cases j <;> assumption

theorem fixed_stable (inp wt scratch out : Tape) (hi : inp.read ≠ .start)
    (hw : wt.read ≠ .start) (hs : scratch.read ≠ .start) (ho : out.read ≠ .start) :
    ∀ i w o, fixed inp wt scratch out i w o →
      fixed inp wt scratch out (transitionInput i) (fun j => transitionTape (w j)) (transitionTape o) := by
  rintro i w o ⟨hin,hwork,hout⟩
  subst i; subst w; subst o
  exact phaseTransition_eq_self_of_reads_ne_start hi (pair_off wt scratch hw hs) ho

theorem after_stable (tail : List Bool) (orig wt scratch out : Tape) (n : ℕ)
    (hw : wt.read ≠ .start) (hs : scratch.read ≠ .start) (ho : out.read ≠ .start) :
    ∀ i w o, after tail orig wt scratch out n i w o →
      after tail orig wt scratch out n (transitionInput i) (fun j => transitionTape (w j)) (transitionTape o) := by
  rintro i w o ⟨hi,hh,hc,hwork,hout⟩
  subst w; subst o
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start
    (pair_off wt scratch hw hs) ho
  exact ⟨by rwa [hi'],by rwa [hi'],by rwa [hi'],hw',ho'⟩

def machine : TM 2 := seqTM (placeWorkTM 1 0 VerifierActivationEmit.seed)
  (seqTM VerifierActivationRow.machine.retargetOutput (placeWorkTM 1 0 VerifierActivationEmit.machine))

theorem row_output_hoare (es : List (List Bool × Bool)) (srcTail witTail : List Bool)
    (inp out : Tape) (hi : inp.HasBinarySuffix (BinaryFields.encode (es.map Prod.fst) ++ srcTail))
    (ho : out.read ≠ .start) :
    machine.HoareTime
      (fixed inp (wordTape (BinaryFields.encodeField (es.map Prod.snd) ++ witTail)) (empty .start) out)
      (after srcTail inp (wordTape (BinaryFields.encodeField (es.map Prod.snd) ++ witTail))
        (empty .start) (out.writeAndMove (Γ.ofBool (VerifierActivationSide.hit es false)) .right)
        (BinaryFields.encode (es.map Prod.fst)).length)
      ((BinaryFields.encode (es.map Prod.fst)).length+4*es.length+10) := by
  let wt := wordTape (BinaryFields.encodeField (es.map Prod.snd) ++ witTail)
  let v := VerifierActivationSide.hit es false
  let n := (BinaryFields.encode (es.map Prod.fst)).length
  have hw : wt.read ≠ .start := (Tape.init_move_right_hasBinaryString _).hasBinarySuffix.read_ne_start
  have hs : (one .start v).read ≠ .start := by change Γ.blank ≠ Γ.start; decide
  have hf : (flag .start false).read ≠ .start := by change Γ.zero ≠ Γ.start; decide
  have last : (placeWorkTM 1 0 VerifierActivationEmit.machine).HoareTime
      (after srcTail inp wt (one .start v) out n)
      (after srcTail inp wt (empty .start) (out.writeAndMove (Γ.ofBool v) .right) n) 2 := by
    rintro i w o ⟨his,hih,hic,hwork,hout⟩
    subst w; subst o
    obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := emit_hoare i wt out his.read_ne_start hw ho v
      _ _ _ ⟨rfl,rfl,rfl⟩
    exact ⟨d,t,ht,hd,hh,by rwa [hdi],by rwa [hdi],by rwa [hdi],hdw,hdo⟩
  have tail := seqTM_hoareTime _ _ (scan_hoare es srcTail witTail inp out hi ho)
    (after_stable srcTail inp wt (one .start v) out n hw hs ho) last
  have h := seqTM_hoareTime _ _ (seed_hoare inp wt out hi.read_ne_start hw ho)
    (fixed_stable inp wt (flag .start false) out hi.read_ne_start hw hf ho) tail
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierActivationOutput
