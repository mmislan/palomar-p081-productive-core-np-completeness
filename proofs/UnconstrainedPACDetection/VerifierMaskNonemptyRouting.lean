module

public import proofs.UnconstrainedPACDetection.VerifierMaskNonempty

@[expose] public section

namespace UnconstrainedPACDetection.VerifierMaskNonemptyRouting
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)

abbrev reader := VerifierMaskNonempty.machine
def buffered : TM 1 := retargetInput reader
def machine : TM 4 := placeWorkTM 0 3 buffered

theorem retarget_run {t : ℕ} {c d : Cfg 0 reader.Q}
    (h : reader.reachesIn t c d) (hi : c.input.StartInvariant)
    (realInput : Tape) (hr : realInput.read ≠ .start) :
    buffered.reachesIn t (retargetWrap reader realInput c) (retargetWrap reader realInput d) := by
  have hidle : realInput.move (idleDir realInput.read) = realInput := by simp [idleDir,hr,Tape.move]
  induction h with
  | zero => exact .zero
  | step hs _ ih =>
    have hc := input_cells_eq_of_step hs
    have hi' : _ := And.intro (hc ▸ hi.1) (fun j hj => hc ▸ hi.2 j hj)
    have step := retargetInput_step_commute reader hs realInput hi
    rw [hidle] at step
    exact .step step (ih hi')

def embed (frame : Fin 4 → Tape) (inp : Tape) (c : Cfg 0 reader.Q) : Cfg 4 machine.Q :=
  placeWorkCfg buffered 0 3 frame (retargetWrap reader inp c)

theorem embed_witness (frame : Fin 4 → Tape) (inp : Tape) (c : Cfg 0 reader.Q) :
    (embed frame inp c).work 0 = c.input := rfl

theorem embed_other (frame : Fin 4 → Tape) (inp : Tape) (c : Cfg 0 reader.Q)
    (j : Fin 4) (h0 : j ≠ 0) : (embed frame inp c).work j = frame j := by
  fin_cases j <;> first | exact (h0 rfl).elim | rfl

theorem check_hoare (w : BinaryWitnessData.Witness) (frame : Fin 4 → Tape) (inp₀ : Tape) (a : Bool)
    (h0 : frame 0 = wordTape w.encode) (hf : ∀ j, (frame j).read ≠ .start)
    (hi : inp₀.read ≠ .start) :
    machine.HoareTime (VerifierTapeCleanup.frame frame inp₀ (one .start a))
      (fun inp work out => inp = inp₀ ∧
        work 0 = VerifierFlowRestart.flowInput w.mask (VerifierFlowBothSource.flowWire w) ∧
        (∀ j, j ≠ 0 → work j = frame j) ∧ out = one .start (a && w.mask.any id))
      (2*w.mask.length+2) := by
  rintro inp work out ⟨hin,hwork,hout⟩
  subst inp; subst work; subst out
  let c : Cfg 0 reader.Q := ⟨reader.qstart,wordTape w.encode,fun j => Fin.elim0 j,one .start a⟩
  obtain ⟨d,hd,hh,_,hdh,hdc,hdo⟩ := VerifierMaskNonempty.run w.mask (VerifierFlowBothSource.flowWire w)
    c .start a rfl (Tape.init_move_right_hasBinaryString _).hasBinarySuffix rfl
  have hret := retarget_run hd ((Tape.StartInvariant.init_ofBool w.encode).move .right) inp₀ hi
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal buffered 0 3 frame hret
    (by intro j _; exact hf j)
  have he : embed frame inp₀ c = (⟨machine.qstart,inp₀,frame,one .start a⟩ : Cfg 4 machine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      change (embed frame inp₀ c).work j = frame j
      by_cases hj : j = 0
      · subst j; rw [embed_witness,h0]
      · exact embed_other frame inp₀ c j hj
    · rfl
  refine ⟨embed frame inp₀ d,_,le_rfl,?_,hh,rfl,?_,?_,hdo⟩
  · change machine.reachesIn _ (embed frame inp₀ c) (embed frame inp₀ d) at hp
    simpa only [he] using hp
  · rw [embed_witness]
    apply Tape.ext
    · change d.input.head = 2*w.mask.length+2
      change d.input.head = 1+2*w.mask.length+1 at hdh
      omega
    · exact hdc
  · intro j hj; exact embed_other frame inp₀ d j hj

theorem selected_iff (w : BinaryWitnessData.Witness) (m : ℕ) (hm : w.mask.length = m) :
    w.mask.any id = true ↔ (w.entities m).Nonempty := by
  constructor
  · intro h
    obtain ⟨b,hb,hbt⟩ := List.any_eq_true.mp h
    have ht : b = true := hbt
    subst b
    obtain ⟨i,hi,hval⟩ := List.mem_iff_getElem.mp hb
    refine ⟨⟨i,by omega⟩,?_⟩
    simp only [BinaryWitnessData.Witness.entities,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [List.getD_eq_getElem w.mask false hi]
    exact hval
  · rintro ⟨i,hi⟩
    have hit : i.val < w.mask.length := by omega
    have hv : w.mask[i.val] = true := by
      simp only [BinaryWitnessData.Witness.entities,Finset.mem_filter,Finset.mem_univ,true_and] at hi
      rw [List.getD_eq_getElem w.mask false hit] at hi
      exact hi
    exact List.any_eq_true.mpr ⟨true,List.mem_iff_getElem.mpr ⟨i.val,hit,hv⟩,rfl⟩

end UnconstrainedPACDetection.VerifierMaskNonemptyRouting
