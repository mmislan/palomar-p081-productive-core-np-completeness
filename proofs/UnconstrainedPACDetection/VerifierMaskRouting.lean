module

public import proofs.UnconstrainedPACDetection.VerifierTapePermutation
public import proofs.UnconstrainedPACDetection.VerifierOutputRouting
public import proofs.UnconstrainedPACDetection.VerifierSignedWitnessField

@[expose] public section

namespace UnconstrainedPACDetection.VerifierMaskRouting
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierIndexedField (counter)

abbrev reader := VerifierMaskAccess.machine
def buffered : TM 2 := retargetInput reader
def routed : TM 3 := buffered.retargetOutput
def placed : TM 13 := placeWorkTM 0 10 routed
def permutation : Equiv.Perm (Fin 13) :=
  (Equiv.swap 0 12).trans ((Equiv.swap 1 4).trans (Equiv.swap 2 11))
def machine : TM 13 := VerifierTapePermutation.machine placed permutation

theorem retarget_run {t : ℕ} {c d : Cfg 1 reader.Q}
    (h : reader.reachesIn t c d) (hi : c.input.StartInvariant)
    (realInput : Tape) (hr : realInput.read ≠ .start) :
    buffered.reachesIn t (retargetWrap reader realInput c) (retargetWrap reader realInput d) := by
  have hidle : realInput.move (idleDir realInput.read) = realInput := by
    simp [idleDir,hr,Tape.move]
  induction h with
  | zero => exact .zero
  | step hs _ ih =>
    have hc := input_cells_eq_of_step hs
    have hi' : _ := And.intro (hc ▸ hi.1) (fun j hj => hc ▸ hi.2 j hj)
    have step := retargetInput_step_commute reader hs realInput hi
    rw [hidle] at step
    exact .step step (ih hi')

def embed (frame : Fin 13 → Tape) (inp out : Tape) (c : Cfg 1 reader.Q) : Cfg 13 machine.Q :=
  VerifierTapePermutation.wrap placed permutation
    (placeWorkCfg routed 0 10 (fun j => frame (permutation j))
      (VerifierOutputRouting.wrap buffered out (retargetWrap reader inp c)))

theorem embed_index (frame : Fin 13 → Tape) (inp out : Tape) (c : Cfg 1 reader.Q) :
    (embed frame inp out c).work 12 = c.work 0 := by
  simp [embed,VerifierTapePermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
    VerifierOutputRouting.wrap,retargetCfg,retargetWrap,permutation,Equiv.swap_apply_def]

theorem embed_witness (frame : Fin 13 → Tape) (inp out : Tape) (c : Cfg 1 reader.Q) :
    (embed frame inp out c).work 4 = c.input := by
  simp [embed,VerifierTapePermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
    VerifierOutputRouting.wrap,retargetCfg,retargetWrap,permutation,Equiv.swap_apply_def]

theorem embed_scratch (frame : Fin 13 → Tape) (inp out : Tape) (c : Cfg 1 reader.Q) :
    (embed frame inp out c).work 11 = c.output := by
  simp [embed,VerifierTapePermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
    VerifierOutputRouting.wrap,retargetCfg,retargetWrap,permutation,Equiv.swap_apply_def]

theorem embed_other (frame : Fin 13 → Tape) (inp out : Tape) (c : Cfg 1 reader.Q)
    (j : Fin 13) (h4 : j ≠ 4) (h11 : j ≠ 11) (h12 : j ≠ 12) :
    (embed frame inp out c).work j = frame j := by
  fin_cases j <;> first
    | exact (h4 rfl).elim
    | exact (h11 rfl).elim
    | exact (h12 rfl).elim
    | rfl

/-- Witness on tape4, entity index on tape12, result on scratch11.
The source, cumulative verdict, and all other tapes are exact frames. -/
theorem read_hoare (w : BinaryWitnessData.Witness) (x : ℕ) (hx : x < w.mask.length)
    (frame : Fin 13 → Tape) (inp₀ out₀ : Tape)
    (h4 : frame 4 = wordTape w.encode) (h11 : frame 11 = wordTape [])
    (h12 : frame 12 = counter (2+x)) (hf : ∀ j, (frame j).read ≠ .start)
    (hi : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) :
    machine.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = frame ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ (∀ j, j ≠ 11 → work j = frame j) ∧
        (work 11).HasBinaryPrefix [w.mask.getD x false] ∧ (work 11).cells 0 = .start ∧ out = out₀)
      (5*x+15) := by
  rintro inp work out ⟨rfl,hwork,rfl⟩
  subst work
  let c : Cfg 1 reader.Q := ⟨reader.qstart,wordTape w.encode,fun _ => counter (2+x),wordTape []⟩
  obtain ⟨d,t,ht,hd,hh,hdin,hdw,hdo⟩ := VerifierMaskAccess.witness_hoare w x hx []
    c.input c.work c.output ⟨rfl,rfl,Tape.init_nil_move_right_hasBinaryPrefix_nil⟩
  have hret := retarget_run hd ((Tape.StartInvariant.init_ofBool w.encode).move .right) inp hi
  have hout := VerifierOutputRouting.run_frame buffered out ho hret
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal routed 0 10
    (fun j => frame (permutation j)) hout (by intro j _; exact hf _)
  have hperm := VerifierTapePermutation.run placed permutation hp
  have he : embed frame inp out c = (⟨machine.qstart,inp,frame,out⟩ : Cfg 13 machine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      change (embed frame inp out c).work j = frame j
      by_cases hj4 : j = 4
      · subst j; rw [embed_witness,h4]
      by_cases hj11 : j = 11
      · subst j; rw [embed_scratch,h11]
      by_cases hj12 : j = 12
      · subst j; rw [embed_index,h12]
      exact embed_other frame inp out c j hj4 hj11 hj12
    · rfl
  refine ⟨embed frame inp out d,t,ht,?_,hh,rfl,?_,?_,?_,rfl⟩
  · change machine.reachesIn t (embed frame inp out c) (embed frame inp out d) at hperm
    simpa only [he] using hperm
  · intro j hj
    by_cases hj4 : j = 4
    · subst j; rw [embed_witness,hdin,h4]
    by_cases hj12 : j = 12
    · subst j; rw [embed_index,hdw,h12]
    exact embed_other frame inp out d j hj4 hj hj12
  · rw [embed_scratch]; exact hdo
  · rw [embed_scratch]
    exact output_cells_zero_eq_start_of_reachesIn hd rfl

end UnconstrainedPACDetection.VerifierMaskRouting
