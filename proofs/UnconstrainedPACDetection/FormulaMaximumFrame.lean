module

public import proofs.UnconstrainedPACDetection.FormulaMaximumExecution
public import proofs.UnconstrainedPACDetection.FormulaLookupFrame

@[expose] public section

namespace UnconstrainedPACDetection.FormulaMaximumFrame
open Complexity Complexity.TM FormulaMaximum
open VerifierPairRestore (word word_parked)

/-- The maximum scan retains the exact unary scratch cells and a bounded live cursor. -/
theorem scan_frame (xs : List Bool) (q : ScanState) (k mx : Nat) (inp out : Tape)
    (hk : k ≤ mx) (hi : inp.HasBinarySuffix xs)
    (ho : out.HasBinaryPrefix (List.replicate mx true)) :
    ∃ d, machine.reachesIn (cost q k xs) (cfg (.scanning q) inp out mx (k+1)) d ∧
      machine.halted d ∧ d.output.HasBinaryPrefix (List.replicate (scan q k mx xs) true) ∧
      ∃ j ≤ scan q k mx xs, d.work = fun _ => cursor (scan q k mx xs) j := by
  have hor : out.read ≠ .start := by rw [ho.read_blank]; decide
  induction xs generalizing q k mx inp out with
  | nil =>
    let d := cfg .done inp out mx (k+1)
    have hs : machine.step (cfg (.scanning q) inp out mx (k+1)) = some d := by
      simp only [TM.step,machine,cfg,reduceCtorEq,↓reduceIte,hi.read_nil]
      congr 1
      apply Cfg.ext
      · rfl
      · simp [d,cfg,idleDir,Tape.move]
      · funext j; exact transitionTape_eq_self (cursor_read_ne_start mx k)
      · exact transitionTape_eq_self hor
    exact ⟨d,.step hs .zero,rfl,ho,k,hk,rfl⟩
  | cons b bs ih =>
    have hs := bit_step q k mx inp out b hk hi.read_cons hor
    cases ha : action q b with
    | keep q' =>
      simp only [after,ha] at hs
      obtain ⟨d,hd,hh,hout,hwork⟩ := ih q' k mx (inp.move .right) out hk hi.move_right_cons ho hor
      refine ⟨d,?_,hh,?_,?_⟩
      · simpa only [cost,ha,Nat.add_comm] using TM.reachesIn.step hs hd
      · simpa only [scan,ha] using hout
      · simpa only [scan,ha] using hwork
    | advance =>
      simp only [after,ha] at hs
      let out' := if (cursor mx k).read = .blank then out.writeAndMove .one .right else out
      have ho' : out'.HasBinaryPrefix (List.replicate (max mx (k+1)) true) := maximum_output mx k hk out ho
      have hor' : out'.read ≠ .start := by rw [ho'.read_blank]; decide
      obtain ⟨d,hd,hh,hout,hwork⟩ := ih (true,none) (k+1) (max mx (k+1))
        (inp.move .right) out' (Nat.le_max_right _ _) hi.move_right_cons ho' hor'
      refine ⟨d,?_,hh,?_,?_⟩
      · simpa only [cost,ha,Nat.add_comm] using TM.reachesIn.step hs hd
      · simpa only [scan,ha] using hout
      · simpa only [scan,ha] using hwork
    | reset =>
      simp only [after,ha] at hs
      have hir : (inp.move .right).read ≠ .start := hi.move_right_cons.read_ne_start
      have hr := rewind_run (k+1) mx (inp.move .right) out hir hor
      obtain ⟨d,hd,hh,hout,hwork⟩ := ih (false,none) 0 mx (inp.move .right) out
        (Nat.zero_le _) hi.move_right_cons ho hor
      refine ⟨d,?_,hh,?_,?_⟩
      · have hall := machine.reachesIn_trans (TM.reachesIn.step hs hr) hd
        convert hall using 1
        simp only [cost,ha]
        omega
      · simpa only [scan,ha] using hout
      · simpa only [scan,ha] using hwork

def value (src : List Bool) : Nat := scan (false,none) 0 0 src

def result (src : List Bool) : Complexity.TM.TapePred 1 := fun inp work out =>
  inp.cells = (word src).cells ∧ inp.StartInvariant ∧ inp.head ≤ 3*src.length+2 ∧
    OutAcc (maximumBits src) out ∧ ∃ j ≤ value src, work = fun _ => cursor (value src) j

theorem scan_hoare (src : List Bool) : machine.HoareTime
    (EmitPred (word src) (fun _ => regTape 0) []) (result src) (3*src.length+1) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  have he : out = word [] := ho.eq outAcc_nil_init
  subst out
  obtain ⟨d,hr,hh,hout,hwork⟩ := scan_frame src (false,none) 0 0 (word src) (word [])
    (by omega) (Tape.init_move_right_hasBinarySuffix src) Tape.init_nil_move_right_hasBinaryPrefix_nil
  obtain ⟨hi,_,ho⟩ := FormulaLookupFrame.start_frame _ hr
    ((Tape.StartInvariant.init_ofBool src).move .right)
    (by intro j; exact ⟨regCells_zero 0,fun i hi => regCells_ne_start hi⟩)
    ((Tape.StartInvariant.init_ofBool []).move .right)
  have hb := (head_le_start_add_of_reachesIn _ hr).1
  have ht := cost_bound (false,none) 0 src
  refine ⟨d,cost (false,none) 0 src,by omega,hr,hh,input_cells_eq_of_reachesIn hr,hi,?_,?_,hwork⟩
  · change d.input.head ≤ 1+cost (false,none) 0 src at hb
    omega
  · exact FormulaLookupFrame.prefix_acc _ _ hout ho.1

theorem result_parked (src : List Bool) {inp : Tape} {work : Fin 1 → Tape} {out : Tape}
    (h : result src inp work out) : ∀ j, Parked (work j) := by
  obtain ⟨_,_,_,_,k,_,hw⟩ := h
  intro j
  rw [hw]
  exact ⟨by simp [cursor],fun i hi => regCells_ne_start hi⟩

theorem result_stable (src : List Bool) : ∀ inp work out,
    result src inp work out → result src (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have hp := result_parked src h
  obtain ⟨hc,hi,hb,ho,hw⟩ := h
  rw [show (fun j => transitionTape (work j)) = work from
    funext (fun j => transitionTape_eq_self (hp j).read_ne_start),
    transitionTape_eq_self ho.parked.read_ne_start]
  refine ⟨(Tape.move_cells _ _).trans hc,hi.move _,?_,ho,hw⟩
  by_cases hr : inp.read = Γ.start
  · have hz : inp.head = 0 := by
      by_contra hn
      exact hi.read_ne_start (by omega) hr
    simp [transitionInput,idleDir,hr,Tape.move,hz]
  · simpa [transitionInput,idleDir,hr,Tape.move] using hb

end UnconstrainedPACDetection.FormulaMaximumFrame
