module

public import proofs.UnconstrainedPACDetection.FormulaMaximumMachine

@[expose] public section

namespace UnconstrainedPACDetection.FormulaMaximum
open Complexity Complexity.TM

def after (q : ScanState) (k mx : Nat) (inp out : Tape) (b : Bool) : Cfg 1 machine.Q :=
  match action q b with
  | .keep q' => cfg (.scanning q') (inp.move .right) out mx (k+1)
  | .advance => cfg (.scanning (true,none)) (inp.move .right)
      (if (cursor mx k).read = .blank then out.writeAndMove .one .right else out)
      (max mx (k+1)) (k+2)
  | .reset => cfg .rewind (inp.move .right) out mx (k+1)

theorem bit_step (q : ScanState) (k mx : Nat) (inp out : Tape) (b : Bool)
    (hk : k ≤ mx) (hi : inp.read = Γ.ofBool b) (ho : out.read ≠ .start) :
    machine.step (cfg (.scanning q) inp out mx (k+1)) = some (after q k mx inp out b) := by
  have hin : inp.read ≠ .start := by rw [hi]; cases b <;> decide
  have hib : inp.read ≠ .blank := by rw [hi]; cases b <;> decide
  have hb : decide (inp.read = .one) = b := by rw [hi]; cases b <;> rfl
  have hw := cursor_read_ne_start mx k
  cases ha : action q b with
  | keep q' =>
    simp only [TM.step,machine,cfg,reduceCtorEq,↓reduceIte,ite_eq_right hin,ite_eq_right hib,hb,ha,after]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; exact transitionTape_eq_self hw
    · exact transitionTape_eq_self ho
  | advance =>
    simp only [TM.step,machine,cfg,reduceCtorEq,↓reduceIte,ite_eq_right hin,ite_eq_right hib,hb,ha,after]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; exact cursor_advance mx k hk
    · by_cases he : regCells mx (k+1) = .blank
      · simp [he,cursor,Tape.read]
      · have ht := transitionTape_eq_self ho
        unfold transitionTape at ht
        simpa [he,cursor,Tape.read] using ht
  | reset =>
    simp only [TM.step,machine,cfg,reduceCtorEq,↓reduceIte,ite_eq_right hin,ite_eq_right hib,hb,ha,after]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; exact transitionTape_eq_self hw
    · exact transitionTape_eq_self ho

theorem machine_scan (xs : List Bool) (q : ScanState) (k mx : Nat) (inp out : Tape)
    (hk : k ≤ mx) (hi : inp.HasBinarySuffix xs)
    (ho : out.HasBinaryPrefix (List.replicate mx true)) :
    ∃ d, machine.reachesIn (cost q k xs) (cfg (.scanning q) inp out mx (k+1)) d ∧
      machine.halted d ∧ d.output.HasBinaryPrefix (List.replicate (scan q k mx xs) true) := by
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
    exact ⟨d,.step hs .zero,rfl,ho⟩
  | cons b bs ih =>
    have hs := bit_step q k mx inp out b hk hi.read_cons hor
    cases ha : action q b with
    | keep q' =>
      simp only [after,ha] at hs
      obtain ⟨d,hd,hh,hout⟩ := ih q' k mx (inp.move .right) out hk hi.move_right_cons ho hor
      refine ⟨d,?_,hh,?_⟩
      · simpa only [cost,ha,Nat.add_comm] using TM.reachesIn.step hs hd
      · simpa only [scan,ha] using hout
    | advance =>
      simp only [after,ha] at hs
      let out' := if (cursor mx k).read = .blank then out.writeAndMove .one .right else out
      have ho' : out'.HasBinaryPrefix (List.replicate (max mx (k+1)) true) := maximum_output mx k hk out ho
      have hor' : out'.read ≠ .start := by rw [ho'.read_blank]; decide
      obtain ⟨d,hd,hh,hout⟩ := ih (true,none) (k+1) (max mx (k+1))
        (inp.move .right) out' (Nat.le_max_right _ _) hi.move_right_cons ho' hor'
      refine ⟨d,?_,hh,?_⟩
      · simpa only [cost,ha,Nat.add_comm] using TM.reachesIn.step hs hd
      · simpa only [scan,ha] using hout
    | reset =>
      simp only [after,ha] at hs
      have hir : (inp.move .right).read ≠ .start := hi.move_right_cons.read_ne_start
      have hr := rewind_run (k+1) mx (inp.move .right) out hir hor
      obtain ⟨d,hd,hh,hout⟩ := ih (false,none) 0 mx (inp.move .right) out
        (Nat.zero_le _) hi.move_right_cons ho hor
      refine ⟨d,?_,hh,?_⟩
      · have hfirst := TM.reachesIn.step hs hr
        have hall := machine.reachesIn_trans hfirst hd
        convert hall using 1
        simp only [cost,ha]
        omega
      · simpa only [scan,ha] using hout

def maximumBits (xs : List Bool) : List Bool := List.replicate (scan (false,none) 0 0 xs) true

theorem computes : machine.ComputesInTime maximumBits (fun n => 3*n+2) := by
  intro xs
  let inp := (Tape.init (xs.map Γ.ofBool)).move .right
  let out := (Tape.init []).move .right
  have hs : machine.step (machine.initCfg xs) = some (cfg (.scanning (false,none)) inp out 0 1) := by
    simp [TM.step,machine,cfg,inp,out,Tape.read,Tape.init,readBackWrite,idleDir,
      Tape.writeAndMove,Tape.write,Tape.move]
    funext j
    apply Tape.ext
    · rfl
    · funext i
      by_cases hi : i = 0 <;> simp [regCells,hi]
  obtain ⟨d,hd,hh,ho⟩ := machine_scan xs (false,none) 0 0 inp out (by rfl)
    (Tape.init_move_right_hasBinarySuffix xs) (by simpa using Tape.init_nil_move_right_hasBinaryPrefix_nil)
  refine ⟨d,cost (false,none) 0 xs+1,?_,.step hs hd,hh,ho.hasOutput⟩
  change cost (false,none) 0 xs+1 ≤ 3*xs.length+2
  have h := cost_bound (false,none) 0 xs
  omega

theorem maximumBits_mem_FP : maximumBits ∈ FP := by
  refine ⟨1,1,machine,(fun n => 3*n+2),computes,?_⟩
  have hn : (fun n : ℕ => n) =O ((· ^ 1) : ℕ → ℕ) := by
    simpa only [pow_one] using BigO.refl (fun n : ℕ => n)
  have hthree : (fun n : ℕ => 3*n) =O ((· ^ 1) : ℕ → ℕ) := by
    simpa [show ∀ n : Nat, n+n+n = 3*n by intro n; omega] using BigO.add (BigO.add hn hn) hn
  exact BigO.add hthree (BigO.const_le_pow 2 1)

theorem decoded_output (xs : List Bool) (φ : SAT.CNF) (h : SAT.CNF.decode? xs = some φ) :
    maximumBits xs = List.replicate φ.maxVar true := by
  rw [maximumBits,decoded_maximum xs φ h]

end UnconstrainedPACDetection.FormulaMaximum
