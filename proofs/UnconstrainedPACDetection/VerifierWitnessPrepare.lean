module

public import proofs.UnconstrainedPACDetection.VerifierWitnessGrammar

@[expose] public section

namespace UnconstrainedPACDetection.VerifierWitnessPrepare
open Complexity Complexity.TM
open VerifierWitnessGrammar (Phase next accept run)
open VerifierAccumulate (markerDir)
open VerifierBufferedProduct (wordTape)

def emitted (q : Phase) (b : Bool) (j : Fin 2) : Bool :=
  if j = 0 then (next q b).2.1 else (next q b).2.2

def machine : TM 2 where
  Q := Phase
  qstart := .maskMarker
  qhalt := .done
  δ := fun q i w o =>
    if i = .blank then
      (.done,fun j => readBackWrite (w j),readBackWrite (Γ.ofBool (accept q)),
        markerDir i .stay,fun j => idleDir (w j),.right)
    else
      ((next q (decide (i = .one))).1,
        fun j => if emitted q (decide (i = .one)) j then .one else readBackWrite (w j),
        readBackWrite o,.right,
        fun j => if emitted q (decide (i = .one)) j then .right else idleDir (w j),idleDir o)
  δ_right_of_start := by
    intro q i w o
    dsimp only
    split
    · exact ⟨fun h => by simp [markerDir,h],fun _ => idleDir_right_of_start,fun _ => rfl⟩
    · refine ⟨fun _ => rfl,?_,idleDir_right_of_start⟩
      intro j h
      dsimp only
      split
      · rfl
      · exact idleDir_right_of_start h

def emit (t : Tape) (b : Bool) : Tape := if b then t.writeAndMove .one .right else t

theorem emit_prefix (t : Tape) (xs : List Bool) (b : Bool) (h : t.HasBinaryPrefix xs) :
    (emit t b).HasBinaryPrefix (xs ++ List.replicate (if b then 1 else 0) true) := by
  cases b
  · simpa [emit] using h
  · simpa [emit,Γ.ofBool] using Tape.hasBinaryPrefix_write_bit true h

def tick (c : Cfg 2 Phase) (b : Bool) : Cfg 2 Phase :=
  ⟨(next c.state b).1,c.input.move .right,fun j => emit (c.work j) (emitted c.state b j),c.output⟩

theorem tick_step (c : Cfg 2 Phase) (b : Bool) (hn : c.state ≠ .done)
    (hi : c.input.read = Γ.ofBool b) (hw : ∀ j, (c.work j).read ≠ .start)
    (ho : c.output.read ≠ .start) : machine.step c = some (tick c b) := by
  have hib : c.input.read ≠ .blank := by rw [hi]; cases b <;> decide
  have he : decide (c.input.read = .one) = b := by rw [hi]; cases b <;> rfl
  simp only [TM.step,machine,hn,↓reduceIte,ite_eq_right hib,he]
  congr 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    dsimp only [tick,emit]
    split
    · rfl
    · exact transitionTape_eq_self (hw j)
  · exact transitionTape_eq_self ho

theorem next_live (q : Phase) (b : Bool) (h : q ≠ .done) : (next q b).1 ≠ .done := by
  cases q <;> cases b <;> simp_all [next]
  split <;> decide

/-- All raw bit strings, including malformed ones, halt after exactly one
transition per bit and a final blank transition. -/
theorem scan_run (bits : List Bool) (c : Cfg 2 Phase) (xs ys : List Bool)
    (hn : c.state ≠ .done) (hi : c.input.HasBinarySuffix bits)
    (h0 : (c.work 0).HasBinaryPrefix xs) (h1 : (c.work 1).HasBinaryPrefix ys)
    (ho : c.output.HasBinaryPrefix []) :
    ∃ d, machine.reachesIn (bits.length+1) c d ∧ machine.halted d ∧
      d.input.HasBinarySuffix [] ∧ d.input.head = c.input.head+bits.length ∧
      (d.work 0).HasBinaryPrefix (xs++List.replicate (run c.state bits).2.1 true) ∧
      (d.work 1).HasBinaryPrefix (ys++List.replicate (run c.state bits).2.2 true) ∧
      d.output.HasBinaryPrefix [accept (run c.state bits).1] := by
  have hw : ∀ j, (c.work j).read ≠ .start := by
    intro j
    fin_cases j
    · change (c.work 0).read ≠ .start
      rw [h0.read_blank]; decide
    · change (c.work 1).read ≠ .start
      rw [h1.read_blank]; decide
  have hor : c.output.read ≠ .start := by rw [ho.read_blank]; decide
  induction bits generalizing c xs ys with
  | nil =>
    let d : Cfg 2 Phase := ⟨.done,c.input,c.work,
      c.output.writeAndMove (Γ.ofBool (accept c.state)) .right⟩
    have hs : machine.step c = some d := by
      simp only [TM.step,machine,hn,↓reduceIte,hi.read_nil,markerDir]
      simp only [reduceCtorEq,↓reduceIte]
      congr 1
      apply Cfg.ext
      · rfl
      · rfl
      · funext j; exact transitionTape_eq_self (hw j)
      · dsimp only [d]
        cases h : accept c.state <;> rfl
    exact ⟨d,.step hs .zero,rfl,hi,by simp [d],by simpa [d,run] using h0,
      by simpa [d,run] using h1,by simpa [d,run] using Tape.hasBinaryPrefix_write_bit (accept c.state) ho⟩
  | cons b bs ih =>
    have hs := tick_step c b hn hi.read_cons hw hor
    let mid := tick c b
    have hm0 : (mid.work 0).HasBinaryPrefix
        (xs++List.replicate (if (next c.state b).2.1 then 1 else 0) true) :=
      emit_prefix _ _ _ h0
    have hm1 : (mid.work 1).HasBinaryPrefix
        (ys++List.replicate (if (next c.state b).2.2 then 1 else 0) true) := by
      simpa [mid,tick,emitted] using emit_prefix (c.work 1) ys ((next c.state b).2.2) h1
    obtain ⟨d,hd,hh,hdi,hdh,hd0,hd1,hdo⟩ := ih mid _ _ (next_live _ _ hn)
      hi.move_right_cons hm0 hm1 ho
      (by
        intro j
        fin_cases j
        · change (mid.work 0).read ≠ .start; rw [hm0.read_blank]; decide
        · change (mid.work 1).read ≠ .start; rw [hm1.read_blank]; decide) hor
    refine ⟨d,?_,hh,hdi,?_,?_,?_,?_⟩
    · convert TM.reachesIn.step hs hd using 1
    · dsimp only [mid,tick,Tape.move] at hdh
      simp only [List.length_cons]
      omega
    · change (d.work 0).HasBinaryPrefix (xs++List.replicate
        ((if (next c.state b).2.1 then 1 else 0)+(run (next c.state b).1 bs).2.1) true)
      rw [List.replicate_add,← List.append_assoc]
      exact hd0
    · change (d.work 1).HasBinaryPrefix (ys++List.replicate
        ((if (next c.state b).2.2 then 1 else 0)+(run (next c.state b).1 bs).2.2) true)
      rw [List.replicate_add,← List.append_assoc]
      exact hd1
    · exact hdo

theorem raw_hoare (bits : List Bool) : machine.HoareTime
    (fun inp work out => inp.HasBinarySuffix bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (fun inp work out => inp.HasBinarySuffix [] ∧
      (work 0).HasBinaryPrefix (List.replicate (run .maskMarker bits).2.1 true) ∧
      (work 1).HasBinaryPrefix (List.replicate (run .maskMarker bits).2.2 true) ∧
      out.HasBinaryPrefix [accept (run .maskMarker bits).1]) (bits.length+1) := by
  rintro inp work out ⟨hi,hwork,hout⟩
  subst work; subst out
  have he := VerifierEntityLoopBody.prefix_of_acc [] (wordTape []) outAcc_nil_init
  obtain ⟨d,hd,hh,hdi,_,hd0,hd1,hdo⟩ := scan_run bits
    ⟨.maskMarker,inp,fun _ => wordTape [],wordTape []⟩ [] []
    (by change Phase.maskMarker ≠ Phase.done; decide) hi he he he
  exact ⟨d,bits.length+1,le_rfl,hd,hh,hdi,by simpa using hd0,by simpa using hd1,hdo⟩

/-- Canonical witnesses are accepted and emit their exact dimensions. Rewinding
these unary prefixes, source-header comparison, and converse grammar soundness
are separate raw-initialization obligations. -/
theorem witness_hoare (w : BinaryWitnessData.Witness) : machine.HoareTime
    (fun inp work out => inp.HasBinarySuffix w.encode ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (fun inp work out => inp.HasBinarySuffix [] ∧
      (work 0).HasBinaryPrefix (List.replicate w.mask.length true) ∧
      (work 1).HasBinaryPrefix (List.replicate w.flow.length true) ∧ out.HasBinaryPrefix [true])
    (w.encode.length+1) := by
  simpa only [VerifierWitnessGrammar.witness_run,accept,decide_true] using raw_hoare w.encode

end UnconstrainedPACDetection.VerifierWitnessPrepare
