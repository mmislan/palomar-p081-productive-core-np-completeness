module

public import proofs.UnconstrainedPACDetection.FormulaValidWriter
public import proofs.UnconstrainedPACDetection.FormulaReductionInput

@[expose] public section

namespace UnconstrainedPACDetection.FormulaInputSelector
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def machine : TM 0 where
  Q := Fin 9
  qstart := 0
  qhalt := 8
  δ := fun q i w o =>
    if q=0 then (1,fun j => readBackWrite (w j),readBackWrite o,.right,fun j => idleDir (w j),idleDir o) else
    if q=1 then (if i=.one then 2 else 6,fun j => readBackWrite (w j),readBackWrite o,.right,fun j => idleDir (w j),idleDir o) else
    if q=2 then (3,fun j => readBackWrite (w j),readBackWrite o,.right,fun j => idleDir (w j),idleDir o) else
    if q=3 then (4,fun j => readBackWrite (w j),readBackWrite o,.right,fun j => idleDir (w j),idleDir o) else
    if q=4 then (5,fun j => readBackWrite (w j),readBackWrite o,.right,fun j => idleDir (w j),idleDir o) else
    if q=5 then
      if i=.blank then (8,fun j => readBackWrite (w j),readBackWrite o,idleDir i,fun j => idleDir (w j),idleDir o)
      else (5,fun j => readBackWrite (w j),readBackWrite (Γ.ofBool (decide (i=.one))),.right,fun j => idleDir (w j),.right)
    else if q=6 then (7,fun j => readBackWrite (w j),.one,idleDir i,fun j => idleDir (w j),.right)
    else if q=7 then (8,fun j => readBackWrite (w j),.zero,idleDir i,fun j => idleDir (w j),.right)
    else allIdle 8 i w o
  δ_right_of_start := by
    intro q i w o
    fin_cases q <;> cases i <;> cases o <;> norm_num [Fin.ext_iff,idleDir,allIdle]

theorem copy_run (xs ys : List Bool) (inp out : Tape) (hi : inp.HasBinarySuffix xs) (ho : OutAcc ys out) :
    ∃ d, machine.reachesIn (xs.length+1) ⟨(5 : Fin 9),inp,(fun j => Fin.elim0 j),out⟩ d ∧
      machine.halted d ∧ OutAcc (ys ++ xs) d.output := by
  induction xs generalizing inp out ys with
  | nil =>
    refine ⟨⟨(8 : Fin 9),inp,(fun j => Fin.elim0 j),out⟩,.step ?_ .zero,rfl,?_⟩
    · have hr := hi.read_nil
      simp [TM.step,machine,hr]
      exact ⟨rfl,Subsingleton.elim _ _,ho.parked.writeAndMove_readBack_idle⟩
    · simpa using ho
  | cons b xs ih =>
    let nextOut := out.writeAndMove (Γ.ofBool b) .right
    have hs : machine.step ⟨(5 : Fin 9),inp,(fun j => Fin.elim0 j),out⟩ =
        some ⟨(5 : Fin 9),inp.move .right,(fun j => Fin.elim0 j),nextOut⟩ := by
      have hr := hi.read_cons
      cases b <;> simp [TM.step,machine,hr,nextOut,Γ.ofBool,readBackWrite]
      all_goals exact Subsingleton.elim _ _
    obtain ⟨d,hd,hh,hout⟩ := ih (ys ++ [b]) (inp.move .right) nextOut hi.move_right_cons (outAcc_append_bit ho b)
    refine ⟨d,.step hs hd,hh,?_⟩
    simpa only [List.append_assoc,List.singleton_append] using hout

def cfg (src : List Bool) (q : Fin 9) (head : Nat) (out : Tape) : Cfg 0 machine.Q :=
  ⟨q,⟨head,(Tape.init (src.map Γ.ofBool)).cells⟩,(fun j => Fin.elim0 j),out⟩

theorem pair_shape (b : Bool) (xs : List Bool) : pair [b] xs = [b,b,false,true] ++ xs := by
  rw [pair_cons_eq]
  rfl

theorem true_prefix (xs : List Bool) :
    machine.reachesIn 5 (machine.initCfg (pair [true] xs)) (cfg (pair [true] xs) 5 5 (word [])) := by
  refine .step (c'' := cfg (pair [true] xs) 1 1 (word [])) ?_
    (.step (c'' := cfg (pair [true] xs) 2 2 (word [])) ?_
      (.step (c'' := cfg (pair [true] xs) 3 3 (word [])) ?_
        (.step (c'' := cfg (pair [true] xs) 4 4 (word [])) ?_ (.step ?_ .zero))))
  all_goals simp [TM.step,machine,cfg,pair_shape,word,Tape.read,Tape.init,
    Tape.move,Tape.writeAndMove,Tape.write,readBackWrite,idleDir,Γ.ofBool]
  all_goals exact Subsingleton.elim _ _

theorem true_run (xs : List Bool) : ∃ d, machine.reachesIn (xs.length+6)
    (machine.initCfg (pair [true] xs)) d ∧ machine.halted d ∧ d.output.HasOutput xs := by
  have hi := Tape.init_move_right_hasBinarySuffix (pair [true] xs)
  rw [pair_shape] at hi
  have hs := hi.move_right_cons.move_right_cons.move_right_cons.move_right_cons
  have hs' : (cfg (pair [true] xs) 5 5 (word [])).input.HasBinarySuffix xs := by
    simpa [cfg,pair_shape,Tape.move,Tape.init] using hs
  have ho : OutAcc [] (word []) := by
    exact outAcc_nil_init
  obtain ⟨d,hd,hh,hout⟩ := copy_run xs [] _ (word []) hs' ho
  refine ⟨d,?_,hh,?_⟩
  · simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using TM.reachesIn_trans machine (true_prefix xs) hd
  · simpa using hout.hasOutput

theorem false_run (xs : List Bool) : ∃ d, machine.reachesIn 4
    (machine.initCfg (pair [false] xs)) d ∧ machine.halted d ∧ d.output.HasOutput [true,false] := by
  let o1 := (word []).writeAndMove .one .right
  let o2 := o1.writeAndMove .zero .right
  refine ⟨cfg (pair [false] xs) 8 2 o2,?_,rfl,?_⟩
  · refine .step (c'' := cfg (pair [false] xs) 1 1 (word [])) ?_
      (.step (c'' := cfg (pair [false] xs) 6 2 (word [])) ?_
        (.step (c'' := cfg (pair [false] xs) 7 2 o1) ?_ (.step ?_ .zero)))
    all_goals simp [TM.step,machine,cfg,pair_shape,word,Tape.read,Tape.init,
      Tape.move,Tape.writeAndMove,Tape.write,readBackWrite,idleDir,Γ.ofBool,o1,o2]
    all_goals exact Subsingleton.elim _ _
  · have ho : OutAcc [] (word []) := outAcc_nil_init
    exact (outAcc_append_bit (outAcc_append_bit ho true) false).hasOutput

def normalize (xs : List Bool) : List Bool := if (SAT.CNF.decode? xs).isSome then xs else [true,false]

theorem prepared_run (xs : List Bool) : ∃ d t, t≤xs.length+6 ∧
    machine.reachesIn t (machine.initCfg (FormulaReductionInput.prepare xs)) d ∧
    machine.halted d ∧ d.output.HasOutput (normalize xs) := by
  cases hb : (SAT.CNF.decode? xs).isSome with
  | false =>
    obtain ⟨d,hd,hh,ho⟩ := false_run xs
    exact ⟨d,4,by omega,by simpa [FormulaReductionInput.prepare,hb] using hd,hh,by simpa [normalize,hb] using ho⟩
  | true =>
    obtain ⟨d,hd,hh,ho⟩ := true_run xs
    exact ⟨d,xs.length+6,le_rfl,by simpa [FormulaReductionInput.prepare,hb] using hd,hh,by simpa [normalize,hb] using ho⟩

theorem normalized_formula (xs : List Bool) : ∃ φ : SAT.CNF,
    normalize xs=φ.encode ∧ FormulaPACEncoding.compile xs=FormulaPACEncoding.encode φ := by
  cases hd : SAT.CNF.decode? xs with
  | none => exact ⟨[[]],by simp [normalize,hd]; rfl,by simp [FormulaPACEncoding.compile,hd]⟩
  | some φ => exact ⟨φ,by simpa [normalize,hd] using SAT.CNF.decode?_sound hd,by simp [FormulaPACEncoding.compile,hd]⟩

end UnconstrainedPACDetection.FormulaInputSelector
