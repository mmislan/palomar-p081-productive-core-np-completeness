module

public import proofs.UnconstrainedPACDetection.FormulaTokenCount

@[expose] public section

namespace UnconstrainedPACDetection.FormulaTokenCount
open Complexity SAT
open Complexity.TM

def emit (t : Tape) (b : Bool) : Tape := if b then t.writeAndMove .one .right else t

theorem emit_prefix (t : Tape) (xs : List Bool) (b : Bool) (h : t.HasBinaryPrefix xs) :
    (emit t b).HasBinaryPrefix (xs ++ List.replicate (if b then 1 else 0) true) := by
  cases b
  · simpa [emit] using h
  · simpa [emit, Γ.ofBool] using Tape.hasBinaryPrefix_write_bit true h

/-- A fixed finite machine emits one unary mark for each selected separator. -/
def machine (sep : Bool) : TM 0 where
  Q := Option (Option Bool)
  qstart := some none
  qhalt := none
  δ := fun q i w o =>
    match q with
    | none => allIdle none i w o
    | some m =>
      if i = .start then
        (some m,fun j => readBackWrite (w j),readBackWrite o,
          .right,fun j => idleDir (w j),idleDir o)
      else if i = .blank then
        (none,fun j => readBackWrite (w j),readBackWrite o,
          idleDir i,fun j => idleDir (w j),idleDir o)
      else
        (some (next m (decide (i = .one))),fun j => readBackWrite (w j),
          if hit sep m (decide (i = .one)) then .one else readBackWrite o,
          .right,fun j => idleDir (w j),
          if hit sep m (decide (i = .one)) then .right else idleDir o)
  δ_right_of_start := by
    intro q i w o
    cases q with
    | none => exact rightOfStart_allIdle i w o
    | some m =>
      dsimp only
      split
      · exact ⟨fun _ => rfl,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩
      · split
        · exact ⟨fun h => by contradiction,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩
        · refine ⟨fun _ => rfl,fun _ => idleDir_right_of_start,?_⟩
          split
          · exact fun _ => rfl
          · exact idleDir_right_of_start

theorem scan (sep : Bool) (xs : List Bool) :
    ∀ (m : Option Bool) (c : Cfg 0 (machine sep).Q) (out : List Bool),
    c.state = some m → c.input.HasBinarySuffix xs → c.output.HasBinaryPrefix out →
    ∃ d, (machine sep).reachesIn (xs.length+1) c d ∧ (machine sep).halted d ∧
      d.output.HasBinaryPrefix (out ++ List.replicate (run sep m xs) true) := by
  induction xs with
  | nil =>
    intro m c out hs hi ho
    let d : Cfg 0 (machine sep).Q :=
      { state := none,input := c.input,work := (fun j => nomatch j),output := c.output }
    have keep : c.output.writeAndMove (readBackWrite c.output.read).toΓ
        (idleDir c.output.read) = c.output :=
      transitionTape_eq_self (by rw [ho.read_blank]; decide)
    have step : (machine sep).step c = some d := by
      simp [TM.step,machine,hs,hi.read_nil,d,idleDir,Tape.move]
      exact ⟨by funext j; exact Fin.elim0 j,keep⟩
    exact ⟨d,.step step .zero,rfl,by simpa [run,d] using ho⟩
  | cons b xs ih =>
    intro m c out hs hi ho
    let mid : Cfg 0 (machine sep).Q :=
      { state := some (next m b),input := c.input.move .right,
        work := (fun j => nomatch j),output := emit c.output (hit sep m b) }
    have keep : c.output.writeAndMove (readBackWrite c.output.read).toΓ
        (idleDir c.output.read) = c.output :=
      transitionTape_eq_self (by rw [ho.read_blank]; decide)
    have step : (machine sep).step c = some mid := by
      cases he : hit sep m b <;> cases b <;>
        simp [TM.step,machine,hs,hi.read_cons,Γ.ofBool,mid,emit,he]
      all_goals first
        | exact ⟨by funext j; exact Fin.elim0 j,keep⟩
        | (funext j; exact Fin.elim0 j)
    have hm := emit_prefix c.output out (hit sep m b) ho
    obtain ⟨d,hd,hh,hout⟩ := ih (next m b) mid _ rfl hi.move_right_cons hm
    refine ⟨d,.step step hd,hh,?_⟩
    simpa only [run,List.replicate_add,List.append_assoc] using hout

def countBits (sep : Bool) (xs : List Bool) : List Bool := List.replicate (run sep none xs) true

theorem computes (sep : Bool) :
    (machine sep).ComputesInTime (countBits sep) (fun n => n+2) := by
  intro xs
  let c : Cfg 0 (machine sep).Q :=
    { state := some none,input := (Tape.init (xs.map Γ.ofBool)).move .right,
      work := (fun j => nomatch j),output := (Tape.init []).move .right }
  have step : (machine sep).step ((machine sep).initCfg xs) = some c := by
    simp [TM.step,machine,c,Tape.read,Tape.init,readBackWrite,idleDir,
      Tape.writeAndMove,Tape.write,Tape.move]
    funext j; exact Fin.elim0 j
  obtain ⟨d,hd,hh,ho⟩ := scan sep xs none c [] rfl
    (Tape.init_move_right_hasBinarySuffix xs) Tape.init_nil_move_right_hasBinaryPrefix_nil
  exact ⟨d,xs.length+2,le_rfl,.step step hd,hh,by simpa [countBits] using ho.hasOutput⟩

theorem countBits_mem_FP (sep : Bool) : countBits sep ∈ FP := by
  refine ⟨1,0,machine sep,(fun n => n+2),computes sep,?_⟩
  have hn : (fun n : ℕ => n) =O ((· ^ 1) : ℕ → ℕ) := by
    simpa only [pow_one] using BigO.refl (fun n : ℕ => n)
  exact BigO.add hn (BigO.const_le_pow 2 1)

theorem decoded_output (xs : List Bool) (φ : CNF) (h : CNF.decode? xs = some φ) :
    countBits true xs = List.replicate φ.length true ∧
    countBits false xs = List.replicate (FormulaWiring.occurrences φ).length true := by
  have he := CNF.decode?_sound h
  subst xs
  simp [countBits,formula_count,FormulaEnumeration.occurrence_count]

end UnconstrainedPACDetection.FormulaTokenCount
