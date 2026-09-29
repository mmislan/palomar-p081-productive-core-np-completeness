module

public import proofs.UnconstrainedPACDetection.FormulaMaximum
public import proofs.Complexitylib.Models.TuringMachine.Registers

@[expose] public section

namespace UnconstrainedPACDetection.FormulaMaximum
open Complexity Complexity.TM

def cursor (mx k : Nat) : Tape := ⟨k+1,regCells mx⟩

theorem cursor_read (mx k : Nat) :
    (cursor mx k).read = if k < mx then Γ.one else Γ.blank := by
  have h : k+1 ≤ mx ↔ k < mx := by omega
  simp [cursor,Tape.read,regCells,h]

theorem write_back (t : Tape) (h : t.read ≠ .start) :
    t.write (readBackWrite t.read).toΓ = t := by
  simpa [transitionTape,idleDir,h,Tape.move] using transitionTape_eq_self h

theorem cursor_read_ne_start (mx k : Nat) : (cursor mx k).read ≠ .start := by
  rw [cursor_read]
  split <;> decide

theorem cursor_advance (mx k : Nat) (hk : k ≤ mx) :
    (cursor mx k).writeAndMove .one .right = cursor (max mx (k+1)) (k+1) := by
  by_cases he : k = mx
  · subst k
    simp [cursor,Tape.writeAndMove,Tape.write,Tape.move,regCells_update_succ]
  · have hlt : k+1 ≤ mx := by omega
    have hr : regCells mx (k+1) = Γ.one := regCells_one (by omega) hlt
    have hu : Function.update (regCells mx) (k+1) Γ.one = regCells mx := by
      rw [← hr,Function.update_eq_self]
    simp [cursor,Tape.writeAndMove,Tape.write,Tape.move,hu,max_eq_left hlt]

theorem maximum_output (mx k : Nat) (hk : k ≤ mx) (out : Tape)
    (ho : out.HasBinaryPrefix (List.replicate mx true)) :
    (if (cursor mx k).read = .blank then out.writeAndMove .one .right else out).HasBinaryPrefix
      (List.replicate (max mx (k+1)) true) := by
  by_cases he : k = mx
  · subst k
    have h := Tape.hasBinaryPrefix_write_bit true ho
    simpa [cursor_read,List.replicate_add,Γ.ofBool] using h
  · have hlt : k < mx := by omega
    simpa [cursor_read,hlt,max_eq_left (show k+1 ≤ mx by omega)] using ho

end UnconstrainedPACDetection.FormulaMaximum
