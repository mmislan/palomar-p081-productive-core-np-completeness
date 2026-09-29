module

public import proofs.UnconstrainedPACDetection.VerifierPairParser

@[expose] public section

namespace UnconstrainedPACDetection.VerifierPairParser
open Complexity Complexity.TM

theorem reject_at (q : Phase) (hq : q ≠ 4) (inp a b out : Tape)
    (ha : Parked a) (hb : Parked b) (ho : OutAcc [] out)
    (hr : rule q inp.read = (4,none,some false,false)) :
    ∃ d, machine.reachesIn 1 (config q inp a b out) d ∧ machine.halted d ∧
      OutAcc [false] d.output := by
  have hs := step_rule q hq inp a b out ha hb ho.parked 4 none (some false) false hr
  exact ⟨_,.step hs .zero,rfl,outAcc_append_bit ho false⟩

theorem malformed (xs : List Bool) : ∀ (inp a b out : Tape),
    unpair? xs = none → inp.HasBinarySuffix xs → Parked a → Parked b → OutAcc [] out →
    ∃ d t, t ≤ xs.length+1 ∧ machine.reachesIn t (config 0 inp a b out) d ∧
      machine.halted d ∧ OutAcc [false] d.output := by
  induction xs using List.twoStepInduction with
  | nil =>
    intro inp a b out _ hi ha hb ho
    obtain ⟨d,hd,hh,hout⟩ := reject_at 0 (by decide) inp a b out ha hb ho
      (by rw [hi.read_nil]; rfl)
    exact ⟨d,1,by simp,hd,hh,hout⟩
  | singleton bit =>
    intro inp a b out _ hi ha hb ho
    have hs := step_rule 0 (by decide) inp a b out ha hb ho.parked
      (if bit then 2 else 1) none none true (by rw [hi.read_cons]; cases bit <;> rfl)
    obtain ⟨d,hd,hh,hout⟩ := reject_at (if bit then 2 else 1)
      (by cases bit <;> decide) (inp.move .right) a b out ha hb ho
      (by rw [hi.move_right_cons.read_nil]; cases bit <;> rfl)
    exact ⟨d,2,by simp,.step hs hd,hh,hout⟩
  | cons_cons first second rest ih _ =>
    intro inp a b out hn hi ha hb ho
    by_cases heq : first = second
    · subst second
      have hrest : unpair? rest = none := by
        cases first <;> simpa [unpair?] using hn
      have hs := token first rest inp a b out hi ha hb ho.parked
      have ha' : Parked (a.writeAndMove (Γ.ofBool first) .right) := by
        refine ⟨by simp [Tape.writeAndMove,Tape.move],?_⟩
        intro j hj
        simp only [Tape.writeAndMove,Tape.move_cells,Tape.write]
        split
        · exact ha.2 j hj
        · by_cases hja : j = a.head
          · subst j; simp; cases first <;> decide
          · simp only [Function.update_of_ne hja]; exact ha.2 j hj
      obtain ⟨d,t,ht,hd,hh,hout⟩ := ih ((inp.move .right).move .right)
        (a.writeAndMove (Γ.ofBool first) .right) b out hrest
        hi.move_right_cons.move_right_cons ha' hb ho
      exact ⟨d,2+t,by simp only [List.length_cons]; omega,machine.reachesIn_trans hs hd,hh,hout⟩
    · cases first <;> cases second
      · contradiction
      · simp [unpair?] at hn
      · have hs := step_rule 0 (by decide) inp a b out ha hb ho.parked
          2 none none true (by rw [hi.read_cons]; rfl)
        obtain ⟨d,hd,hh,hout⟩ := reject_at 2 (by decide) (inp.move .right) a b out ha hb ho
          (by rw [hi.move_right_cons.read_cons]; rfl)
        exact ⟨d,2,by simp,.step hs hd,hh,hout⟩
      · contradiction

end UnconstrainedPACDetection.VerifierPairParser
