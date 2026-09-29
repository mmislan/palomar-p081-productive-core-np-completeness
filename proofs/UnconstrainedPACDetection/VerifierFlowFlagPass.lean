module

public import proofs.UnconstrainedPACDetection.VerifierFlowFlags

@[expose] public section

namespace UnconstrainedPACDetection.VerifierFlowFlagPass
open Complexity Complexity.TM
open VerifierFlowFlags
open VerifierActivationScan (flag)

def accept (es : List (ℤ × Bool)) (a : Bool) : Bool :=
  es.foldl (fun acc e => acc && (decide (e.1 = 0) || e.2)) a

theorem zero_header (t : Tape) (z : ℤ) (suffix : List Bool)
    (h : t.HasBinarySuffix (BinaryFields.encodeField z.natAbs.bits ++ suffix)) :
    decide (t.read = .zero) = decide (z = 0) := by
  cases hb : z.natAbs.bits with
  | nil =>
    have hn := BinaryFields.readNat_bits z.natAbs
    rw [hb] at hn
    have hz : z = 0 := Int.natAbs_eq_zero.mp hn.symm
    have hi : t.HasBinarySuffix (false :: suffix) := by
      simpa only [hb,BinaryFields.encodeField,List.singleton_append] using h
    rw [hi.read_cons,hz]; rfl
  | cons b bs =>
    have hz : z ≠ 0 := by intro hz; subst z; simp at hb
    have hi : t.HasBinarySuffix (true :: b :: (BinaryFields.encodeField bs ++ suffix)) := by
      simpa only [hb,BinaryFields.encodeField,List.cons_append] using h
    rw [hi.read_cons]
    simp [Γ.ofBool,hz]

theorem run (es : List (ℤ × Bool)) (tail : List Bool)
    (c : Cfg 1 (Fin 6)) (m : Γ) (a : Bool) (hq : c.state = 0)
    (hi : c.input.HasBinarySuffix (BinaryFields.encode (es.map (fun e => BinaryFields.writeInt e.1))))
    (hw : (c.work 0).HasBinarySuffix (es.map Prod.snd ++ tail)) (ho : c.output = flag m a) :
    ∃ d, machine.reachesIn
        ((BinaryFields.encode (es.map (fun e => BinaryFields.writeInt e.1))).length+es.length+1) c d ∧
      d.state = (5 : Fin 6) ∧ d.input.HasBinarySuffix [] ∧
      d.input.head = c.input.head+(BinaryFields.encode (es.map (fun e => BinaryFields.writeInt e.1))).length ∧
      d.input.cells = c.input.cells ∧ (d.work 0).HasBinarySuffix tail ∧
      (d.work 0).head = (c.work 0).head+es.length ∧
      (∀ j, (d.work j).cells = (c.work j).cells) ∧
      d.output = VerifierVerdictAnd.one m (accept es a) := by
  induction es generalizing c a with
  | nil =>
    have hi' : c.input.HasBinarySuffix [] := hi
    have hs := finish_step c m a hq hi'.read_nil hw.read_ne_start ho
    refine ⟨⟨(5 : Fin 6),c.input,c.work,VerifierVerdictAnd.one m a⟩,.step hs .zero,rfl,hi',?_,rfl,hw,?_,?_,rfl⟩
    · rfl
    · rfl
    · intro j; rfl
  | cons e es ih =>
    let rest := BinaryFields.encode (es.map (fun e => BinaryFields.writeInt e.1))
    have hi' : c.input.HasBinarySuffix
        (true :: decide (e.1 < 0) :: (BinaryFields.encodeField e.1.natAbs.bits ++ rest)) := hi
    have hor : c.output.read ≠ .start := by rw [ho,VerifierActivationScan.flag_read]; cases a <;> decide
    let c1 := moved c 1 .right .stay
    have hs1 := step_keep c 1 .right .stay (by rw [hq]; decide)
      hi.read_ne_start hw.read_ne_start hor (by simp [action,hq,hi'.read_cons,Γ.ofBool])
    have hi1 : c1.input.HasBinarySuffix
        (decide (e.1 < 0) :: (BinaryFields.encodeField e.1.natAbs.bits ++ rest)) := hi'.move_right_cons
    let c2 := moved c1 2 .right .stay
    have hs2 := step_keep c1 2 .right .stay (by change (1 : Fin 6) ≠ 5; decide)
      hi1.read_ne_start hw.read_ne_start hor (by simp [action,c1,moved])
    have hi2 : c2.input.HasBinarySuffix (BinaryFields.encodeField e.1.natAbs.bits ++ rest) := hi1.move_right_cons
    have hw' : (c2.work 0).HasBinarySuffix (e.2 :: (es.map Prod.snd ++ tail)) := hw
    let b := a && (decide (e.1 = 0) || e.2)
    let c3 : Cfg 1 (Fin 6) := ⟨3,c2.input,fun j => (c2.work j).move .right,flag m b⟩
    have hs3 : machine.step c2 = some c3 := by
      change machine.step c2 = some ⟨3,c2.input,fun j => (c2.work j).move .right,flag m b⟩
      dsimp only [b]
      rw [← zero_header c2.input e.1 rest hi2]
      exact check_step c2 m a e.2 rfl hi2.read_ne_start hw'.read_cons ho
    have hw3 : (c3.work 0).HasBinarySuffix (es.map Prod.snd ++ tail) := hw'.move_right_cons
    have ho3 : c3.output.read ≠ .start := by change Γ.ofBool b ≠ .start; cases b <;> decide
    obtain ⟨d,hd,hdq,hdi,hdh,hdc,hdw,hdo⟩ := field_run e.1.natAbs.bits rest c3 rfl hi2 hw3.read_ne_start ho3
    obtain ⟨f,hf,hfq,hfi,hfh,hfc,hfw,hfwh,hfwc,hfo⟩ :=
      ih d b hdq hdi (by rw [hdw]; exact hw3) hdo
    refine ⟨f,?_,hfq,hfi,?_,hfc.trans hdc,hfw,?_,?_,hfo⟩
    · have h := machine.reachesIn_trans (.step hs1 (.step hs2 (.step hs3 hd))) hf
      convert h using 1
      simp only [List.map_cons,BinaryFields.encode,List.flatMap_cons,List.length_append,
        BinaryFields.encodeField_length,BinaryFields.writeInt,List.length_cons]
      omega
    · rw [hfh,hdh]
      simp only [c3,c2,c1,moved,Tape.move,List.map_cons,BinaryFields.encode,
        List.flatMap_cons,List.length_append,BinaryFields.encodeField_length,
        BinaryFields.writeInt,List.length_cons]
      omega
    · rw [hfwh,hdw]
      simp only [c3,c2,c1,moved,Tape.move,List.length_cons]; omega
    · intro j; rw [hfwc,hdw]; rfl

theorem accept_iff (es : List (ℤ × Bool)) (a : Bool) :
    accept es a = true ↔ a = true ∧ ∀ e ∈ es, e.1 ≠ 0 → e.2 = true := by
  induction es generalizing a with
  | nil => simp [accept]
  | cons e es ih =>
    change accept es (a && (decide (e.1 = 0) || e.2)) = true ↔ _
    rw [ih]
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,List.mem_cons,forall_eq_or_imp]
    tauto

end UnconstrainedPACDetection.VerifierFlowFlagPass
