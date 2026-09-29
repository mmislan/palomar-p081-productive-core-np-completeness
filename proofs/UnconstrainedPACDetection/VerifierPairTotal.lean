module

public import proofs.UnconstrainedPACDetection.VerifierPairMalformed

@[expose] public section

namespace UnconstrainedPACDetection.VerifierPairParser
open Complexity Complexity.TM

/-- Exact syntax-only parser postcondition. Successful tapes remain at their
append cursors; rewinding is a separate charged machine operation. -/
def result (xs : List Bool) (work : Fin 2 → Tape) (out : Tape) : Prop :=
  match unpair? xs with
  | none => OutAcc [false] out
  | some (src,wit) => OutAcc src (work 0) ∧ OutAcc wit (work 1) ∧ OutAcc [true] out

theorem total (xs : List Bool) (inp a b out : Tape)
    (hi : inp.HasBinarySuffix xs) (ha : OutAcc [] a) (hb : OutAcc [] b) (ho : OutAcc [] out) :
    ∃ d t, t ≤ xs.length+1 ∧ machine.reachesIn t (config 0 inp a b out) d ∧
      machine.halted d ∧ result xs d.work d.output := by
  cases hu : unpair? xs with
  | none =>
    obtain ⟨d,t,ht,hd,hh,hout⟩ := malformed xs inp a b out hu hi ha.parked hb.parked ho
    exact ⟨d,t,ht,hd,hh,by simpa only [result,hu] using hout⟩
  | some data =>
    obtain ⟨src,wit⟩ := data
    have hx := eq_pair_of_unpair?_eq_some hu
    obtain ⟨d,hd,hh,hs,hw,hout⟩ := scan_pair src wit inp a b out [] (hx ▸ hi) ha hb ho
    refine ⟨d,2*src.length+wit.length+3,?_,hd,hh,?_⟩
    · rw [hx,pair_length]; omega
    · simpa only [result,hu,List.nil_append] using And.intro hs (And.intro hw hout)

end UnconstrainedPACDetection.VerifierPairParser
