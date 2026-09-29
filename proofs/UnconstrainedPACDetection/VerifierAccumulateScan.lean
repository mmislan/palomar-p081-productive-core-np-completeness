module

public import proofs.UnconstrainedPACDetection.VerifierAccumulate
public import proofs.UnconstrainedPACDetection.VerifierBinaryAddFrames

@[expose] public section

/-! Complete in-place scan, leaving canonical sum contents ready for rewind. -/
namespace UnconstrainedPACDetection.VerifierAccumulate
open Complexity
open Complexity.TM

def finish (c : Cfg 1 machine.Q) (carry : Bool) : Cfg 1 machine.Q :=
  { c with
    state := (1,false),
    work := fun j => if carry then (c.work j).writeAndMove .one .right else c.work j }

theorem finish_step (carry : Bool) (emitted : List Bool) (c : Cfg 1 machine.Q)
    (hq : c.state = (0,carry)) (hx : c.input.HasBinarySuffix [])
    (hy : Split (c.work 0) emitted []) (hout : c.output.read ≠ .start) :
    machine.step c = some (finish c carry) := by
  have hys := split_suffix _ emitted [] hy
  have hn : c.state ≠ machine.qhalt := by simp [hq, machine]
  cases carry <;> simp only [TM.step, hn, ↓reduceIte]
  all_goals
    simp only [machine, hq, hx.read_nil, hys.read_nil, markerDir]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [finish, hys.read_nil] <;>
        simpa [transitionTape, hys.read_nil, idleDir] using
          transitionTape_eq_self hys.read_ne_start
    · exact transitionTape_eq_self hout

theorem scan_boundary (xs ys emitted : List Bool) (carry : Bool) (c : Cfg 1 machine.Q)
    (hq : c.state = (0,carry)) (hx : c.input.HasBinarySuffix xs)
    (hy : Split (c.work 0) emitted ys) (hout : c.output.read ≠ .start) :
    ∃ d, machine.reachesIn (max xs.length ys.length+1) c d ∧ d.state = (1,false) ∧
      Split (d.work 0) (emitted ++ VerifierBinaryAdd.add carry xs ys) [] ∧
      d.input.HasBinarySuffix [] ∧ d.input.head = c.input.head + xs.length ∧
      d.input.cells = c.input.cells ∧ d.output = c.output := by
  by_cases hempty : xs = [] ∧ ys = []
  · obtain ⟨rfl,rfl⟩ := hempty
    have hs := finish_step carry emitted c hq hx hy hout
    refine ⟨finish c carry, .step hs .zero, rfl, ?_, hx, by simp [finish], rfl, rfl⟩
    cases carry with
    | false => simpa only [finish, Bool.false_eq_true, ↓reduceIte, VerifierBinaryAdd.add, List.append_nil] using hy
    | true =>
      have h := split_write (c.work 0) emitted [] true hy
      simpa only [finish, ↓reduceIte, VerifierBinaryAdd.add, List.tail_nil, Γ.ofBool] using h
  · have hne : xs ≠ [] ∨ ys ≠ [] := by tauto
    obtain ⟨a, hca, hqa, hxa, hya, hha, hcia, hoa⟩ := scan_step xs ys emitted carry c hq hx hy hout hne
    have hpositive : 0 < xs.length+ys.length := by
      by_contra h
      apply hempty
      exact ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega)⟩
    obtain ⟨d, had, hqd, hyd, hxd, hhd, hcd, hod⟩ :=
      scan_boundary xs.tail ys.tail
        (emitted ++ [VerifierBinaryAdd.digit (xs.headD false) (ys.headD false) carry])
        (VerifierBinaryAdd.carry (xs.headD false) (ys.headD false) carry) a hqa hxa hya
        (by simpa only [hoa] using hout)
    have htime : max xs.tail.length ys.tail.length+1 = max xs.length ys.length := by
      simp only [List.length_tail]; omega
    have hadd : VerifierBinaryAdd.add carry xs ys =
        VerifierBinaryAdd.digit (xs.headD false) (ys.headD false) carry ::
        VerifierBinaryAdd.add (VerifierBinaryAdd.carry (xs.headD false) (ys.headD false) carry) xs.tail ys.tail := by
      cases xs <;> cases ys
      · simp at hempty
      all_goals simp only [VerifierBinaryAdd.add, List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil]
    refine ⟨d, ?_, hqd, ?_, hxd, ?_, hcd.trans hcia, hod.trans hoa⟩
    · simpa only [htime] using TM.reachesIn.step hca had
    · simpa only [hadd, List.append_assoc, List.singleton_append] using hyd
    · have hcount := VerifierBinaryAdd.suffix_advance_count hx
      omega
termination_by xs.length+ys.length
decreasing_by
  all_goals simp only [List.length_tail]; omega

end UnconstrainedPACDetection.VerifierAccumulate
