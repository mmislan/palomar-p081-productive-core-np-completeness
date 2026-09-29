module

public import proofs.UnconstrainedPACDetection.FormulaLookupMachine

@[expose] public section

namespace UnconstrainedPACDetection.FormulaLookupScan
open Complexity Complexity.TM

theorem after_query (c : Cfg 2 machine.Q) (a : Action) (i : Nat)
    (h : (c.work 0).HasBinarySuffix (List.replicate i true))
    (hs : a.skip = true → 0 < i) :
    ((after c a).work 0).HasBinarySuffix
      (List.replicate (if a.skip then i-1 else i) true) := by
  cases he : a.skip
  · simpa [after,he] using h
  · have hp := hs he
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    simpa [after,he] using h.move_right_cons

theorem after_count (c : Cfg 2 machine.Q) (a : Action) (xs : List Bool)
    (h : (c.work 1).HasBinaryPrefix xs) :
    ((after c a).work 1).HasBinaryPrefix
      (xs ++ List.replicate (if a.count then 1 else 0) true) := by
  simpa [after] using FormulaTokenCount.emit_prefix (c.work 1) xs a.count h

theorem after_output (c : Cfg 2 machine.Q) (a : Action) (xs : List Bool)
    (h : c.output.HasBinaryPrefix xs) :
    (after c a).output.HasBinaryPrefix (xs ++ a.output.toList) :=
  put_prefix c.output xs a.output h

theorem query_blank (t : Tape) (i : Nat)
    (h : t.HasBinarySuffix (List.replicate i true)) :
    decide (t.read = .blank) = decide (i = 0) := by
  cases i with
  | zero => simp [h.read_nil]
  | succ i => simp [h.read_cons,Γ.ofBool]

theorem eof_step (c : Cfg 2 machine.Q) (s : Option Bool)
    (hs : c.state = some s) (hi : c.input.HasBinarySuffix [])
    (hw : ∀ j, (c.work j).read ≠ .start) (ho : c.output.read ≠ .start) :
    machine.step c = some {c with state := none} := by
  simp only [TM.step,machine,hs,reduceCtorEq,↓reduceIte,hi.read_nil]
  congr 1
  apply Cfg.ext
  · rfl
  · simp [idleDir,Tape.move]
  · funext j
    exact transitionTape_eq_self (hw j)
  · exact transitionTape_eq_self ho

/-- Full streaming execution from prepared tapes, including early stop and EOF.
The returned query cursor and clause/output prefixes remain available to the caller. -/
theorem scan (xs : List Bool) :
    ∀ (s : Option Bool) (i : Nat) (c : Cfg 2 machine.Q) (marks out : List Bool),
    c.state = some s → c.input.HasBinarySuffix xs →
    (c.work 0).HasBinarySuffix (List.replicate i true) →
    (c.work 1).HasBinaryPrefix marks → c.output.HasBinaryPrefix out →
    ∃ d t, t ≤ xs.length+1 ∧ machine.reachesIn t c d ∧ machine.halted d ∧
      (d.work 0).HasBinarySuffix (List.replicate (run s i xs).remaining true) ∧
      (d.work 1).HasBinaryPrefix (marks ++ List.replicate (run s i xs).clauses true) ∧
      d.output.HasBinaryPrefix (out ++ (run s i xs).raw) := by
  induction xs with
  | nil =>
    intro s i c marks out hs hi hq hc ho
    have hw : ∀ j, (c.work j).read ≠ .start := by
      intro j
      fin_cases j
      · exact hq.read_ne_start
      · change (c.work 1).read ≠ .start
        rw [hc.read_blank]; decide
    refine ⟨{c with state := none},1,by simp,.step (eof_step c s hs hi hw ?_) .zero,rfl,?_,?_,?_⟩
    · rw [ho.read_blank]; decide
    · exact hq
    · simpa [run] using hc
    · simpa [run] using ho
  | cons b xs ih =>
    intro s i c marks out hs hi hq hc ho
    have hw : ∀ j, (c.work j).read ≠ .start := by
      intro j
      fin_cases j
      · exact hq.read_ne_start
      · change (c.work 1).read ≠ .start
        rw [hc.read_blank]; decide
    have hop : c.output.read ≠ .start := by rw [ho.read_blank]; decide
    let a := action s b (decide (i = 0))
    let mid := after c a
    have step := bit_step s b (decide (i = 0)) c hs hi.read_cons (query_blank _ i hq) hw hop
    have hm : mid.input.HasBinarySuffix xs := hi.move_right_cons
    have hskip : a.skip = true → 0 < i := by
      dsimp [a,action]
      split <;> simp
      omega
    have hmq := after_query c a i hq hskip
    have hmc := after_count c a marks hc
    have hmo := after_output c a out ho
    cases he : event s b with
    | pending v =>
      obtain ⟨d,t,ht,hd,hh,hq',hc',ho'⟩ := ih (some v) i mid marks out
        (by simp [mid,after,a,action,he]; rfl) hm
        (by simpa [mid,a,action,he] using hmq)
        (by simpa [mid,a,action,he] using hmc)
        (by simpa [mid,a,action,he] using hmo)
      refine ⟨d,t+1,by simpa using Nat.add_le_add_right ht 1,.step step hd,hh,?_,?_,?_⟩
      · simpa [run,he] using hq'
      · simpa [run,he] using hc'
      · simpa [run,he] using ho'
    | data v =>
      obtain ⟨d,t,ht,hd,hh,hq',hc',ho'⟩ := ih none i mid marks _
        (by simp [mid,after,a,action,he]; rfl) hm
        (by simpa [mid,a,action,he] using hmq)
        (by simpa [mid,a,action,he] using hmc) hmo
      refine ⟨d,t+1,by simpa using Nat.add_le_add_right ht 1,.step step hd,hh,?_,?_,?_⟩
      · simpa [run,he] using hq'
      · simpa [run,he] using hc'
      · by_cases hz : i = 0 <;> simpa [run,he,a,action,hz,List.append_assoc] using ho'
    | literal =>
      cases i with
      | zero =>
        refine ⟨mid,1,by simp,.step step .zero,?_,?_,?_,?_⟩
        · change mid.state = none
          simp [mid,after,a,action,he]
          rfl
        · simpa [mid,after,a,action,he,run] using hq
        · simpa [mid,after,a,action,he,run,FormulaTokenCount.emit] using hc
        · simpa [mid,after,a,action,he,run,put] using ho
      | succ i =>
        obtain ⟨d,t,ht,hd,hh,hq',hc',ho'⟩ := ih none i mid marks out
          (by simp [mid,after,a,action,he]; rfl) hm
          (by simpa [mid,a,action,he] using hmq)
          (by simpa [mid,a,action,he] using hmc)
          (by simpa [mid,a,action,he] using hmo)
        refine ⟨d,t+1,by simpa using Nat.add_le_add_right ht 1,.step step hd,hh,?_,?_,?_⟩
        · simpa [run,he] using hq'
        · simpa [run,he] using hc'
        · simpa [run,he] using ho'
    | clause =>
      obtain ⟨d,t,ht,hd,hh,hq',hc',ho'⟩ := ih none i mid (marks ++ [true]) out
        (by simp [mid,after,a,action,he]; rfl) hm
        (by simpa [mid,a,action,he] using hmq)
        (by simpa [mid,a,action,he] using hmc)
        (by simpa [mid,a,action,he] using hmo)
      refine ⟨d,t+1,by simpa using Nat.add_le_add_right ht 1,.step step hd,hh,?_,?_,?_⟩
      · simpa [run,he] using hq'
      · simpa [run,he,List.replicate_succ,List.append_assoc] using hc'
      · simpa [run,he] using ho'

end UnconstrainedPACDetection.FormulaLookupScan
