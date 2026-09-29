module

public import proofs.UnconstrainedPACDetection.FormulaComparisonScan

@[expose] public section

namespace UnconstrainedPACDetection.FormulaBlockingMachine
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)
open FormulaComparisonPrepare (literal)

def target (v : Nat) (b : Bool) := FormulaLookupMatching.marked (FormulaLookupMatching.target v b)
def verdict (src : List Bool) (i v : Nat) (b : Bool) :=
  VerifierBinaryEquality.compare true (target v b) (literal src i)

def post (src : List Bool) (i v : Nat) (b z : Bool) (emitted : List Bool) :
    Complexity.TM.TapePred 6 := fun inp work out =>
  inp = word src ∧ work 0 = word (List.replicate i true) ∧
  OutAcc (List.replicate (FormulaLookupScan.run none i src).clauses true) (work 1) ∧
  (work 2).HasBinarySuffix [] ∧ (work 3).HasBinarySuffix [] ∧
  (work 2).cells = (word (literal src i)).cells ∧
  (work 3).cells = (word (target v b)).cells ∧
  OutAcc [z] (work 4) ∧ work 5 = regTape v ∧ OutAcc emitted out

theorem ready_parked (src : List Bool) (i v : Nat) (b : Bool) (emitted : List Bool)
    {inp : Tape} {work : Fin 6 → Tape} {out : Tape}
    (h : FormulaComparisonPrepare.ready src i v b emitted inp work out) :
    ∀ j, Parked (work j) := by
  obtain ⟨_,hq,hc,hl,ht,he,hv,_⟩ := h
  intro j
  fin_cases j
  · change Parked (work 0); rw [hq]; exact word_parked _
  · exact hc.parked
  · change Parked (work 2); rw [hl]; exact word_parked _
  · change Parked (work 3); rw [ht]; exact word_parked _
  · change Parked (work 4); rw [he]; exact word_parked _
  · change Parked (work 5); rw [hv]; exact parked_regTape _

theorem scan_hoare (src : List Bool) (i v : Nat) (b : Bool) (emitted : List Bool) :
    FormulaComparisonScan.machine.HoareTime (FormulaComparisonPrepare.ready src i v b emitted)
      (post src i v b (verdict src i v b) emitted) (src.length+v+3) := by
  intro inp work out h
  have hp := ready_parked src i v b emitted h
  obtain ⟨rfl,hq,hc,hl,ht,he,hv,ho⟩ := h
  obtain ⟨d,t,hb,hd,hh,hdi,hw,he2,he3,hc2,hc3,hbit,hout⟩ := FormulaComparisonScan.scan_hoare
    (target v b) (literal src i) (word src) work emitted (word_parked src) hp hl ht he
    _ _ _ ⟨rfl,rfl,ho⟩
  refine ⟨d,t,?_,hd,hh,hdi,?_,?_,he2,he3,hc2,hc3,hbit,?_,hout⟩
  · have hr := FormulaLookupRouting.raw_length_bound src i
    have hmax : max (target v b).length (literal src i).length ≤ src.length+v+2 := by
      simp only [target,literal,FormulaLookupMatching.marked,FormulaLookupMatching.target,
        SAT.Lit.encodeRaw,SAT.Unary.encode,List.length_append,List.length_cons,List.length_nil,
        List.length_replicate]
      apply max_le <;> omega
    omega
  · rw [hw 0 (by decide)]; exact hq
  · rw [hw 1 (by decide)]; exact hc
  · rw [hw 5 (by decide)]; exact hv

def machine (b : Bool) : TM 6 := seqTM (FormulaComparisonPrepare.machine b) FormulaComparisonScan.machine

theorem operation_hoare (src : List Bool) (i v : Nat) (b : Bool) (emitted : List Bool) :
    (machine b).HoareTime (EmitPred (word src) (FormulaComparisonPrepare.initialWork i v) emitted)
      (post src i v b (verdict src i v b) emitted) (5*src.length+6*v+36) := by
  have hs : ∀ inp work out, FormulaComparisonPrepare.ready src i v b emitted inp work out →
      FormulaComparisonPrepare.ready src i v b emitted (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
    intro inp work out h
    have hp := ready_parked src i v b emitted h
    have hi := h.1
    have ho := h.2.2.2.2.2.2.2
    obtain ⟨hin,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start
      (hi ▸ (word_parked src).read_ne_start) (fun j => (hp j).read_ne_start)
      ho.parked.read_ne_start
    simpa only [hin,hw,hout] using h
  have h := seqTM_hoareTime _ _ (FormulaComparisonPrepare.ready_hoare src i v b emitted)
    hs (scan_hoare src i v b emitted)
  exact h.mono_bound (by omega)

theorem compare_symm (xs ys : List Bool) :
    VerifierBinaryEquality.compare true xs ys = VerifierBinaryEquality.compare true ys xs := by
  apply Bool.eq_iff_iff.mpr
  simp only [VerifierBinaryEquality.equality_iff]
  exact eq_comm

/-- Actual occurrence blocking on a decoded formula, including the missing-occurrence case. -/
theorem blocking_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (b : Bool) (emitted : List Bool) :
    (machine b).HoareTime (EmitPred (word φ.encode) (FormulaComparisonPrepare.initialWork i.val v.val) emitted)
      (post φ.encode i.val v.val b (FormulaWiring.blocked φ i v b) emitted)
      (5*φ.encode.length+6*v.val+36) := by
  have he : verdict φ.encode i.val v.val b = FormulaWiring.blocked φ i v b := by
    rw [verdict,compare_symm]
    exact FormulaLookupMatching.blocking_compare φ i v b
  simpa only [he] using operation_hoare φ.encode i.val v.val b emitted

/-- Cursor bounds required by the following scratch-cleanup phase. -/
theorem bounded_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (b : Bool) (emitted : List Bool) :
    (machine b).HoareTime (EmitPred (word φ.encode) (FormulaComparisonPrepare.initialWork i.val v.val) emitted)
      (fun inp work out => post φ.encode i.val v.val b (FormulaWiring.blocked φ i v b) emitted inp work out ∧
        ∀ j, (work j).head ≤ 5*φ.encode.length+6*v.val+37)
      (5*φ.encode.length+6*v.val+36) := by
  intro inp work out h
  have hw0 := h.2.1
  obtain ⟨d,t,ht,hd,hh,hpost⟩ := blocking_hoare φ i v b emitted inp work out h
  have heads := (head_le_start_add_of_reachesIn (machine b) hd).2.2
  refine ⟨d,t,ht,hd,hh,hpost,?_⟩
  intro j
  have hj : (work j).head = 1 := by
    rw [hw0]
    fin_cases j <;> rfl
  have hb := heads j
  change (d.work j).head ≤ (work j).head+t at hb
  rw [hj] at hb
  omega

end UnconstrainedPACDetection.FormulaBlockingMachine
