module

public import proofs.UnconstrainedPACDetection.FormulaBlockingMachine
public import proofs.UnconstrainedPACDetection.VerifierTapeCleanup

@[expose] public section

namespace UnconstrainedPACDetection.FormulaBlockingCleanup
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)
open VerifierTapeCleanup (safe frame cleared safe_cleared stable)

def clearedWork (w : Fin 6 → Tape) := cleared (cleared (cleared w 1) 2) 3
def machine : TM 6 := seqTM (VerifierTapeCleanup.machine 1)
  (seqTM (VerifierTapeCleanup.machine 2) (VerifierTapeCleanup.machine 3))

theorem cleanup_three (xs ys zs : List Bool) (w : Fin 6 → Tape) (inp out : Tape)
    (hx : (w 1).cells = (word xs).cells) (hy : (w 2).cells = (word ys).cells)
    (hz : (w 3).cells = (word zs).cells) (hw : safe w)
    (hi : inp.read ≠ Γ.start) (ho : out.read ≠ Γ.start) (hh : 1 ≤ out.head) :
    machine.HoareTime (frame w inp out) (frame (clearedWork w) inp out)
      ((w 1).head+(w 2).head+(w 3).head+2*(xs.length+ys.length+zs.length)+26) := by
  let w1 := cleared w 1
  let w2 := cleared w1 2
  have hp1 := safe_cleared w 1 hw
  have hp2 := safe_cleared w1 2 hp1
  have h1 := VerifierTapeCleanup.cleanup_hoare 1 xs w inp out hx hw hi ho hh
  have h2 := VerifierTapeCleanup.cleanup_hoare 2 ys w1 inp out
    (by simpa [w1, cleared, VerifierPairRestore.word,
      VerifierBufferedProduct.wordTape] using hy) hp1 hi ho hh
  have h3 := VerifierTapeCleanup.cleanup_hoare 3 zs w2 inp out
    (by simpa [w2, w1, cleared, VerifierPairRestore.word,
      VerifierBufferedProduct.wordTape] using hz) hp2 hi ho hh
  have h23 := seqTM_hoareTime _ _ h2 (stable w2 inp out hp2 hi ho) h3
  have h := seqTM_hoareTime _ _ h1 (stable w1 inp out hp1 hi ho) h23
  apply h.mono_bound
  simp only [w1,w2,cleared,Function.update_of_ne (by decide : (2 : Fin 6) ≠ 1),
    Function.update_of_ne (by decide : (3 : Fin 6) ≠ 2),
    Function.update_of_ne (by decide : (3 : Fin 6) ≠ 1)]
  omega

theorem count_bound (src : List Bool) (i : Nat) :
    (FormulaLookupScan.run none i src).clauses ≤ src.length+1 := by
  obtain ⟨d,t,ht,hr,_,_,hc,_⟩ := FormulaLookupFrame.prepared_run src i
  have h := (head_le_start_add_of_reachesIn FormulaLookupScan.machine hr).2.2 1
  change (d.work 1).head ≤ 1+t at h
  rw [hc.1] at h
  simp only [List.length_replicate] at h
  omega

def ready (src : List Bool) (i v : Nat) (z : Bool) (emitted : List Bool) :
    Complexity.TM.TapePred 6 := fun inp work out =>
  inp = word src ∧ work 0 = word (List.replicate i true) ∧
  work 1 = word [] ∧ work 2 = word [] ∧ work 3 = word [] ∧
  OutAcc [z] (work 4) ∧ work 5 = regTape v ∧ OutAcc emitted out

theorem post_safe (src : List Bool) (i v : Nat) (b z : Bool) (emitted : List Bool)
    {inp : Tape} {work : Fin 6 → Tape} {out : Tape}
    (h : FormulaBlockingMachine.post src i v b z emitted inp work out) : safe work := by
  obtain ⟨_,hq,hc,h2,h3,_,_,hz,hv,_⟩ := h
  intro j
  fin_cases j
  · change (work 0).read ≠ Γ.start ∧ 1 ≤ (work 0).head
    rw [hq]; exact ⟨(word_parked _).read_ne_start,(word_parked _).1⟩
  · exact ⟨hc.parked.read_ne_start,hc.parked.1⟩
  · exact ⟨h2.read_ne_start,h2.1⟩
  · exact ⟨h3.read_ne_start,h3.1⟩
  · exact ⟨hz.parked.read_ne_start,hz.parked.1⟩
  · change (work 5).read ≠ Γ.start ∧ 1 ≤ (work 5).head
    rw [hv]; exact ⟨(parked_regTape _).read_ne_start,(parked_regTape _).1⟩

theorem cleanup_hoare (src : List Bool) (i v : Nat) (b z : Bool) (emitted : List Bool) :
    machine.HoareTime
      (fun inp work out => FormulaBlockingMachine.post src i v b z emitted inp work out ∧
        ∀ j, (work j).head ≤ 5*src.length+6*v+37)
      (ready src i v z emitted) (19*src.length+20*v+147) := by
  rintro inp work out ⟨h,hheads⟩
  have hs := post_safe src i v b z emitted h
  obtain ⟨rfl,hq,hc,_,_,hc2,hc3,hz,hv,ho⟩ := h
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hout⟩ := cleanup_three
    (List.replicate (FormulaLookupScan.run none i src).clauses true)
    (FormulaComparisonPrepare.literal src i) (FormulaBlockingMachine.target v b)
    work (word src) out (VerifierPairRestore.acc_cells _ _ hc) hc2 hc3 hs
    (word_parked src).read_ne_start ho.parked.read_ne_start ho.parked.1
    _ _ _ ⟨rfl,rfl,rfl⟩
  refine ⟨d,t,?_,hd,hh,hdi,?_,?_,?_,?_,?_,?_,?_⟩
  · have h1 := hheads 1
    have h2 := hheads 2
    have h3 := hheads 3
    have hc' := count_bound src i
    have hl := FormulaLookupRouting.raw_length_bound src i
    simp only [FormulaComparisonPrepare.literal,FormulaBlockingMachine.target,
      FormulaLookupMatching.marked,FormulaLookupMatching.target,SAT.Lit.encodeRaw,
      SAT.Unary.encode,List.length_append,List.length_cons,List.length_nil,List.length_replicate] at ht
    omega
  · rw [hdw]; simpa [clearedWork,cleared] using hq
  · rw [hdw]; simp [clearedWork,cleared]; rfl
  · rw [hdw]; simp [clearedWork,cleared]; rfl
  · rw [hdw]; simp [clearedWork,cleared]; rfl
  · rw [hdw]; simpa [clearedWork,cleared] using hz
  · rw [hdw]; simpa [clearedWork,cleared] using hv
  · rw [hout]; exact ho

end UnconstrainedPACDetection.FormulaBlockingCleanup
