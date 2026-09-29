module

public import proofs.UnconstrainedPACDetection.FormulaInputSelector
public import proofs.UnconstrainedPACDetection.FormulaRunComposition
public import proofs.UnconstrainedPACDetection.FormulaValidBudget

@[expose] public section

namespace UnconstrainedPACDetection.FormulaTotalWriter
open Complexity Complexity.TM Polynomial
open FormulaRunComposition (Run)

theorem normalize_mem_FP : FormulaInputSelector.normalize ∈ FP := by
  obtain ⟨k,M,p,hM⟩ := mem_FP_iff_computesInTime_polynomial.mp FormulaReductionInput.prepare_mem_FP
  let q : Polynomial Nat := C 2*p+C 3*X+C 25
  apply mem_FP_iff_computesInTime_polynomial.mpr
  refine ⟨compositionTapeCount k 0,compositionTM M FormulaInputSelector.machine,q,?_⟩
  intro xs
  have h0 : Run M xs (FormulaReductionInput.prepare xs) (p.eval xs.length) := hM xs
  have h1 := FormulaInputSelector.prepared_run xs
  have hn : FormulaInputSelector.machine.qstart≠FormulaInputSelector.machine.qhalt := by decide
  obtain ⟨d,t,ht,hr,hh,ho⟩ := FormulaRunComposition.compose M FormulaInputSelector.machine xs
    (FormulaReductionInput.prepare xs) (FormulaInputSelector.normalize xs) (p.eval xs.length) (xs.length+6) h0 h1 hn
  refine ⟨d,t,?_,hr,hh,ho⟩
  rw [FormulaReductionInput.prepare_length] at ht
  change t ≤ q.eval xs.length
  simp only [q,eval_add,eval_mul,eval_C,eval_X]
  omega

theorem normalize_length (xs : List Bool) : (FormulaInputSelector.normalize xs).length≤xs.length+2 := by
  unfold FormulaInputSelector.normalize
  split <;> simp

theorem valid_run (φ : SAT.CNF) : Run FormulaValidWriter.machine φ.encode (FormulaPACEncoding.encode φ)
    (FormulaValidWriter.budget φ) := by
  obtain ⟨d,t,ht,hr,hh,_,_,ho⟩ := FormulaValidWriter.hoare φ
    (Tape.init (φ.encode.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init []) ⟨rfl,fun _ => rfl,rfl⟩
  exact ⟨d,t,ht,hr,hh,ho.hasOutput⟩

theorem compile_mem_FP : FormulaPACEncoding.compile ∈ FP := by
  obtain ⟨k,M,p,hM⟩ := mem_FP_iff_computesInTime_polynomial.mp normalize_mem_FP
  obtain ⟨b,hb⟩ := FormulaValidBudget.polynomial
  let q : Polynomial Nat := C 2*p+C 2*(X+C 2)+b.comp (X+C 2)+C 11
  apply mem_FP_iff_computesInTime_polynomial.mpr
  refine ⟨compositionTapeCount k 28,compositionTM M FormulaValidWriter.machine,q,?_⟩
  intro xs
  obtain ⟨φ,hφ,hout⟩ := FormulaInputSelector.normalized_formula xs
  have h0 : Run M xs φ.encode (p.eval xs.length) := by
    unfold Run
    simpa only [hφ] using hM xs
  have h1 := valid_run φ
  have hn : FormulaValidWriter.machine.qstart≠FormulaValidWriter.machine.qhalt := by
    intro h; cases h
  obtain ⟨d,t,ht,hr,hh,ho⟩ := FormulaRunComposition.compose M FormulaValidWriter.machine xs φ.encode
    (FormulaPACEncoding.encode φ) (p.eval xs.length) (FormulaValidWriter.budget φ) h0 h1 hn
  refine ⟨d,t,?_,hr,hh,?_⟩
  · have hlen : φ.encode.length≤xs.length+2 := by simpa only [hφ] using normalize_length xs
    have hbound := hb φ
    have hmono : b.eval φ.encode.length≤b.eval (xs.length+2) := polynomial_eval_mono_nat b hlen
    have he : q.eval xs.length = 2*p.eval xs.length+2*(xs.length+2)+b.eval (xs.length+2)+11 := by simp [q]
    change t ≤ q.eval xs.length
    rw [he]
    omega
  · simpa only [hout] using ho

end UnconstrainedPACDetection.FormulaTotalWriter
