module

public import proofs.UnconstrainedPACDetection.FormulaPairExecution

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRoutedFrame
open Complexity Complexity.TM

/-- A fixed placement/permutation transports an actual subroutine contract while
    preserving arbitrary populated caller tapes and their precise head positions. -/
theorem hoare {n : Nat} (M : TM n) (pre post : Nat)
    (σ : Equiv.Perm (Fin (pre+n+post))) (inp : Tape)
    (small : Fin n → Tape) (large : Fin (pre+n+post) → Tape)
    (ys zs : List Bool) (B : Nat) (hp : ∀ j, Parked (large j))
    (hm : ∀ j, large (σ (placeWorkIdx pre post j)) = small j)
    (h : M.HoareTime (EmitPred inp small ys) (EmitPred inp small zs) B) :
    (VerifierWorkPermutation.machine (placeWorkTM pre post M) σ).HoareTime
      (EmitPred inp large ys) (EmitPred inp large zs) B := by
  have hbase := FormulaPairExecution.place_hoare M pre post inp small
    (fun j => large (σ j)) ys zs B (fun j => hp (σ j)) hm h
  rintro i w out ⟨hi,hw,ho⟩
  subst i; subst w
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := hbase inp (fun j => large (σ j)) out ⟨rfl,rfl,ho⟩
  have hs := VerifierWorkPermutation.run_commute (placeWorkTM pre post M) σ hr
  refine ⟨VerifierWorkPermutation.wrap _ σ d,t,ht,?_,hh,hdi,?_,hdo⟩
  · simpa only [VerifierWorkPermutation.machine, VerifierWorkPermutation.wrap,
      Equiv.apply_symm_apply] using hs
  · funext j
    simp only [VerifierWorkPermutation.wrap,hdw,Equiv.apply_symm_apply]

end UnconstrainedPACDetection.FormulaRoutedFrame
