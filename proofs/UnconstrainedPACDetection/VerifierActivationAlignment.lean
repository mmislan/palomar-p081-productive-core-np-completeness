module

public import proofs.UnconstrainedPACDetection.VerifierActivationBudget
public import Mathlib.Data.List.OfFn

@[expose] public section

namespace UnconstrainedPACDetection.VerifierActivationAlignment
open VerifierActivationSemantics (entries verdict)
open VerifierCanonicalCoordinates (coefficient)

def rows (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) : List VerifierActivationLoop.Row :=
  (List.finRange s.reactions).map (entries s w false) ++
    (List.finRange s.reactions).map (entries s w true)

theorem rows_length (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) :
    (rows s w).length = 2*s.reactions := by simp [rows]; omega

theorem entries_mask (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (hm : w.mask.length = s.entities) (side : Bool) (r : Fin s.reactions) :
    (entries s w side r).map Prod.snd = w.mask := by
  apply List.ext_getElem
  · simp [entries,hm]
  · intro i hi hj
    simp only [entries,List.length_map,List.length_finRange] at hi
    simp [entries,List.getD,show i < w.mask.length by omega]

theorem rows_mask (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (hm : w.mask.length = s.entities) : ∀ es ∈ rows s w, es.map Prod.snd = w.mask := by
  intro es he
  rcases List.mem_append.mp he with he | he
  all_goals
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp he
    exact entries_mask s w hm _ r

theorem rectangle {α : Type} (f : ℕ → α) (m n off : ℕ) :
    (List.finRange n).flatMap (fun r => (List.finRange m).map (fun x => f (off+r.val*m+x.val))) =
      List.ofFn (fun i : Fin (n*m) => f (off+i.val)) := by
  have h := List.ofFn_mul (fun i : Fin (n*m) => f (off+i.val))
  simpa [List.finRange,List.flatMap, List.map_ofFn,Function.comp_def,Nat.add_assoc] using h.symm

theorem fields_side (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) (side : Bool) :
    ((List.finRange s.reactions).map (entries s w side)).flatMap (fun es => es.map Prod.fst) =
      List.ofFn (fun i : Fin (s.reactions*s.entities) =>
        (s.values.getD ((if side then s.entities*s.reactions else 0)+i.val) 0).bits) := by
  simp only [List.flatMap_map,entries,List.map_map,Function.comp_def]
  simp_rw [VerifierCanonicalCoordinates.coefficient_getD]
  exact rectangle (fun i => (s.values.getD i 0).bits) s.entities s.reactions _

theorem fields (s : BinarySourceData.DenseSource) (hs : s.WellFormed) (w : BinaryWitnessData.Witness) :
    (rows s w).flatMap (fun es => es.map Prod.fst) = s.values.map Nat.bits := by
  rw [rows,List.flatMap_append,fields_side,fields_side]
  simp only [Bool.false_eq_true,↓reduceIte,zero_add]
  have hlen : s.values.length = s.reactions*s.entities+s.reactions*s.entities := by
    change s.values.length = 2*(s.entities*s.reactions) at hs
    nlinarith
  have h := List.ofFn_add (f := fun i : Fin (s.reactions*s.entities+s.reactions*s.entities) =>
    (s.values.getD i.val 0).bits)
  have hwhole : List.ofFn (fun i : Fin (s.reactions*s.entities+s.reactions*s.entities) =>
      (s.values.getD i.val 0).bits) = s.values.map Nat.bits := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp [List.getD,show i < s.values.length by simpa using hj]
  rw [← hwhole,h]
  simp [Nat.mul_comm,Nat.add_comm]

end UnconstrainedPACDetection.VerifierActivationAlignment
