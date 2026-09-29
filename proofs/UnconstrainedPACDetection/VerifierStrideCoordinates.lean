module

public import proofs.UnconstrainedPACDetection.VerifierCanonicalCoordinates

@[expose] public section

/-! Canonical same-entity traversal between reactions and coefficient sides. -/
namespace UnconstrainedPACDetection.VerifierStrideCoordinates
open VerifierCanonicalCoordinates

theorem mapped_tail_split {α : Type} (f : α → List Bool) (xs : List α)
    (i gap next : ℕ) (d : α) (he : next = i+1+gap) (hn : next < xs.length) :
    BinaryFields.encode ((xs.drop (i+1)).map f) =
      BinaryFields.encode (((xs.drop (i+1)).take gap).map f) ++
        (BinaryFields.encodeField (f (xs.getD next d)) ++ BinaryFields.encode ((xs.drop (next+1)).map f)) := by
  have ht : xs.drop (i+1) = (xs.drop (i+1)).take gap ++ (xs.drop (i+1)).drop gap :=
    (List.take_append_drop gap _).symm
  have hd : (xs.drop (i+1)).drop gap = xs.drop next := by rw [List.drop_drop,← he]
  rw [hd,List.drop_eq_getElem_cons hn] at ht
  have h := congrArg (fun l => BinaryFields.encode (l.map f)) ht
  rw [List.getD_eq_getElem xs d hn]
  simpa only [List.map_append,List.map_cons,BinaryFields.encode,List.flatMap_append,List.flatMap_cons] using h

def skipped (s : BinarySourceData.DenseSource) (b : Bool) (r : Fin s.reactions) (x : Fin s.entities) :=
  ((s.values.drop (valueIndex s b r x+1)).take (s.entities-1)).map Nat.bits

theorem successor_index (s : BinarySourceData.DenseSource) (b : Bool)
    (r r' : Fin s.reactions) (x : Fin s.entities) (hr : r'.val = r.val+1) :
    valueIndex s b r' x = valueIndex s b r x+1+(s.entities-1) := by
  have hm : 0 < s.entities := Nat.zero_lt_of_lt x.isLt
  have h : valueIndex s b r' x = valueIndex s b r x+s.entities := by
    simp only [valueIndex,hr]
    ring
  omega

theorem side_boundary_index (s : BinarySourceData.DenseSource)
    (last first : Fin s.reactions) (x : Fin s.entities)
    (hl : last.val+1 = s.reactions) (hf : first.val = 0) :
    valueIndex s true first x = valueIndex s false last x+1+(s.entities-1) := by
  have hm : 0 < s.entities := Nat.zero_lt_of_lt x.isLt
  have hsub : s.entities - 1 + 1 = s.entities := by omega
  simp only [valueIndex,Bool.false_eq_true,↓reduceIte,hf,zero_mul,add_zero,zero_add]
  nlinarith

theorem source_gap (s : BinarySourceData.DenseSource) (hs : s.WellFormed) (b b' : Bool)
    (r r' : Fin s.reactions) (x : Fin s.entities)
    (he : valueIndex s b' r' x = valueIndex s b r x+1+(s.entities-1)) :
    (skipped s b r x).length = s.entities-1 ∧
    sourceSuffix s b r x = BinaryFields.encode (skipped s b r x) ++
      (BinaryFields.encodeField (coefficient s b' r' x).bits ++ sourceSuffix s b' r' x) := by
  have hn := valueIndex_lt s hs b' r' x
  refine ⟨?_,?_⟩
  · have hg : s.entities-1 ≤ s.values.length-(valueIndex s b r x+1) := by omega
    simp [skipped,List.length_take,min_eq_left hg]
  · have h := mapped_tail_split Nat.bits s.values (valueIndex s b r x) (s.entities-1)
      (valueIndex s b' r' x) 0 he hn
    simpa only [sourceSuffix,skipped,coefficient_getD] using h

/-- Exactly m-1 intervening fields reach the next reaction at the same entity. -/
theorem source_successor (s : BinarySourceData.DenseSource) (hs : s.WellFormed) (b : Bool)
    (r r' : Fin s.reactions) (x : Fin s.entities) (hr : r'.val = r.val+1) :
    (skipped s b r x).length = s.entities-1 ∧
    sourceSuffix s b r x = BinaryFields.encode (skipped s b r x) ++
      (BinaryFields.encodeField (coefficient s b r' x).bits ++ sourceSuffix s b r' x) :=
  source_gap s hs b b r r' x (successor_index s b r r' x hr)

/-- The same stride crosses from the final left reaction to the first right one. -/
theorem source_side_boundary (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (last first : Fin s.reactions) (x : Fin s.entities)
    (hl : last.val+1 = s.reactions) (hf : first.val = 0) :
    (skipped s false last x).length = s.entities-1 ∧
    sourceSuffix s false last x = BinaryFields.encode (skipped s false last x) ++
      (BinaryFields.encodeField (coefficient s true first x).bits ++ sourceSuffix s true first x) :=
  source_gap s hs false true last first x (side_boundary_index s last first x hl hf)

end UnconstrainedPACDetection.VerifierStrideCoordinates
