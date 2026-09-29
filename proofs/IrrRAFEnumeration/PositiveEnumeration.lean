module

public import proofs.IrrRAFEnumeration.PositiveCompletion

@[expose] public section

namespace IrrRAFEnumeration.PositiveCompletion

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Bounded unrolling of the positive-oracle enumeration loop. The second
component counts oracle calls, not TM transitions. Neither a powerset nor the
answer family is computed by this program. Fuel is used only to truncate it. -/
def enumerate (oracle : Finset (Finset α) → Finset α → Bool) (rs : List α) :
    Nat → Finset (Finset α) → List (Finset α) × Nat
  | 0, _ => ([], 0)
  | fuel+1, G =>
    if oracle G Finset.univ then
      let I := sweep (oracle G) rs Finset.univ
      let tail := enumerate oracle rs fuel (insert I G)
      (I :: tail.1, rs.length + 1 + tail.2)
    else ([], 1)

/-- Sufficient unrolling returns exactly the missing minima, without duplicates,
and accounts for every successful sweep and the final negative query. -/
theorem enumerate_correct (P : Finset α → Prop) (F : Finset (Finset α))
    (hF : ∀ I, I ∈ F ↔ Minimal P I)
    (oracle : Finset (Finset α) → Finset α → Bool)
    (horacle : ∀ G U, oracle G U = true ↔ Available P G U)
    (rs : List α) (hcover : ∀ r, r ∈ rs)
    (fuel : Nat) (G : Finset (Finset α)) (hG : G ⊆ F)
    (hfuel : (F \ G).card < fuel) :
    (enumerate oracle rs fuel G).1.Nodup ∧
    (∀ I ∈ (enumerate oracle rs fuel G).1, I ∉ G) ∧
    (enumerate oracle rs fuel G).1.toFinset ∪ G = F ∧
    (enumerate oracle rs fuel G).2 =
      (rs.length+1) * (enumerate oracle rs fuel G).1.length + 1 := by
  induction fuel generalizing G with
  | zero => omega
  | succ fuel ih =>
    by_cases hquery : oracle G Finset.univ = true
    · let I := sweep (oracle G) rs Finset.univ
      obtain ⟨hmin, hnew⟩ := sweep_new_minimal (oracle G) (horacle G) rs Finset.univ
        (fun r _ => hcover r) ((horacle G _).mp hquery)
      have hIF : I ∈ F := (hF I).mpr hmin
      have hIG : I ∉ G := hnew
      have hnext : insert I G ⊆ F := Finset.insert_subset hIF hG
      have hfuel' : (F \ insert I G).card < fuel := by
        have hc : (insert I G).card = G.card + 1 := Finset.card_insert_of_notMem hIG
        rw [Finset.card_sdiff_of_subset hG] at hfuel
        rw [Finset.card_sdiff_of_subset hnext, hc]
        have hcG := Finset.card_le_card hnext
        rw [hc] at hcG
        omega
      obtain ⟨hnd, hav, heq, hcost⟩ := ih (insert I G) hnext hfuel'
      have hinot : I ∉ (enumerate oracle rs fuel (insert I G)).1 := by
        intro hi
        exact hav I hi (Finset.mem_insert_self I G)
      simp only [enumerate, hquery, ↓reduceIte]
      change
        (I :: (enumerate oracle rs fuel (insert I G)).1).Nodup ∧
        (∀ J ∈ I :: (enumerate oracle rs fuel (insert I G)).1, J ∉ G) ∧
        (I :: (enumerate oracle rs fuel (insert I G)).1).toFinset ∪ G = F ∧
        rs.length+1+(enumerate oracle rs fuel (insert I G)).2 =
          (rs.length+1)*(I :: (enumerate oracle rs fuel (insert I G)).1).length+1
        at ⊢
      refine ⟨List.nodup_cons.mpr ⟨hinot, hnd⟩, ?_, ?_, ?_⟩
      · intro J hJ
        rcases List.mem_cons.mp hJ with rfl | hJ
        · exact hIG
        · exact fun hJG => hav J hJ (Finset.mem_insert_of_mem hJG)
      · simpa only [List.toFinset_cons, Finset.insert_union, Finset.union_insert] using heq
      · simp only [List.length_cons]
        rw [hcost]
        ring
    · have hcomplete : G = F := by
        apply Finset.Subset.antisymm hG
        intro I hi
        by_contra hnot
        have hav := (available_univ_iff_missing
          (fun J hJ => (hF J).mp (hG hJ))).mpr ⟨I, (hF I).mp hi, hnot⟩
        exact hquery ((horacle G _).mpr hav)
      simp only [enumerate, hquery]
      simp [hcomplete]

/-- Complete duplicate-free ordinary irrRAF enumeration, conditional only on
the exact positive oracle, with its actual number of oracle invocations.
The remaining complexity obligation is to implement and charge that oracle
and this loop in the repository's TM model. -/
theorem enumerate_irrRAFs_correct {M R : Type*} [Fintype R]
    [DecidableEq M] [DecidableEq R] (Q : RAF.CRS M R) (C : RAF.Catalysis M R)
    (oracle : Finset (Finset R) → Finset R → Bool)
    (horacle : ∀ G U, oracle G U = true ↔ Available (RAF.IsRAF Q C) G U)
    (rs : List R) (hcover : ∀ r, r ∈ rs) (fuel : Nat)
    (hfuel : (irrRAFFamily Q C).card < fuel) :
    (enumerate oracle rs fuel ∅).1.Nodup ∧
    (enumerate oracle rs fuel ∅).1.toFinset = irrRAFFamily Q C ∧
    (enumerate oracle rs fuel ∅).2 =
      (rs.length+1)*(enumerate oracle rs fuel ∅).1.length+1 := by
  have h := enumerate_correct (RAF.IsRAF Q C) (irrRAFFamily Q C)
    (fun I => mem_irrRAFFamily Q C I) oracle horacle rs hcover fuel ∅
    (Finset.empty_subset _) (by simpa using hfuel)
  simpa using h

end IrrRAFEnumeration.PositiveCompletion
