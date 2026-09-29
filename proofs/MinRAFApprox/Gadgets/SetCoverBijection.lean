module

public import proofs.MinRAFApprox.Gadgets.SetCoverReachability

@[expose] public section

namespace MinRAFApprox.SetCoverSource

open RAF RAF.Frankl MinRAFApprox.Reaction

variable {m n M : Nat}

/-- A cover's canonical reaction family is catalyzed entirely by the final
product of each selected block. -/
theorem canonical_productGraph
    (I : MinRAFApprox.SetCoverInstance (Fin m) (Fin n)) (hM : 0 < M)
    (C : Finset (Fin n)) (hC : I.Covers C) :
    ProductGraphCatalyzed (crs m n M) (catalysis I)
      (MinRAFApprox.canonicalRAF (U := Fin m) (K := Fin M) C) := by
  intro r hr
  apply Or.inr
  cases r with
  | gate i =>
      obtain ⟨j, hjC, hij⟩ := hC i
      refine ⟨block j (lastFin M hM),
        (MinRAFApprox.block_mem_canonicalRAF C j (lastFin M hM)).2 hjC,
        MinRAFApprox.Molecule.z j (lastFin M hM), ?_, ?_⟩
      · change MinRAFApprox.Molecule.z j (lastFin M hM) ∈
          ({MinRAFApprox.Molecule.z j (lastFin M hM)} :
            Finset (MinRAFApprox.Molecule n M))
        simp
      · simp [catalysis, lastFin, hij]
  | block j k =>
      have hjC := (MinRAFApprox.block_mem_canonicalRAF C j k).1 hr
      refine ⟨block j (lastFin M hM),
        (MinRAFApprox.block_mem_canonicalRAF C j (lastFin M hM)).2 hjC,
        MinRAFApprox.Molecule.z j (lastFin M hM), ?_, ?_⟩
      · change MinRAFApprox.Molecule.z j (lastFin M hM) ∈
          ({MinRAFApprox.Molecule.z j (lastFin M hM)} :
            Finset (MinRAFApprox.Molecule n M))
        simp
      · simp [catalysis, lastFin]

theorem canonical_isRAF
    (I : MinRAFApprox.SetCoverInstance (Fin m) (Fin n))
    (hm : 0 < m) (hM : 0 < M) (C : Finset (Fin n)) (hC : I.Covers C) :
    IsRAF (crs m n M) (catalysis I)
      (MinRAFApprox.canonicalRAF (U := Fin m) (K := Fin M) C) := by
  let : Nonempty (Fin m) := ⟨lastFin m hm⟩
  exact (isRAF_iff_foodGenerated_and_productGraph _ _ _).2
    ⟨MinRAFApprox.canonicalRAF_nonempty C,
      canonical_foodGenerated hm C,
      canonical_productGraph I hM C hC⟩

/-- Every literal RAF satisfies the four block-cover normal-form clauses. -/
theorem isRAF_implies_blockCover
    (I : MinRAFApprox.SetCoverInstance (Fin m) (Fin n))
    (hm : 0 < m) (hM : 0 < M)
    (S : Finset (MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M)))
    (hS : IsRAF (crs m n M) (catalysis I) S) :
    MinRAFApprox.IsBlockCoverRAF I S := by
  obtain ⟨hne, hfg, hgraph⟩ :=
    (isRAF_iff_foodGenerated_and_productGraph _ _ _).1 hS
  refine ⟨hne, ?_, ?_, ?_⟩
  · intro j k hjk u
    have hjlast := block_support_forces_last I hM S hgraph hjk
    have hjzero := block_prefix S hfg j (lastFin M hM) hjlast
      ⟨0, hM⟩ (by simp [lastFin])
    have hglast := zero_block_forces_last_gate S hfg hm hjzero rfl
    exact gate_prefix S hfg (lastFin m hm) hglast u
      (by simp [lastFin]; omega)
  · intro i hi
    obtain ⟨j, hjlast, hij⟩ := gate_support_yields_cover_block I hM S hgraph hi
    exact ⟨j, lastFin M hM, hjlast, hij⟩
  · intro j k hjk l
    have hjlast := block_support_forces_last I hM S hgraph hjk
    exact block_prefix S hfg j (lastFin M hM) hjlast l
      (by simp [lastFin]; omega)

/-- Exact literal theorem for the amplified source: its RAFs are precisely the
canonical families indexed by set covers. -/
theorem setCoverSource_raf_iff
    (I : MinRAFApprox.SetCoverInstance (Fin m) (Fin n))
    (hm : 0 < m) (hM : 0 < M)
    (S : Finset (MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M))) :
    IsRAF (crs m n M) (catalysis I) S ↔
      ∃ C : Finset (Fin n), I.Covers C ∧
        S = MinRAFApprox.canonicalRAF C := by
  let : Nonempty (Fin m) := ⟨lastFin m hm⟩
  let : Nonempty (Fin M) := ⟨lastFin M hM⟩
  constructor
  · intro hS
    exact (MinRAFApprox.blockCoverRAF_iff_cover I S).1
      (isRAF_implies_blockCover I hm hM S hS)
  · rintro ⟨C, hC, rfl⟩
    exact canonical_isRAF I hm hM C hC

end MinRAFApprox.SetCoverSource
