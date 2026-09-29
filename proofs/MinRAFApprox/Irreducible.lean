module

public import proofs.MinRAFApprox.NumericalEstimates

@[expose] public section

namespace MinRAFApprox.SetCoverSource

open RAF MinRAFApprox.Reaction

variable {m n M : Nat}

/-- A nonempty RAF with no proper RAF subset.  This is the standard iRAF
predicate, kept local so the reduction does not depend on broader RAF-family
enumeration modules. -/
def IsIrreducibleRAF {Mol R : Type*} [DecidableEq Mol] [DecidableEq R]
    (Q : CRS Mol R) (C : Catalysis Mol R) (A : Finset R) : Prop :=
  IsRAF Q C A ∧
    ∀ B : Finset R, IsRAF Q C B → B ⊆ A → A ⊆ B

/-- Inclusion-minimal, rather than minimum-cardinality, set cover. -/
def InclusionMinimalCover
    (I : MinRAFApprox.SetCoverInstance (Fin m) (Fin n))
    (C : Finset (Fin n)) : Prop :=
  I.Covers C ∧
    ∀ D : Finset (Fin n), I.Covers D → D ⊆ C → C ⊆ D

/-- Canonical RAF containment is exactly containment of the selected sets. -/
theorem canonicalRAF_subset_iff (hM : 0 < M)
    {C D : Finset (Fin n)} :
    MinRAFApprox.canonicalRAF (U := Fin m) (K := Fin M) D ⊆
        MinRAFApprox.canonicalRAF C ↔
      D ⊆ C := by
  constructor
  · intro h j hjD
    have hbD : block (U := Fin m) j (lastFin M hM) ∈
        MinRAFApprox.canonicalRAF (U := Fin m) (K := Fin M) D :=
      (MinRAFApprox.block_mem_canonicalRAF D j (lastFin M hM)).2 hjD
    exact (MinRAFApprox.block_mem_canonicalRAF C j (lastFin M hM)).1 (h hbD)
  · intro h r hr
    cases r with
    | gate i => exact MinRAFApprox.gate_mem_canonicalRAF C i
    | block j k =>
        exact (MinRAFApprox.block_mem_canonicalRAF C j k).2
          (h ((MinRAFApprox.block_mem_canonicalRAF D j k).1 hr))

/-- Exact irreducibility theorem: a canonical source RAF is an iRAF exactly
when its selected sets form an inclusion-minimal cover. -/
theorem irreducibleRAF_iff_inclusionMinimalCover
    (I : MinRAFApprox.SetCoverInstance (Fin m) (Fin n))
    (hm : 0 < m) (hM : 0 < M) (C : Finset (Fin n)) :
    IsIrreducibleRAF (crs m n M) (catalysis I)
        (MinRAFApprox.canonicalRAF (U := Fin m) (K := Fin M) C) ↔
      InclusionMinimalCover I C := by
  constructor
  · intro hirr
    obtain ⟨D, hD, hEq⟩ :=
      (setCoverSource_raf_iff I hm hM
        (MinRAFApprox.canonicalRAF (U := Fin m) (K := Fin M) C)).1 hirr.1
    have hCD : C ⊆ D :=
      (canonicalRAF_subset_iff (m := m) hM).1 (by simp [hEq])
    have hDC : D ⊆ C :=
      (canonicalRAF_subset_iff (m := m) hM).1 (by simp [hEq])
    have hCoverC : I.Covers C := by
      have hCD_eq : C = D := Finset.Subset.antisymm hCD hDC
      simpa [hCD_eq] using hD
    refine ⟨hCoverC, ?_⟩
    intro E hE hEC
    have hrafE := canonical_isRAF I hm hM E hE
    have hsub : MinRAFApprox.canonicalRAF (U := Fin m) (K := Fin M) E ⊆
        MinRAFApprox.canonicalRAF C :=
      (canonicalRAF_subset_iff (m := m) hM).2 hEC
    exact (canonicalRAF_subset_iff (m := m) hM).1
      (hirr.2 (MinRAFApprox.canonicalRAF E) hrafE hsub)
  · rintro ⟨hC, hminimal⟩
    refine ⟨canonical_isRAF I hm hM C hC, ?_⟩
    intro S hrafS hSC
    obtain ⟨D, hD, rfl⟩ := (setCoverSource_raf_iff I hm hM S).1 hrafS
    have hDC : D ⊆ C := (canonicalRAF_subset_iff (m := m) hM).1 hSC
    exact (canonicalRAF_subset_iff (m := m) hM).2 (hminimal D hD hDC)

/-- A finite indexed hypergraph, with vertices indexed by `Fin v` and edges
indexed by `Fin e`. -/
structure IndexedHypergraph (e v : Nat) where
  edges : Fin e → Finset (Fin v)
  nonempty : ∀ edge, (edges edge).Nonempty

namespace IndexedHypergraph

variable {e v : Nat}

def Transversal (H : IndexedHypergraph e v) (C : Finset (Fin v)) : Prop :=
  ∀ edge : Fin e, ∃ vertex ∈ C, vertex ∈ H.edges edge

def toSetCover (H : IndexedHypergraph e v) :
    MinRAFApprox.SetCoverInstance (Fin e) (Fin v) where
  sets vertex := Finset.univ.filter fun edge => vertex ∈ H.edges edge
  coverable edge := by
    obtain ⟨vertex, hv⟩ := H.nonempty edge
    exact ⟨vertex, by simp [hv]⟩

theorem covers_iff_transversal (H : IndexedHypergraph e v)
    (C : Finset (Fin v)) :
    (toSetCover H).Covers C ↔ H.Transversal C := by
  constructor <;> intro h edge
  · obtain ⟨vertex, hvC, hve⟩ := h edge
    exact ⟨vertex, hvC, by simpa [toSetCover] using hve⟩
  · obtain ⟨vertex, hvC, hve⟩ := h edge
    exact ⟨vertex, hvC, by simp [toSetCover, hve]⟩

def MinimalTransversal (H : IndexedHypergraph e v)
    (C : Finset (Fin v)) : Prop :=
  H.Transversal C ∧
    ∀ D : Finset (Fin v), H.Transversal D → D ⊆ C → C ⊆ D

theorem minimalTransversal_iff_minimalCover
    (H : IndexedHypergraph e v) (C : Finset (Fin v)) :
    H.MinimalTransversal C ↔ InclusionMinimalCover (toSetCover H) C := by
  simp only [MinimalTransversal, InclusionMinimalCover, covers_iff_transversal]

/-- Hypergraph transversals are realized exactly as irreducible RAFs, already
with block length one. -/
theorem irreducibleRAF_iff_minimalTransversal
    (H : IndexedHypergraph e v) (he : 0 < e) (C : Finset (Fin v)) :
    IsIrreducibleRAF (crs e v 1) (catalysis (toSetCover H))
        (MinRAFApprox.canonicalRAF (U := Fin e) (K := Fin 1) C) ↔
      H.MinimalTransversal C := by
  rw [irreducibleRAF_iff_inclusionMinimalCover (toSetCover H) he (by omega)]
  exact (minimalTransversal_iff_minimalCover H C).symm

end IndexedHypergraph

end MinRAFApprox.SetCoverSource
