module

public import proofs.MinRAFApprox.Gadgets.FiniteSupport
public import proofs.MinRAFApprox.ComplexityTransfer

@[expose] public section

namespace MinRAFApprox.SetCoverSource

variable {m n M : Nat}

/-- Number of element-set incidences in an indexed SET COVER instance. -/
def incidenceCount (I : MinRAFApprox.SetCoverInstance (Fin m) (Fin n)) : Nat :=
  ∑ j : Fin n, (I.sets j).card

/-- The incidence list is never larger than the full `n`-by-`m` matrix. -/
theorem incidenceCount_le (I : MinRAFApprox.SetCoverInstance (Fin m) (Fin n)) :
    incidenceCount I ≤ n * m := by
  classical
  unfold incidenceCount
  calc
    (∑ j : Fin n, (I.sets j).card) ≤ ∑ _j : Fin n, m := by
      apply Finset.sum_le_sum
      intro j _hj
      simpa using Finset.card_le_univ (I.sets j)
    _ = n * m := by simp

/-- Exact catalysis-incidence count of the explicit source when `M > 0`:
there is one edge from the final product of each block to each of its `M`
block reactions, and one edge for each element-set incidence. -/
def sourceCatalysisIncidenceCount
    (I : MinRAFApprox.SetCoverInstance (Fin m) (Fin n)) (M : Nat) : Nat :=
  n * M + incidenceCount I

/-- Complete sparse-list encoding size.  The summands count, respectively,
active molecules, reactions, the food entry, input incidences, output
incidences, and catalysis incidences.  For a nonempty universe the exact input
count is `2(m+nM)-1`, so the normalized total is the expression below. -/
def sourceEncodingSize
    (I : MinRAFApprox.SetCoverInstance (Fin m) (Fin n)) (M : Nat) : Nat :=
  1 + 5 * (m + n * M) + n * M + incidenceCount I

/-- Full encoding size is polynomial in the literal source parameters. -/
theorem sourceEncodingSize_le
    (I : MinRAFApprox.SetCoverInstance (Fin m) (Fin n)) (M : Nat) :
    sourceEncodingSize I M ≤ 1 + 6 * (m + n * M) + n * m := by
  have hinc := incidenceCount_le I
  unfold sourceEncodingSize
  omega

theorem amplification_le_succ (hm : 0 < m) :
    MinRAFApprox.SetCoverSource.amplification m ≤ m + 1 := by
  simp [MinRAFApprox.SetCoverSource.amplification]
  omega

/-- With the reduction's chosen amplification, the full sparse encoding has
an explicit quadratic bound in the input dimensions. -/
theorem amplified_sourceEncodingSize_le
    (I : MinRAFApprox.SetCoverInstance (Fin m) (Fin n)) (hm : 0 < m) :
    sourceEncodingSize I (MinRAFApprox.SetCoverSource.amplification m) ≤
      1 + 6 * (m + n * (m + 1)) + n * m := by
  have hM := amplification_le_succ (m := m) hm
  have hnm : n * MinRAFApprox.SetCoverSource.amplification m ≤ n * (m + 1) :=
    Nat.mul_le_mul_left n hM
  have hsize := sourceEncodingSize_le I
    (MinRAFApprox.SetCoverSource.amplification m)
  omega

end MinRAFApprox.SetCoverSource
