module

public import proofs.IrrRAFEnumeration.SATBitEncoding

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open RAF SATCompletion CircuitSource

/-- A known ordering of the baseline, computed without a SAT decision. -/
def baselineRows (n m : Nat) :=
  List.ofFn (fun i : Fin n => sourceSet (m := m) (pair i))

theorem baselineRows_family (n m : Nat) :
    (baselineRows n m).toFinset = baseline n m := by
  ext S
  simp [baselineRows, baseline]

theorem baselineRows_nodup (n m : Nat) : (baselineRows n m).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  exact pair_injective (sourceSet_injective h)

/-- R bits per reaction subset; R is supplied by the source header. -/
def baselineBody (n m : Nat) : List Bool :=
  List.ofFn (fun k : Fin (n * reactionCount n m) =>
    let ix : Fin n × Fin (reactionCount n m) := finProdFinEquiv.symm k
    decide ((reactionCode _ _).symm ix.2 ∈ sourceSet (m := m) (pair ix.1)))

def baselineBits (n m : Nat) : List Bool :=
  List.replicate n true ++ [false] ++ baselineBody n m

theorem baselineBits_header (n m : Nat) :
    readUnary (baselineBits n m) = (n, baselineBody n m) := by
  simpa [baselineBits, List.append_assoc] using readUnary_prefix n (baselineBody n m)

def readBaseline (n m : Nat) (i : Fin n)
    (r : Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m))) : Bool :=
  (baselineBody n m).get
    ⟨(finProdFinEquiv (i, reactionCode _ _ r)).val, by
      simpa only [baselineBody, List.length_ofFn, reactionCount] using
        (finProdFinEquiv (i, reactionCode _ _ r)).isLt⟩

theorem readBaseline_iff (n m : Nat) (i : Fin n)
    (r : Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m))) :
    readBaseline n m i r = true ↔ r ∈ sourceSet (m := m) (pair i) := by
  simp only [readBaseline, baselineBody, List.get_eq_getElem, List.getElem_ofFn]
  change decide ((reactionCode _ _).symm
    (finProdFinEquiv.symm (finProdFinEquiv (i, reactionCode _ _ r))).2 ∈
    sourceSet (m := m) (pair
      (finProdFinEquiv.symm (finProdFinEquiv (i, reactionCode _ _ r))).1)) = true ↔ _
  simp only [Equiv.symm_apply_apply, decide_eq_true_eq]

theorem baselineBits_length (n m : Nat) :
    (baselineBits n m).length = n+1+n*reactionCount n m := by
  simp [baselineBits, baselineBody]
  omega

theorem baselineBits_polynomial (n m : Nat) :
    (baselineBits n m).length ≤ 20*(n+m+1)^3 := by
  rw [baselineBits_length]
  simp only [reactionCount, step_card, Choice,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  nlinarith [Nat.zero_le (n^3), Nat.zero_le (m^3),
    Nat.zero_le (n^2*m), Nat.zero_le (n*m^2)]

/-- A concrete polynomial-length input and known duplicate-free output list.
Completeness of this actual baseline remains exactly Boolean CNF UNSAT. -/
theorem sat_reduction_with_bit_encodings {n m : Nat} (hn : 2 ≤ n)
    (Φ : Fin m → Finset (Choice n)) :
    (sourceBits Φ).length ≤ 500*(n+m+1)^4 ∧
    (baselineBits n m).length ≤ 20*(n+m+1)^3 ∧
    (baselineRows n m).Nodup ∧
    (baselineRows n m).toFinset ⊆ irrRAFFamily (crs (rules Φ)) catalysis ∧
    ((baselineRows n m).toFinset = irrRAFFamily (crs (rules Φ)) catalysis ↔
      ¬ ∃ f : Fin n → Bool, Satisfies Φ f) := by
  refine ⟨sourceBits_polynomial Φ, baselineBits_polynomial n m,
    baselineRows_nodup n m, ?_, ?_⟩
  · rw [baselineRows_family]
    exact baseline_subset_irrRAFFamily hn Φ
  · rw [baselineRows_family, eq_comm]
    exact (sat_reduction_with_polynomial_source hn Φ).2.2.2.2

end IrrRAFEnumeration.SATSource
