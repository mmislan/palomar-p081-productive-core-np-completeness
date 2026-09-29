module

public import proofs.RAF.Frankl.Semantics
public import proofs.IrrRAFEnumeration.PositiveCompletion

@[expose] public section

namespace IrrRAFEnumeration.PositiveRAFTrace

open RAF

variable {M R : Type*} [DecidableEq M]

theorem closure_mono_time (Q : CRS M R) (S : Finset R) :
    Monotone (closureAt Q S) := by
  apply monotone_nat_of_le_succ
  intro k
  exact Finset.subset_union_left

theorem closure_eq_after (Q : CRS M R) (S : Finset R) {k : Nat}
    (h : closureAt Q S (k+1) = closureAt Q S k) (t : Nat) :
    closureAt Q S (k+t) = closureAt Q S k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_succ, closureAt, ih]
    exact h

variable [Fintype M]

/-- At most one strict increase per molecule is possible. -/
theorem closure_stable (Q : CRS M R) (S : Finset R) :
    closureAt Q S (Fintype.card M + 1) = closureAt Q S (Fintype.card M) := by
  have hex : ∃ k ≤ Fintype.card M,
      closureAt Q S (k+1) = closureAt Q S k := by
    by_contra h
    push Not at h
    have hgrow : ∀ k ≤ Fintype.card M + 1, k ≤ (closureAt Q S k).card := by
      intro k
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hsub := closure_mono_time Q S (Nat.le_succ k)
        have hlt : (closureAt Q S k).card < (closureAt Q S (k+1)).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨hsub, Ne.symm (h k (by omega))⟩)
        omega
    have hlarge := hgrow (Fintype.card M + 1) (by omega)
    have hsmall := Finset.card_le_univ (closureAt Q S (Fintype.card M + 1))
    omega
  obtain ⟨k, hk, hfix⟩ := hex
  have h₁ := closure_eq_after Q S hfix (Fintype.card M - k)
  have h₂ := closure_eq_after Q S hfix (Fintype.card M + 1 - k)
  have e₁ : k + (Fintype.card M - k) = Fintype.card M := by omega
  have e₂ : k + (Fintype.card M + 1 - k) = Fintype.card M + 1 := by omega
  rw [e₁] at h₁
  rw [e₂] at h₂
  exact h₂.trans h₁.symm

theorem closure_subset_bounded (Q : CRS M R) (S : Finset R) (k : Nat) :
    closureAt Q S k ⊆ closureAt Q S (Fintype.card M) := by
  by_cases hk : k ≤ Fintype.card M
  · exact closure_mono_time Q S hk
  · have he := closure_eq_after Q S (closure_stable Q S) (k - Fintype.card M)
    have hh : Fintype.card M + (k - Fintype.card M) = k := by omega
    rw [hh] at he
    exact he.subset

/-- A finite end-row check. Catalysts are required only in the final closure. -/
def EndCheck (Q : CRS M R) (C : Catalysis M R) (S : Finset R) (D : Finset M) : Prop :=
  S.Nonempty ∧ ∀ r ∈ S, Q.inputs r ⊆ D ∧ ∃ x ∈ D, C x r

instance (Q : CRS M R) (C : Catalysis M R) [DecidableRel C]
    (S : Finset R) (D : Finset M) : Decidable (EndCheck Q C S D) := by
  unfold EndCheck
  infer_instance

theorem isRAF_iff_bounded (Q : CRS M R) (C : Catalysis M R)
    [DecidableEq R] (S : Finset R) :
    IsRAF Q C S ↔ EndCheck Q C S (closureAt Q S (Fintype.card M)) := by
  constructor
  · rintro ⟨hne, hfood, hcat⟩
    refine ⟨hne, ?_⟩
    intro r hr
    obtain ⟨k, hk⟩ := hfood r hr
    obtain ⟨x, j, hx, hcx⟩ := hcat r hr
    exact ⟨hk.trans (closure_subset_bounded Q S k),
      x, closure_subset_bounded Q S j hx, hcx⟩
  · rintro ⟨hne, hend⟩
    refine ⟨hne, ?_, ?_⟩
    · intro r hr
      exact ⟨Fintype.card M, (hend r hr).1⟩
    · intro r hr
      obtain ⟨x, hx, hc⟩ := (hend r hr).2
      exact ⟨x, Fintype.card M, hx, hc⟩

abbrev Rows (M : Type*) [Fintype M] := Fin (Fintype.card M + 1) → Finset M

/-- A polynomial number of explicit parallel closure rows. -/
def TraceCheck (Q : CRS M R) (C : Catalysis M R) (S : Finset R) (D : Rows M) : Prop :=
  D ⟨0, by omega⟩ = Q.food ∧
  (∀ i : Fin (Fintype.card M),
    D ⟨i.val+1, by omega⟩ = closureStep Q S (D ⟨i.val, by omega⟩)) ∧
  EndCheck Q C S (D ⟨Fintype.card M, by omega⟩)

instance (Q : CRS M R) (C : Catalysis M R) [DecidableRel C]
    (S : Finset R) (D : Rows M) : Decidable (TraceCheck Q C S D) := by
  unfold TraceCheck
  infer_instance

def traceCheckB (Q : CRS M R) (C : Catalysis M R) [DecidableRel C]
    (S : Finset R) (D : Rows M) : Bool := decide (TraceCheck Q C S D)

theorem traceCheckB_correct (Q : CRS M R) (C : Catalysis M R) [DecidableRel C]
    (S : Finset R) (D : Rows M) :
    traceCheckB Q C S D = true ↔ TraceCheck Q C S D := by
  simp [traceCheckB]

theorem trace_rows_exact (Q : CRS M R) (C : Catalysis M R) (S : Finset R)
    (D : Rows M) (h : TraceCheck Q C S D) (i : Fin (Fintype.card M + 1)) :
    D i = closureAt Q S i.val := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero => exact h.1
  | succ k ih =>
    have hk' : k < Fintype.card M := by omega
    rw [h.2.1 ⟨k, hk'⟩]
    exact congrArg (closureStep Q S) (ih (by omega))

/-- Sound and complete bounded positive certificates for ordinary RAFs. -/
theorem isRAF_iff_trace (Q : CRS M R) (C : Catalysis M R)
    [DecidableEq R] (S : Finset R) :
    IsRAF Q C S ↔ ∃ D : Rows M, TraceCheck Q C S D := by
  constructor
  · intro h
    refine ⟨fun i => closureAt Q S i.val, rfl, ?_, ?_⟩
    · intro i; rfl
    · exact (isRAF_iff_bounded Q C S).mp h
  · rintro ⟨D, hD⟩
    apply (isRAF_iff_bounded Q C S).mpr
    have he := trace_rows_exact Q C S D hD ⟨Fintype.card M, by omega⟩
    rw [← he]
    exact hD.2.2

/-- Dense bit rows have exactly d(d+1) bits, including the initial food row. -/
def rowBits {d : Nat} (D : Fin (d+1) → Finset (Fin d)) : List Bool :=
  (List.ofFn fun i : Fin (d+1) =>
    List.ofFn fun x : Fin d => decide (x ∈ D i)).flatten

theorem rowBits_length {d : Nat} (D : Fin (d+1) → Finset (Fin d)) :
    (rowBits D).length = (d+1)*d := by
  simp [rowBits, List.length_flatten, List.sum_ofFn, Finset.sum_const]
  ring

/-- An ordinary RAF trace and downward-hereditary exclusions; no minimality
certificate appears in this uniform completion witness relation. -/
def CompletionTraceCheck [DecidableEq R] (Q : CRS M R) (C : Catalysis M R)
    (G : Finset (Finset R)) (U S : Finset R) (D : Rows M) : Prop :=
  S ⊆ U ∧ TraceCheck Q C S D ∧ ∀ I ∈ G, ¬ I ⊆ S

instance [DecidableEq R] (Q : CRS M R) (C : Catalysis M R) [DecidableRel C]
    (G : Finset (Finset R)) (U S : Finset R) (D : Rows M) :
    Decidable (CompletionTraceCheck Q C G U S D) := by
  unfold CompletionTraceCheck
  infer_instance

def completionTraceCheckB [DecidableEq R] (Q : CRS M R) (C : Catalysis M R)
    [DecidableRel C] (G : Finset (Finset R)) (U S : Finset R) (D : Rows M) : Bool :=
  decide (CompletionTraceCheck Q C G U S D)

theorem completionTraceCheckB_correct [DecidableEq R]
    (Q : CRS M R) (C : Catalysis M R) [DecidableRel C]
    (G : Finset (Finset R)) (U S : Finset R) (D : Rows M) :
    completionTraceCheckB Q C G U S D = true ↔ CompletionTraceCheck Q C G U S D := by
  simp [completionTraceCheckB]

theorem available_iff_completion_trace [DecidableEq R]
    (Q : CRS M R) (C : Catalysis M R) (G : Finset (Finset R)) (U : Finset R) :
    PositiveCompletion.Available (IsRAF Q C) G U ↔
      ∃ S D, CompletionTraceCheck Q C G U S D := by
  constructor
  · rintro ⟨S, hSU, hS, hG⟩
    obtain ⟨D, hD⟩ := (isRAF_iff_trace Q C S).mp hS
    exact ⟨S, D, hSU, hD, hG⟩
  · rintro ⟨S, D, hSU, hD, hG⟩
    exact ⟨S, hSU, (isRAF_iff_trace Q C S).mpr ⟨D, hD⟩, hG⟩

/-- Reaction-mask and dense closure-row encoding of a positive certificate. -/
def certificateBits {d m : Nat} (S : Finset (Fin m))
    (D : Fin (d+1) → Finset (Fin d)) : List Bool :=
  (List.ofFn fun r : Fin m => decide (r ∈ S)) ++ rowBits D

theorem certificateBits_length {d m : Nat} (S : Finset (Fin m))
    (D : Fin (d+1) → Finset (Fin d)) :
    (certificateBits S D).length = m + (d+1)*d := by
  simp [certificateBits, rowBits_length]

end IrrRAFEnumeration.PositiveRAFTrace
