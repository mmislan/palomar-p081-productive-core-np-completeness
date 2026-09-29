module

public import proofs.RAF.Core.CRS

@[expose] public section

namespace RAF

variable {M R : Type*} [DecidableEq M]

def Enabled (Q : CRS M R) (available : Finset M) (r : R) : Prop :=
  Q.inputs r ⊆ available

instance enabledDecidable (Q : CRS M R) (available : Finset M) (r : R) :
    Decidable (Enabled Q available r) := by
  unfold Enabled
  infer_instance

def closureStep (Q : CRS M R) (S : Finset R) (available : Finset M) : Finset M :=
  available ∪ S.biUnion (fun r => if Enabled Q available r then Q.outputs r else ∅)

def closureAt (Q : CRS M R) (S : Finset R) : Nat → Finset M
  | 0 => Q.food
  | k + 1 => closureStep Q S (closureAt Q S k)

def SeedReaction (Q : CRS M R) (r : R) : Prop := Enabled Q Q.food r

lemma closureStep_eq_food_of_no_seed (Q : CRS M R) (S : Finset R)
    (h : ∀ r ∈ S, ¬ SeedReaction Q r) : closureStep Q S Q.food = Q.food := by
  have hempty :
      S.biUnion (fun r => if Enabled Q Q.food r then Q.outputs r else ∅) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    simp only [Finset.mem_biUnion] at hx
    obtain ⟨r, hr, hxout⟩ := hx
    have hn : ¬ Enabled Q Q.food r := h r hr
    simp [hn] at hxout
  simp [closureStep, hempty]

lemma closureAt_eq_food_of_no_seed (Q : CRS M R) (S : Finset R)
    (h : ∀ r ∈ S, ¬ SeedReaction Q r) : ∀ k, closureAt Q S k = Q.food := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [closureAt, ih, closureStep_eq_food_of_no_seed Q S h]

end RAF
