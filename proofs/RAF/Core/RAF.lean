module

public import proofs.RAF.Core.Closure

@[expose] public section

namespace RAF

variable {M R : Type*} [DecidableEq M] [DecidableEq R]

def FoodGenerated (Q : CRS M R) (S : Finset R) : Prop :=
  ∀ r ∈ S, ∃ k, Q.inputs r ⊆ closureAt Q S k

def CatalyzedFromClosure (Q : CRS M R) (C : Catalysis M R)
    (S : Finset R) (r : R) : Prop :=
  ∃ x k, x ∈ closureAt Q S k ∧ C x r

def ReflexivelyAutocatalytic (Q : CRS M R) (C : Catalysis M R)
    (S : Finset R) : Prop :=
  ∀ r ∈ S, CatalyzedFromClosure Q C S r

def IsRAF (Q : CRS M R) (C : Catalysis M R) (S : Finset R) : Prop :=
  S.Nonempty ∧ FoodGenerated Q S ∧ ReflexivelyAutocatalytic Q C S

end RAF
