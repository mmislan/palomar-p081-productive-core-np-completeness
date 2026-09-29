module

public import proofs.MinRAFApprox.Gadgets.BlockCoverNormalForm
public import proofs.RAF.Frankl.Antimatroid

@[expose] public section

namespace MinRAFApprox

open RAF RAF.Frankl Reaction

/-- Molecules of the literal amplified source.  A single food molecule is
reused; `y` marks progress through the mandatory gate chain and `z` marks
progress through a set block. -/
inductive Molecule (n M : Nat)
  | food
  | y (i : Nat)
  | z (j : Fin n) (k : Fin M)
  deriving DecidableEq

namespace SetCoverSource

variable {m n M : Nat}

def predFin {N : Nat} (k : Fin N) : Fin N :=
  ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le k.val 1) k.isLt⟩

def lastFin (N : Nat) (hN : 0 < N) : Fin N := ⟨N - 1, by omega⟩

def crs (m n M : Nat) :
    CRS (Molecule n M) (Reaction (Fin m) (Fin n) (Fin M)) where
  food := {Molecule.food}
  inputs
    | gate i =>
        if i.val = 0 then {Molecule.food}
        else {Molecule.food, Molecule.y (i.val - 1)}
    | block j k =>
        if k.val = 0 then {Molecule.food, Molecule.y (m - 1)}
        else {Molecule.food, Molecule.z j (predFin k)}
  outputs
    | gate i => {Molecule.y i.val}
    | block j k => {Molecule.z j k}

/-- Every reaction of block `j` is catalyzed by the final product of that
block.  Final block products also catalyze exactly the gates covered by the
corresponding set. -/
def catalysis (I : SetCoverInstance (Fin m) (Fin n)) :
    Catalysis (Molecule n M) (Reaction (Fin m) (Fin n) (Fin M))
  | Molecule.z j l, gate i => l.val = M - 1 ∧ i ∈ I.sets j
  | Molecule.z j l, block j' _ => l.val = M - 1 ∧ j = j'
  | _, _ => False

theorem y_origin
    (S : Finset (Reaction (Fin m) (Fin n) (Fin M))) {t k : Nat}
    (hy : Molecule.y t ∈ closureAt (crs m n M) S k) :
    ∃ i : Fin m, gate (J := Fin n) (K := Fin M) i ∈ S ∧ i.val = t := by
  rcases mem_closureAt_imp_food_or_output (crs m n M) S hy with hfood | ⟨r, hr, hout⟩
  · change Molecule.y t ∈ ({Molecule.food} : Finset (Molecule n M)) at hfood
    simp at hfood
  · cases r with
    | gate i =>
        change Molecule.y t ∈ ({Molecule.y i.val} : Finset (Molecule n M)) at hout
        simp at hout
        exact ⟨i, hr, hout.symm⟩
    | block j l =>
        change Molecule.y t ∈ ({Molecule.z j l} : Finset (Molecule n M)) at hout
        simp at hout

theorem z_origin
    (S : Finset (Reaction (Fin m) (Fin n) (Fin M))) {j : Fin n} {l : Fin M} {k : Nat}
    (hz : Molecule.z j l ∈ closureAt (crs m n M) S k) :
    block (U := Fin m) j l ∈ S := by
  rcases mem_closureAt_imp_food_or_output (crs m n M) S hz with hfood | ⟨r, hr, hout⟩
  · change Molecule.z j l ∈ ({Molecule.food} : Finset (Molecule n M)) at hfood
    simp at hfood
  · cases r with
    | gate i =>
        change Molecule.z j l ∈ ({Molecule.y i.val} : Finset (Molecule n M)) at hout
        simp at hout
    | block j' l' =>
        change Molecule.z j l ∈ ({Molecule.z j' l'} : Finset (Molecule n M)) at hout
        simp at hout
        rcases hout with ⟨rfl, rfl⟩
        exact hr

end SetCoverSource

end MinRAFApprox
