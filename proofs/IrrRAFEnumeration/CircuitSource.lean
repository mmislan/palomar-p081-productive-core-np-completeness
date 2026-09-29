module

public import proofs.RAF.Frankl.Antimatroid

@[expose] public section

namespace IrrRAFEnumeration.CircuitSource

open RAF RAF.Frankl

/-- A finite signal rule system; the last auxiliary reaction is the reset.
Circuit acyclicity and evaluation are proved separately from this literal source. -/
structure Rules (n w q : Nat) where
  inputWire : Fin n → Fin w
  needs : Fin q → Finset (Fin w)
  produces : Fin q → Finset (Fin w)
  output : Fin w

inductive Molecule (w q : Nat)
  | food
  | wire (i : Fin w)
  | marker (j : Fin (q + 1))
  deriving DecidableEq, Fintype

abbrev Reaction (n q : Nat) := Sum (Fin n) (Fin (q + 1))

def nextAux {q : Nat} (j : Fin (q + 1)) : Fin (q + 1) :=
  ⟨(j.val + 1) % (q + 1), Nat.mod_lt _ (by omega)⟩

def crs {n w q : Nat} (D : Rules n w q) :
    CRS (Molecule w q) (Reaction n q) where
  food := {Molecule.food}
  inputs
    | .inl _ => {Molecule.food}
    | .inr j => if h : j.val < q then
        (D.needs ⟨j.val, h⟩).image Molecule.wire
      else {Molecule.wire D.output}
  outputs
    | .inl i => {Molecule.wire (D.inputWire i)}
    | .inr j => insert (Molecule.marker j) <|
        if h : j.val < q then
          (D.produces ⟨j.val, h⟩).image Molecule.wire
        else Finset.univ.image Molecule.wire

def catalystIndex {n q : Nat} : Reaction n q → Fin (q + 1)
  | .inl _ => Fin.last q
  | .inr j => nextAux j

def catalysis {n w q : Nat} : Catalysis (Molecule w q) (Reaction n q) :=
  fun x r => x = Molecule.marker (catalystIndex r)

theorem marker_origin {n w q : Nat} (D : Rules n w q)
    (S : Finset (Reaction n q)) (j : Fin (q + 1)) {k : Nat}
    (h : Molecule.marker j ∈ closureAt (crs D) S k) : Sum.inr j ∈ S := by
  rcases mem_closureAt_imp_food_or_output (crs D) S h with hf | ⟨r, hr, ho⟩
  · simp [crs] at hf
  · cases r with
    | inl i => simp [crs] at ho
    | inr b =>
        have hb : j = b := by
          by_cases hlt : b.val < q <;> simpa [crs, hlt] using ho
        simpa [hb] using hr

theorem catalyst_forces_aux {n w q : Nat} (D : Rules n w q)
    {S : Finset (Reaction n q)} (hS : IsRAF (crs D) catalysis S)
    {r : Reaction n q} (hr : r ∈ S) : Sum.inr (catalystIndex r) ∈ S := by
  obtain ⟨x, k, hx, hc⟩ := hS.2.2 r hr
  change x = Molecule.marker (catalystIndex r) at hc
  subst x
  exact marker_origin D S _ hx

/-- A successor-closed subset of a finite cyclic interval is all or nothing. -/
theorem cyclic_all {q : Nat} (P : Fin (q + 1) → Prop)
    (step : ∀ j, P j → P (nextAux j)) {i : Fin (q + 1)} (hi : P i) :
    ∀ j, P j := by
  have walk : ∀ t : Nat,
      P ⟨(i.val + t) % (q + 1), Nat.mod_lt _ (by omega)⟩ := by
    intro t
    induction t with
    | zero => simpa [Nat.mod_eq_of_lt i.isLt] using hi
    | succ t ih =>
        have hs := step _ ih
        simpa only [nextAux, Nat.mod_add_mod, Nat.add_assoc] using hs
  have hz : P 0 := by
    have h := walk (q + 1 - i.val)
    have he : i.val + (q + 1 - i.val) = q + 1 := by omega
    simpa [he] using h
  intro j
  have walkZero : ∀ t : Nat, ∀ ht : t < q + 1, P ⟨t, ht⟩ := by
    intro t
    induction t with
    | zero => intro ht; exact hz
    | succ t ih =>
        intro ht
        have hs := step ⟨t, by omega⟩ (ih (by omega))
        simpa [nextAux, Nat.mod_eq_of_lt ht] using hs
  exact walkZero j.val j.isLt

/-- Every ordinary RAF of the literal construction contains every auxiliary
reaction. This excludes all spurious RAFs obtained by omitting gate branches. -/
theorem raf_contains_all_aux {n w q : Nat} (D : Rules n w q)
    {S : Finset (Reaction n q)} (hS : IsRAF (crs D) catalysis S) :
    ∀ j : Fin (q + 1), Sum.inr j ∈ S := by
  obtain ⟨r, hr⟩ := hS.1
  have hstart := catalyst_forces_aux D hS hr
  apply cyclic_all (fun j => Sum.inr j ∈ S) _ hstart
  intro j hj
  exact catalyst_forces_aux D hS hj

end IrrRAFEnumeration.CircuitSource
