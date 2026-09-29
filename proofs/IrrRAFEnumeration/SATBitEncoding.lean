module

public import proofs.IrrRAFEnumeration.SATResolution

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open RAF SATCompletion CircuitSource

/-- The finite molecule tags are encoded by offsets, including private markers. -/
def moleculeCode (w q : Nat) : Molecule w q ≃ Fin (1+(w+(q+1))) :=
  (moleculeEquiv w q).trans ((Equiv.sumCongr unitCode
    ((Equiv.sumCongr (Equiv.refl (Fin w)) (Equiv.refl (Fin (q+1)))).trans
      finSumFinEquiv)).trans finSumFinEquiv)

def moleculeCount (n m : Nat) :=
  1+(Fintype.card (Wire n m)+(Fintype.card (Step n m)+1))

def reactionCount (n m : Nat) :=
  Fintype.card (Choice n)+(Fintype.card (Step n m)+1)

def reactionCode (n q : Nat) : Reaction n q ≃ Fin (n+(q+1)) := finSumFinEquiv

/-- One food column and three reaction matrices: inputs, outputs, catalysts. -/
abbrev Slot (M R : Nat) := Fin M ⊕ (Fin R × (Fin 3 × Fin M))

def slotCode (M R : Nat) : Slot M R ≃ Fin (M+R*(3*M)) :=
  (Equiv.sumCongr (Equiv.refl (Fin M))
    ((Equiv.prodCongr (Equiv.refl (Fin R)) finProdFinEquiv).trans
      finProdFinEquiv)).trans finSumFinEquiv

def datum {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    Slot (moleculeCount n m) (reactionCount n m) → Bool
  | .inl x => decide ((moleculeCode _ _).symm x ∈ (crs (rules Φ)).food)
  | .inr (r, c, x) =>
      let rx := (reactionCode _ _).symm r
      let mol := (moleculeCode _ _).symm x
      if c = 0 then decide (mol ∈ (crs (rules Φ)).inputs rx)
      else if c = 1 then decide (mol ∈ (crs (rules Φ)).outputs rx)
      else decide (mol = Molecule.marker (catalystIndex rx))

def sourceBody {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  List.ofFn (fun i => datum Φ ((slotCode (moleculeCount n m) (reactionCount n m)).symm i))

/-- Unary dimension headers followed by a dense Boolean incidence table.
Unary headers remain polynomial here and avoid assumptions about binary codecs. -/
def sourceBits {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  List.replicate (moleculeCount n m) true ++ [false] ++
  List.replicate (reactionCount n m) true ++ [false] ++ sourceBody Φ

def readUnary : List Bool → Nat × List Bool
  | [] => (0, [])
  | false :: bs => (0, bs)
  | true :: bs => let p := readUnary bs; (p.1+1, p.2)

theorem readUnary_prefix (k : Nat) (rest : List Bool) :
    readUnary (List.replicate k true ++ false :: rest) = (k, rest) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, readUnary, ih]

def decodeHeader (bs : List Bool) : Nat × Nat × List Bool :=
  let first := readUnary bs
  let second := readUnary first.2
  (first.1, second.1, second.2)

theorem decodeHeader_sourceBits {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    decodeHeader (sourceBits Φ) =
      (moleculeCount n m, reactionCount n m, sourceBody Φ) := by
  simp [sourceBits, decodeHeader, List.append_assoc, readUnary_prefix]

def readBody {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (z : Slot (moleculeCount n m) (reactionCount n m)) : Bool :=
  (sourceBody Φ).get ⟨((slotCode _ _) z).val, by simp [sourceBody]⟩

theorem readBody_eq {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (z : Slot (moleculeCount n m) (reactionCount n m)) :
    readBody Φ z = datum Φ z := by
  simp [readBody, sourceBody]

theorem serialized_input_iff {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (r : Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m)))
    (x : Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m))) :
    readBody Φ (.inr (reactionCode _ _ r, 0, moleculeCode _ _ x)) = true ↔
      x ∈ (crs (rules Φ)).inputs r := by
  rw [readBody_eq]
  simp [datum]

theorem serialized_output_iff {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (r : Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m)))
    (x : Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m))) :
    readBody Φ (.inr (reactionCode _ _ r, 1, moleculeCode _ _ x)) = true ↔
      x ∈ (crs (rules Φ)).outputs r := by
  rw [readBody_eq]
  simp [datum]

theorem serialized_catalyst_iff {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (r : Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m)))
    (x : Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m))) :
    readBody Φ (.inr (reactionCode _ _ r, 2, moleculeCode _ _ x)) = true ↔
      catalysis x r := by
  rw [readBody_eq]
  simp [datum, catalysis]

theorem serialized_food_iff {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (x : Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m))) :
    readBody Φ (.inl (moleculeCode _ _ x)) = true ↔ x ∈ (crs (rules Φ)).food := by
  rw [readBody_eq]
  simp [datum]

theorem sourceBits_length {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    (sourceBits Φ).length = 2*moleculeCount n m + reactionCount n m + 2 +
      reactionCount n m*(3*moleculeCount n m) := by
  simp [sourceBits, sourceBody]
  omega

theorem sourceBits_polynomial {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    (sourceBits Φ).length ≤ 500*(n+m+1)^4 := by
  rw [sourceBits_length]
  simp only [moleculeCount, reactionCount, wire_card, step_card, Choice,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  nlinarith [Nat.zero_le (n^4), Nat.zero_le (m^4), Nat.zero_le (n^3*m),
    Nat.zero_le (n*m^3), Nat.zero_le (n^2*m^2), Nat.zero_le (n^3),
    Nat.zero_le (m^3), Nat.zero_le (n^2*m), Nat.zero_le (n*m^2)]

end IrrRAFEnumeration.SATSource
