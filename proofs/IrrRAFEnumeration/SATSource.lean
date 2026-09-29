module

public import proofs.IrrRAFEnumeration.CircuitEvaluation
public import proofs.IrrRAFEnumeration.SATLabels

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource

def needs {n m : Nat} : Step n m → Finset (Wire n m)
  | .conflict i => {.literal (i, false), .literal (i, true)}
  | .coverage x => {.literal x}
  | .clause _ x => {.literal x}
  | .finish => Finset.univ.image Wire.covered ∪ Finset.univ.image Wire.clause

def produces {n m : Nat} (Φ : Fin m → Finset (Choice n)) : Step n m → Finset (Wire n m)
  | .conflict _ => {.output}
  | .coverage x => {.covered x.1}
  | .clause j x => if x ∈ Φ j then {.clause j} else ∅
  | .finish => {.output}

def encodeInputs {n : Nat} (T : Finset (Choice n)) := T.image (inputCode n)

def rules {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    Rules (Fintype.card (Choice n)) (Fintype.card (Wire n m)) (Fintype.card (Step n m)) where
  inputWire i := wireCode n m (.literal ((inputCode n).symm i))
  needs j := (needs ((stepCode n m).symm j)).image (wireCode n m)
  produces j := (produces Φ ((stepCode n m).symm j)).image (wireCode n m)
  output := wireCode n m .output

def family {n m : Nat} (Φ : Fin m → Finset (Choice n)) := Finset.univ.image Φ

def Meaning {n m : Nat} (Φ : Fin m → Finset (Choice n)) (T : Finset (Choice n)) :
    Wire n m → Prop
  | .literal x => x ∈ T
  | .covered i => ∃ b, (i,b) ∈ T
  | .clause j => ∃ x ∈ Φ j, x ∈ T
  | .output => eval (family Φ) T

theorem step_preserves {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (T : Finset (Choice n)) (s : Step n m)
    (h : ∀ v ∈ needs s, Meaning Φ T v) {v : Wire n m}
    (hv : v ∈ produces Φ s) : Meaning Φ T v := by
  cases s with
  | conflict i =>
      have heq : v = .output := by simpa [produces] using hv
      subst v
      exact Or.inl ⟨i, h (.literal (i,false)) (by simp [needs]),
        h (.literal (i,true)) (by simp [needs])⟩
  | coverage x =>
      have heq : v = .covered x.1 := by simpa [produces] using hv
      subst v
      exact ⟨x.2, h (.literal x) (by simp [needs])⟩
  | clause j x =>
      by_cases hx : x ∈ Φ j
      · have heq : v = .clause j := by simpa [produces, hx] using hv
        subst v
        exact ⟨x, hx, h (.literal x) (by simp [needs])⟩
      · simp [produces, hx] at hv
  | finish =>
      have heq : v = .output := by simpa [produces] using hv
      subst v
      refine Or.inr ⟨?_, ?_⟩
      · intro i
        exact h (.covered i) (by simp [needs])
      · intro C hC
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hC
        exact h (.clause j) (by simp [needs])

theorem derives_sound {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (T : Finset (Choice n)) {v : Fin (Fintype.card (Wire n m))}
    (h : Derives (rules Φ) (encodeInputs T) v) :
    Meaning Φ T ((wireCode n m).symm v) := by
  induction h with
  | input i hi =>
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
      simpa [rules, Meaning] using hx
  | rule j _ v hv ih =>
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
      simp only [Equiv.symm_apply_apply]
      apply step_preserves Φ T ((stepCode n m).symm j) _ hs
      intro u hu
      have hh := ih (wireCode n m u) (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
      simpa using hh

def Derived {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (T : Finset (Choice n)) (v : Wire n m) : Prop :=
  Derives (rules Φ) (encodeInputs T) (wireCode n m v)

theorem derive_input {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (T : Finset (Choice n)) {x : Choice n} (hx : x ∈ T) : Derived Φ T (.literal x) := by
  have hi : inputCode n x ∈ encodeInputs T := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have h := Derives.input (D := rules Φ) (inputCode n x) hi
  simpa [Derived, rules] using h

theorem derive_step {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (T : Finset (Choice n)) (s : Step n m)
    (h : ∀ v ∈ needs s, Derived Φ T v) {v : Wire n m}
    (hv : v ∈ produces Φ s) : Derived Φ T v := by
  apply Derives.rule (stepCode n m s)
  · intro u hu
    change u ∈ (needs ((stepCode n m).symm (stepCode n m s))).image (wireCode n m) at hu
    simp only [Equiv.symm_apply_apply] at hu
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    exact h a ha
  · change wireCode n m v ∈
      (produces Φ ((stepCode n m).symm (stepCode n m s))).image (wireCode n m)
    simp only [Equiv.symm_apply_apply]
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

theorem eval_imp_derived_output {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (T : Finset (Choice n)) (h : eval (family Φ) T) : Derived Φ T .output := by
  rcases h with ⟨i, hf, ht⟩ | ⟨hc, hh⟩
  · apply derive_step Φ T (.conflict i) _ (by simp [produces])
    intro v hv
    simp only [needs, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact derive_input Φ T hf
    · exact derive_input Φ T ht
  · apply derive_step Φ T .finish _ (by simp [produces])
    intro v hv
    simp only [needs, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · obtain ⟨b, hb⟩ := hc i
      apply derive_step Φ T (.coverage (i,b)) _ (by simp [produces])
      intro u hu
      have heq : u = .literal (i,b) := by simpa [needs] using hu
      subst u
      exact derive_input Φ T hb
    · obtain ⟨x, hx, hxt⟩ := hh (Φ j) (by simp [family])
      apply derive_step Φ T (.clause j x) _ (by simp [produces, hx])
      intro u hu
      have heq : u = .literal x := by simpa [needs] using hu
      subst u
      exact derive_input Φ T hxt

/-- Concrete SAT-to-rule docking, with no assumed evaluation equivalence. -/
theorem accepts_encode_iff_eval {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (T : Finset (Choice n)) : Accepts (rules Φ) (encodeInputs T) ↔ eval (family Φ) T := by
  rw [accepts_iff_derives]
  constructor
  · intro h
    have hs := derives_sound Φ T h
    simpa [rules, Meaning] using hs
  · exact eval_imp_derived_output Φ T

end IrrRAFEnumeration.SATSource
