module

public import proofs.Complexitylib.Models.TuringMachine.Registers.Horner
public import proofs.Complexitylib.Models.TuringMachine.Registers.InputLen

@[expose] public section

namespace IrrRAFEnumeration.PolynomialClockSetup
open Complexity Complexity.TM

def valueCap (p : Polynomial Nat) (x : Nat) :=
  x + ((polyCoeffs p).sum+1)*(x+1)^(p.natDegree+1)

def setupTime (p : Polynomial Nat) (x : Nat) :=
  1+1+((2*x+4)+1+(opBudget (valueCap p x)+1+
    ((p.natDegree+1)*(layerBudget (valueCap p x)+1)+1)))

def setupTM (p : Polynomial Nat) : TM 3 :=
  seqTM bumpTM (seqTM (inputLenRegTM 0) (polyEvalTM 0 1 2 p))

def initialWork : Fin 3 → Tape := fun _ => regTape 0
def lengthWork (x : Nat) := Function.update initialWork 0 (regTape x)
def clockWork (p : Polynomial Nat) (x : Nat) :=
  Function.update (Function.update (lengthWork x) 2 (regTape (p.eval x))) 1
    (regTape (p.eval x))

theorem lengthWork_parked (x : Nat) : ∀ i, Parked (lengthWork x i) := by
  intro i
  by_cases hi : i = 0
  · subst i
    simpa only [lengthWork,Function.update_self] using parked_regTape x
  · rw [lengthWork,Function.update_of_ne hi]
    exact parked_regTape 0

/-- Concrete initialization from the real input and blank tapes. It measures
input length, evaluates a fixed natural-coefficient polynomial in unary, and
parks that clock in work tape 1 while preserving input and empty output. -/
theorem setupTM_correct (p : Polynomial Nat) (x : List Bool) :
    (setupTM p).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred ⟨1,(Tape.init (x.map Γ.ofBool)).cells⟩ (clockWork p x.length) [])
      (setupTime p x.length) := by
  let input : Tape := ⟨1,(Tape.init (x.map Γ.ofBool)).cells⟩
  have hi : Parked input := parked_init_input x
  have h0 : ∀ i, Parked (initialWork i) := fun _ => parked_regTape 0
  have h1 := lengthWork_parked x.length
  have hcap : x.length ≤ valueCap p x.length := Nat.le_add_right _ _
  have hpre : ∀ k, k ≤ p.natDegree+1 →
      hornerFold x.length ((polyCoeffs p).take k) 0 ≤ valueCap p x.length := by
    intro k _
    have h := hornerFold_take_le x.length (polyCoeffs p) k
    rw [polyCoeffs_length] at h
    exact h.trans (Nat.le_add_left _ _)
  have hpoly := polyEvalTM_hoareTime (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    p (valueCap p x.length) x.length 0 0 hcap (Nat.zero_le _) (Nat.zero_le _) hpre
    input (lengthWork x.length) [] hi h1
    (by simp [lengthWork]) (by simp [lengthWork,initialWork])
    (by simp [lengthWork,initialWork])
  have hlen := inputLenRegTM_hoareTime (0 : Fin 3) x initialWork []
    (fun i _ => h0 i) rfl
  have hrest := seqTM_hoareTime _ _ hlen (emitPred_transition hi h1 []) hpoly
  have hb : (bumpTM (n := 3)).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred input initialWork []) 1 := by
    apply (bumpTM_hoareTime x).consequence (fun _ _ _ h => h) _ (le_refl _)
    rintro inp work out ⟨hin,hwork,hout⟩
    exact ⟨hin,funext (fun i => (hwork i).eq_regT),hout⟩
  exact seqTM_hoareTime _ _ hb (emitPred_transition hi h0 []) hrest

/-- The clock-setup bound is the evaluation of an explicit fixed polynomial. -/
noncomputable def setupPolynomial (p : Polynomial Nat) : Polynomial Nat :=
  let cap := Polynomial.X + Polynomial.C ((polyCoeffs p).sum+1)*
    (Polynomial.X+1)^(p.natDegree+1)
  let op := Polynomial.C 32*((cap+2)*(cap+2)*(cap+2))
  1+1+((2*Polynomial.X+4)+1+(op+1+
    (Polynomial.C (p.natDegree+1)*((4*op+3)+1)+1)))

theorem setupTime_eq_polynomial (p : Polynomial Nat) (x : Nat) :
    setupTime p x = (setupPolynomial p).eval x := by
  unfold setupTime setupPolynomial valueCap opBudget layerBudget
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one]
  rfl

end IrrRAFEnumeration.PolynomialClockSetup
