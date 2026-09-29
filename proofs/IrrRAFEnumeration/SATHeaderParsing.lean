module

public import proofs.IrrRAFEnumeration.SATHeaderMachine

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def advanceInput (inp : Tape) (d : Nat) : Tape := ⟨inp.head+d,inp.cells⟩

theorem advanceInput_parked (inp : Tape) (d : Nat) (hp : Parked inp) :
    Parked (advanceInput inp d) := ⟨by dsimp [advanceInput]; have := hp.1; omega, hp.2⟩

theorem advanceInput_move (inp : Tape) (d : Nat) :
    (advanceInput inp d).move .right = advanceInput inp (d+1) := by
  apply Tape.ext
  · simp [advanceInput, Tape.move, Nat.add_assoc]
  · rfl

/-- From an ordinary input position and empty register, parse one complete
unary header in a linear number of actual tape transitions. -/
theorem headerRegTM_correct {k : Nat} (q : Fin k) (v : Nat)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i)) (hq : work q = regTape 0)
    (hones : ∀ i, i < v → inp.cells (inp.head+i) = Γ.one)
    (hend : inp.cells (inp.head+v) = Γ.zero) :
    (headerRegTM q).HoareTime (EmitPred inp work ys)
      (EmitPred (advanceInput inp (v+1)) (Function.update work q (regTape v)) ys)
      (2*v+2) := by
  rintro inp' work' out ⟨hi,hwork,hout⟩
  subst inp'
  subst work'
  let C : Nat → Cfg k (headerRegTM q).Q := fun i =>
    {state := .scan, input := advanceInput inp i,
      work := Function.update work q ⟨i+1,regCells i⟩, output := out}
  have hscan : ∀ i, i ≤ v → (headerRegTM q).reachesIn i (C 0) (C i) := by
    intro i
    induction i with
    | zero => intro _; exact .zero
    | succ i ih =>
        intro hle
        have hs := header_scan_step q (advanceInput inp i) work out i
          (hones i (by omega)) hw hout.parked
        rw [advanceInput_move] at hs
        exact reachesIn_trans _ (ih (by omega)) (.step hs .zero)
  have hdel := header_delimiter_step q (advanceInput inp v) work out v
    hend hw hout.parked
  rw [advanceInput_move] at hdel
  have hback := header_back_run q (advanceInput inp (v+1)) work out v v
    (advanceInput_parked inp _ hp) hw hout.parked
  have hall := reachesIn_trans _ (hscan v le_rfl) (.step hdel hback)
  have hzero : C 0 =
      {state := (headerRegTM q).qstart, input := inp, work := work, output := out} := by
    dsimp [C, advanceInput]
    rw [show (⟨1,regCells 0⟩ : Tape) = work q from hq.symm, Function.update_eq_self]
    rfl
  rw [hzero] at hall
  exact ⟨_,v+(v+1+1),by omega,hall,rfl,rfl,rfl,hout⟩

end IrrRAFEnumeration.SATSource
