module

public import proofs.IrrRAFEnumeration.CompletionQueryDecode

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

theorem header_stop_step {k : Nat} (q : Fin k) (inp : Tape)
    (work : Fin k → Tape) (out : Tape) (v : Nat)
    (hi : inp.read ≠ Γ.one) (hw : ∀ j, Parked (work j)) (ho : Parked out) :
    (headerRegTM q).step
      {state := .scan, input := inp,
       work := Function.update work q ⟨v+1,regCells v⟩, output := out} = some
      {state := .back, input := inp.move .right,
       work := Function.update work q ⟨v,regCells v⟩, output := out} := by
  have hr : (⟨v+1,regCells v⟩ : Tape).read = Γ.blank := by
    change regCells v (v+1) = Γ.blank
    exact regCells_blank (by omega)
  simp only [TM.step,headerRegTM,reduceCtorEq,↓reduceIte,ite_eq_right hi,Function.update_self,hr]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl,rfl,?_,ho.writeAndMove_readBack_idle⟩)
  funext j
  by_cases hj : j = q
  · subst j
    simp only [↓reduceIte,Function.update_self]
    rw [writeAndMove_readBack _ (by rw [hr]; decide)]
    rfl
  · simp only [hj,↓reduceIte,Function.update_of_ne hj]
    exact (hw j).writeAndMove_readBack_idle

theorem header_tolerant_correct {k : Nat} (q : Fin k) (v : Nat)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i)) (hq : work q = regTape 0)
    (hones : ∀ i, i < v → inp.cells (inp.head+i) = Γ.one)
    (hend : inp.cells (inp.head+v) ≠ Γ.one) :
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
  have hdel := header_stop_step q (advanceInput inp v) work out v hend hw hout.parked
  rw [advanceInput_move] at hdel
  have hback := header_back_run q (advanceInput inp (v+1)) work out v v
    (advanceInput_parked inp _ hp) hw hout.parked
  have hall := reachesIn_trans _ (hscan v le_rfl) (.step hdel hback)
  have hzero : C 0 =
      {state := (headerRegTM q).qstart, input := inp, work := work, output := out} := by
    dsimp [C,advanceInput]
    rw [show (⟨1,regCells 0⟩ : Tape) = work q from hq.symm,Function.update_eq_self]
    rfl
  rw [hzero] at hall
  exact ⟨_,v+(v+1+1),by omega,hall,rfl,rfl,rfl,hout⟩

theorem unary_view (z : List Bool) :
    (∀ i, i < (readUnary z).1 → z[i]? = some true) ∧
    z[(readUnary z).1]? ≠ some true ∧
    ∀ i, z[(readUnary z).1+1+i]? = (readUnary z).2[i]? := by
  induction z with
  | nil => simp [readUnary]
  | cons b z ih =>
    cases b with
    | false => simp [readUnary,Nat.add_comm]
    | true =>
      refine ⟨?_,?_,?_⟩
      · intro i hi
        cases i with
        | zero => rfl
        | succ i =>
          have hh : i < (readUnary z).1 := by simp only [readUnary] at hi; omega
          simpa using ih.1 i hh
      · simpa only [readUnary,List.getElem?_cons_succ] using ih.2.1
      · intro i
        simp only [readUnary]
        rw [show (readUnary z).1+1+1+i = ((readUnary z).1+1+i)+1 by omega,
          List.getElem?_cons_succ]
        exact ih.2.2 i

/-- A suffix view includes blank cells beyond the finite bitstring. -/
def StreamAt (inp : Tape) (z : List Bool) : Prop :=
  ∀ i, inp.cells (inp.head+i) = ((z[i]?).map Γ.ofBool).getD Γ.blank

theorem stream_after_header (inp : Tape) (z : List Bool) (h : StreamAt inp z) :
    StreamAt (advanceInput inp ((readUnary z).1+1)) (readUnary z).2 := by
  intro i
  change inp.cells (inp.head+((readUnary z).1+1)+i) = _
  rw [Nat.add_assoc,h,(unary_view z).2.2 i]

theorem header_stream_correct {k : Nat} (q : Fin k) (inp : Tape) (z : List Bool)
    (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i)) (hq : work q = regTape 0)
    (hz : StreamAt inp z) :
    (headerRegTM q).HoareTime (EmitPred inp work ys)
      (EmitPred (advanceInput inp ((readUnary z).1+1))
        (Function.update work q (regTape (readUnary z).1)) ys) (2*(readUnary z).1+2) := by
  apply header_tolerant_correct q _ inp work ys hp hw hq
  · intro i hi
    rw [hz,(unary_view z).1 i hi]
    rfl
  · rw [hz]
    have hn := (unary_view z).2.1
    cases he : z[(readUnary z).1]? with
    | none => simp
    | some b =>
      cases b with
      | false => simp [Γ.ofBool]
      | true => exact False.elim (hn he)

end IrrRAFEnumeration.CompletionQuery
