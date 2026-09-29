module

public import proofs.UnconstrainedPACDetection.VerifierFieldCardinalityCheck

@[expose] public section

namespace UnconstrainedPACDetection.VerifierFieldCardinality
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierFieldCardinalityCount (frame frame_parked)

def exactState (inp₀ : Tape) (base : Fin 11 → Tape) (v : Bool) : Complexity.TM.TapePred 11 :=
  fun inp work out => inp = inp₀ ∧ work = base ∧ out = one .start v
def cleared (base : Fin 11 → Tape) : Fin 11 → Tape := Function.update base 4 (regTape 0)
def checkMachine : TM 11 := seqTM (clearRegTM 4) VerifierFieldCardinalityCheck.compareMachine
def machine : TM 11 := seqTM VerifierFieldCardinalityCount.machine checkMachine

theorem one_acc (v : Bool) : OutAcc [v] (one .start v) :=
  VerifierEntityLoopBody.acc_of_prefix _ _ (VerifierVerdictCommit.one_prefix _ _) rfl

theorem cleared_parked (base : Fin 11 → Tape) (hp : ∀ j, Parked (base j)) :
    ∀ j, Parked (cleared base j) := by
  intro j; by_cases hj : j = 4
  · subst j; exact parked_regTape 0
  · simpa only [cleared,Function.update_of_ne hj] using hp j

theorem stable (inp₀ : Tape) (base : Fin 11 → Tape) (v : Bool)
    (hi : Parked inp₀) (hp : ∀ j, Parked (base j)) : ∀ inp work out,
    exactState inp₀ base v inp work out → exactState inp₀ base v (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out ⟨hin,hw,ho⟩
  subst inp; subst work; subst out
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start
    (fun j => (hp j).read_ne_start) (one_acc v).parked.read_ne_start
  exact ⟨hi',hw',ho'⟩

theorem clear_hoare (inp₀ : Tape) (base : Fin 11 → Tape) (v : Bool)
    (hi : Parked inp₀) (hp : ∀ j, Parked (base j)) (h4 : base 4 = regTape 1) :
    (clearRegTM (4 : Fin 11)).HoareTime (exactState inp₀ base v) (exactState inp₀ (cleared base) v) 6 := by
  rintro inp work out ⟨hin,hw,ho⟩
  subst inp; subst work; subst out
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := clearRegTM_hoareTime (4 : Fin 11) 1 inp₀ base [v]
    hi (fun j _ => hp j) h4 inp₀ base (one .start v) ⟨rfl,rfl,one_acc v⟩
  exact ⟨d,t,ht,hr,hh,hdi,hdw,hdo.eq (one_acc v)⟩

theorem check_hoare (q target : ℕ) (v : Bool) (inp₀ : Tape) (base : Fin 11 → Tape)
    (hi : Parked inp₀) (hp : ∀ j, Parked (base j))
    (h0 : base 0 = regTape q) (h10 : base 10 = regTape target) (h4 : base 4 = regTape 1) :
    checkMachine.HoareTime (exactState inp₀ base v)
      (VerifierFieldCardinalityCheck.after q target v inp₀ (cleared base)) (max q target+11) := by
  have hc := clear_hoare inp₀ base v hi hp h4
  have he := VerifierFieldCardinalityCheck.comparison_hoare q target v inp₀ (cleared base)
    hi.read_ne_start (cleared_parked base hp) (by exact h0) (by exact h10)
    (by exact (VerifierCountPrepare.unary_eq_reg 0).symm)
  have h := seqTM_hoareTime _ _ hc (stable inp₀ (cleared base) v hi (cleared_parked base hp)) he
  exact h.mono_bound (by omega)

theorem count_hoare (m n L : ℕ) (v : Bool) (inp₀ : Tape) (base : Fin 11 → Tape)
    (hi : Parked inp₀) (hp : ∀ j, Parked (base j))
    (h5 : base 5 = regTape m) (h8 : base 8 = regTape n) (h10 : base 10 = regTape 0)
    (hm : m ≤ L) (hn : n ≤ L) : VerifierFieldCardinalityCount.machine.HoareTime
    (exactState inp₀ base v) (exactState inp₀ (frame base (2*m*n+2)) v)
    (4*opBudget (2*(L+1)^2)+3) := by
  rintro inp work out ⟨hin,hw,ho⟩
  subst inp; subst work; subst out
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := VerifierFieldCardinalityCount.validation_hoare
    m n L inp₀ base [v] hi hp h5 h8 h10 hm hn inp₀ base (one .start v) ⟨rfl,rfl,one_acc v⟩
  exact ⟨d,t,ht,hr,hh,hdi,hdw,hdo.eq (one_acc v)⟩

theorem validation_hoare (q m n S L : ℕ) (v : Bool) (inp₀ : Tape) (base : Fin 11 → Tape)
    (hi : Parked inp₀) (hp : ∀ j, Parked (base j))
    (h0 : base 0 = regTape q) (h4 : base 4 = regTape 1)
    (h5 : base 5 = regTape m) (h8 : base 8 = regTape n) (h10 : base 10 = regTape 0)
    (hq : q ≤ S) (hm : m ≤ L) (hn : n ≤ L) : machine.HoareTime
    (exactState inp₀ base v)
    (VerifierFieldCardinalityCheck.after q (2*m*n+2) v inp₀ (cleared (frame base (2*m*n+2))))
    (4*opBudget (2*(L+1)^2)+S+2*(L+1)^2+15) := by
  have hc := count_hoare m n L v inp₀ base hi hp h5 h8 h10 hm hn
  have he := check_hoare q (2*m*n+2) v inp₀ (frame base (2*m*n+2)) hi
    (frame_parked base hp _) (by exact h0) (by rfl) (by exact h4)
  have h := seqTM_hoareTime _ _ hc (stable inp₀ (frame base (2*m*n+2)) v hi (frame_parked base hp _)) he
  have hmn : m*n ≤ L*L := Nat.mul_le_mul hm hn
  have hb : 2*m*n+2 ≤ 2*(L+1)^2 := by nlinarith
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierFieldCardinality
