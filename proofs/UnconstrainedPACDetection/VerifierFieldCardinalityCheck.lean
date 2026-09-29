module

public import proofs.UnconstrainedPACDetection.VerifierFieldCardinalityCount

@[expose] public section

namespace UnconstrainedPACDetection.VerifierFieldCardinalityCheck
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)

def permutation : Equiv.Perm (Fin 11) := (Equiv.swap 1 10).trans (Equiv.swap 2 4)
def placed : TM 11 := placeWorkTM 0 8 VerifierEqualityCommit.machine
def compareMachine : TM 11 := VerifierWorkPermutation.machine placed permutation
def changed (base : Fin 11 → Tape) (a b : Tape) := Function.update (Function.update base 0 a) 10 b
def after (q target : ℕ) (v : Bool) (inp₀ : Tape) (base : Fin 11 → Tape) :
    Complexity.TM.TapePred 11 := fun inp work out => inp = inp₀ ∧ ∃ a b,
      a.HasBinarySuffix [] ∧ b.HasBinarySuffix [] ∧ a.cells = (regTape q).cells ∧
      b.cells = (regTape target).cells ∧ work = changed base a b ∧
      out = one .start (VerifierBinaryEquality.compare true
        (List.replicate target true) (List.replicate q true) && v)

theorem comparison_hoare (q target : ℕ) (v : Bool) (inp₀ : Tape) (base : Fin 11 → Tape)
    (hi : inp₀.read ≠ .start) (hp : ∀ j, Parked (base j))
    (h0 : base 0 = regTape q) (h10 : base 10 = regTape target) (h4 : base 4 = wordTape []) :
    compareMachine.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = base ∧ out = one .start v)
      (after q target v inp₀ base) (max q target+4) := by
  rintro inp work out ⟨hin,hw,ho⟩
  subst inp; subst work; subst out
  have h0' : base 0 = wordTape (List.replicate q true) := h0.trans (VerifierCountPrepare.unary_eq_reg q).symm
  have h10' : base 10 = wordTape (List.replicate target true) := h10.trans (VerifierCountPrepare.unary_eq_reg target).symm
  obtain ⟨d,t,ht,hr,hh,hdi,ha,hb,hac,hbc,hd2,hdo⟩ := VerifierEqualityCommit.validation_hoare
    (List.replicate target true) (List.replicate q true) v inp₀ hi inp₀
    ![wordTape (List.replicate q true),wordTape (List.replicate target true),wordTape []]
    (one .start v) ⟨rfl,rfl,rfl⟩
  let unperm : Fin 11 → Tape := fun j => base (permutation j)
  have hplaced := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierEqualityCommit.machine 0 8 unperm hr (by intro j _; exact (hp _).read_ne_start)
  have hrun := VerifierWorkPermutation.run_commute placed permutation hplaced
  let embed := fun c : Cfg 3 VerifierEqualityCommit.machine.Q =>
    VerifierWorkPermutation.wrap placed permutation (placeWorkCfg VerifierEqualityCommit.machine 0 8 unperm c)
  have he : embed ⟨VerifierEqualityCommit.machine.qstart,inp₀,
      ![wordTape (List.replicate q true),wordTape (List.replicate target true),wordTape []],one .start v⟩ =
      (⟨compareMachine.qstart,inp₀,base,one .start v⟩ : Cfg 11 compareMachine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> first | rfl | exact h0'.symm | exact h10'.symm | exact h4.symm
    · rfl
  change compareMachine.reachesIn t (embed _) (embed d) at hrun
  rw [he] at hrun
  refine ⟨embed d,t,?_,hrun,hh,hdi,d.work 0,d.work 1,ha,hb,?_,?_,?_,hdo⟩
  · simpa only [List.length_replicate,Nat.max_comm] using ht
  · simpa only [VerifierCountPrepare.unary_eq_reg] using hac
  · simpa only [VerifierCountPrepare.unary_eq_reg] using hbc
  · funext j; fin_cases j <;> first | rfl | exact hd2.trans h4.symm

theorem unary_value_injective (q r : ℕ) :
    BinaryFields.readNat (List.replicate q true) = BinaryFields.readNat (List.replicate r true) ↔ q = r := by
  induction q generalizing r with
  | zero =>
    cases r <;> simp [List.replicate_succ,BinaryFields.readNat,Nat.bit]
  | succ q ih =>
    cases r with
    | zero => simp [List.replicate_succ,BinaryFields.readNat,Nat.bit]
    | succ r =>
      have h := ih r
      simp only [List.replicate_succ,BinaryFields.readNat,Nat.bit_true] at *
      omega

theorem numeric_verdict (q target : ℕ) (v : Bool) (inp₀ : Tape) (base : Fin 11 → Tape)
    {inp : Tape} {work : Fin 11 → Tape} {out : Tape} (h : after q target v inp₀ base inp work out) :
    ∃ b, out = one .start b ∧ (b = true ↔ q = target ∧ v = true) := by
  obtain ⟨_,a,b,_,_,_,_,_,ho⟩ := h
  refine ⟨_,ho,?_⟩
  simp only [Bool.and_eq_true,VerifierBinaryEquality.equality_iff,unary_value_injective]

end UnconstrainedPACDetection.VerifierFieldCardinalityCheck
