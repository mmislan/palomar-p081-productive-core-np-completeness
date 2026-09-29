module

public import proofs.UnconstrainedPACDetection.VerifierJointPrepare

@[expose] public section

namespace UnconstrainedPACDetection.VerifierDimensionCompare
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)

def permutation (second : Bool) : Equiv.Perm (Fin 11) :=
  if second then (Equiv.swap 0 6).trans ((Equiv.swap 1 2).trans (Equiv.swap 1 10))
  else (Equiv.swap 0 3).trans (Equiv.swap 2 10)

def placed : TM 11 := placeWorkTM 0 8 VerifierEqualityCommit.machine
def machine (second : Bool) : TM 11 := VerifierWorkPermutation.machine placed (permutation second)

def changed (second : Bool) (base : Fin 11 → Tape) (a b : Tape) : Fin 11 → Tape :=
  Function.update (Function.update base (permutation second 0) a) (permutation second 1) b

def after (second : Bool) (xs ys : List Bool) (v : Bool) (inp₀ : Tape)
    (base : Fin 11 → Tape) : Complexity.TM.TapePred 11 := fun inp work out =>
  inp = inp₀ ∧ ∃ a b, a.HasBinarySuffix [] ∧ b.HasBinarySuffix [] ∧
    a.cells = (wordTape ys).cells ∧ b.cells = (wordTape xs).cells ∧
    work = changed second base a b ∧
    out = one .start (VerifierBinaryEquality.compare true xs ys && v)

theorem validation_hoare (second : Bool) (xs ys : List Bool) (v : Bool)
    (inp₀ : Tape) (base : Fin 11 → Tape) (hi : inp₀.read ≠ .start)
    (hp : ∀ j, Parked (base j))
    (h0 : base (permutation second 0) = wordTape ys)
    (h1 : base (permutation second 1) = wordTape xs)
    (h2 : base (permutation second 2) = wordTape []) : (machine second).HoareTime
    (fun inp work out => inp = inp₀ ∧ work = base ∧ out = one .start v)
    (after second xs ys v inp₀ base) (max xs.length ys.length+4) := by
  rintro inp work out ⟨hin,hw,ho⟩
  subst inp; subst work; subst out
  obtain ⟨d,t,ht,hr,hh,hdi,ha,hb,hac,hbc,hd2,hdo⟩ :=
    VerifierEqualityCommit.validation_hoare xs ys v inp₀ hi inp₀
      ![wordTape ys,wordTape xs,wordTape []] (one .start v) ⟨rfl,rfl,rfl⟩
  let unperm : Fin 11 → Tape := fun j => base (permutation second j)
  have hplaced := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierEqualityCommit.machine 0 8 unperm hr
    (by intro j _; exact (hp _).read_ne_start)
  have hrun := VerifierWorkPermutation.run_commute placed (permutation second) hplaced
  let embed := fun c : Cfg 3 VerifierEqualityCommit.machine.Q =>
    VerifierWorkPermutation.wrap placed (permutation second)
      (placeWorkCfg VerifierEqualityCommit.machine 0 8 unperm c)
  have he : embed ⟨VerifierEqualityCommit.machine.qstart,inp₀,
      ![wordTape ys,wordTape xs,wordTape []],one .start v⟩ =
      (⟨(machine second).qstart,inp₀,base,one .start v⟩ : Cfg 11 (machine second).Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      cases second <;> fin_cases j <;>
        first | rfl | exact h0.symm | exact h1.symm | exact h2.symm
    · rfl
  change (machine second).reachesIn t (embed _) (embed d) at hrun
  rw [he] at hrun
  refine ⟨embed d,t,ht,hrun,hh,hdi,d.work 0,d.work 1,ha,hb,hac,hbc,?_,hdo⟩
  funext j
  cases second <;> fin_cases j <;>
    first | rfl | exact hd2.trans h2.symm

theorem after_parked (second : Bool) (xs ys : List Bool) (v : Bool)
    (inp₀ : Tape) (base : Fin 11 → Tape) (hp : ∀ j, Parked (base j))
    {inp : Tape} {work : Fin 11 → Tape} {out : Tape}
    (h : after second xs ys v inp₀ base inp work out) : ∀ j, Parked (work j) := by
  obtain ⟨_,a,b,ha,hb,_,_,hw,_⟩ := h
  rw [hw]
  intro j
  simp only [changed,Function.update_apply]
  split
  · exact ⟨hb.1,hb.2.2.2⟩
  · split
    · exact ⟨ha.1,ha.2.2.2⟩
    · exact hp j

theorem after_stable (second : Bool) (xs ys : List Bool) (v : Bool)
    (inp₀ : Tape) (base : Fin 11 → Tape) (hi : inp₀.read ≠ .start)
    (hp : ∀ j, Parked (base j)) : ∀ inp work out,
    after second xs ys v inp₀ base inp work out →
    after second xs ys v inp₀ base (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have hw := after_parked second xs ys v inp₀ base hp h
  have horig := h
  obtain ⟨hin,a,b,_,_,_,_,_,ho⟩ := h
  have hout : out.read ≠ .start := by rw [ho]; change Γ.blank ≠ Γ.start; decide
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start (hin ▸ hi)
    (fun j => (hw j).read_ne_start) hout
  simpa only [hi',hw',ho'] using horig

def bothAfter (x₁ y₁ x₂ y₂ : List Bool) (v : Bool) (inp₀ : Tape)
    (base : Fin 11 → Tape) : Complexity.TM.TapePred 11 := fun inp work out =>
  ∃ mid, after false x₁ y₁ v inp₀ base inp₀ mid
      (one .start (VerifierBinaryEquality.compare true x₁ y₁ && v)) ∧
    after true x₂ y₂ (VerifierBinaryEquality.compare true x₁ y₁ && v) inp₀ mid inp work out

theorem second_hoare (x₁ y₁ x₂ y₂ : List Bool) (v : Bool) (inp₀ : Tape)
    (base : Fin 11 → Tape) (hi : inp₀.read ≠ .start) (hp : ∀ j, Parked (base j))
    (h6 : base 6 = wordTape y₂) (h2 : base 2 = wordTape x₂) (h10 : base 10 = wordTape []) :
    (machine true).HoareTime (after false x₁ y₁ v inp₀ base)
      (bothAfter x₁ y₁ x₂ y₂ v inp₀ base) (max x₂.length y₂.length+4) := by
  intro inp work out h
  have hpark := after_parked false x₁ y₁ v inp₀ base hp h
  have hfirst := h
  obtain ⟨hin,a,b,_,_,_,_,hw,ho⟩ := h
  have hw6 : work (permutation true 0) = wordTape y₂ := by rw [hw]; exact h6
  have hw2 : work (permutation true 1) = wordTape x₂ := by rw [hw]; exact h2
  have hw10 : work (permutation true 2) = wordTape [] := by rw [hw]; exact h10
  obtain ⟨d,t,ht,hr,hh,hpost⟩ := validation_hoare true x₂ y₂
    (VerifierBinaryEquality.compare true x₁ y₁ && v) inp₀ work hi hpark hw6 hw2 hw10
    inp work out ⟨hin,rfl,ho⟩
  refine ⟨d,t,ht,hr,hh,work,?_,hpost⟩
  simpa only [hin,ho] using hfirst

def bothMachine : TM 11 := seqTM (machine false) (machine true)

theorem both_hoare (x₁ y₁ x₂ y₂ : List Bool) (v : Bool) (inp₀ : Tape)
    (base : Fin 11 → Tape) (hi : inp₀.read ≠ .start) (hp : ∀ j, Parked (base j))
    (h3 : base 3 = wordTape y₁) (h1 : base 1 = wordTape x₁)
    (h6 : base 6 = wordTape y₂) (h2 : base 2 = wordTape x₂) (h10 : base 10 = wordTape []) :
    bothMachine.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = base ∧ out = one .start v)
      (bothAfter x₁ y₁ x₂ y₂ v inp₀ base)
      (max x₁.length y₁.length + max x₂.length y₂.length + 9) := by
  have h := seqTM_hoareTime _ _
    (validation_hoare false x₁ y₁ v inp₀ base hi hp h3 h1 h10)
    (after_stable false x₁ y₁ v inp₀ base hi hp)
    (second_hoare x₁ y₁ x₂ y₂ v inp₀ base hi hp h6 h2 h10)
  exact h.mono_bound (by omega)

theorem numeric_verdict (m n k l : ℕ) (v : Bool) (inp₀ : Tape) (base : Fin 11 → Tape)
    {inp : Tape} {work : Fin 11 → Tape} {out : Tape}
    (h : bothAfter m.bits (VerifierUnaryBinary.digits k) n.bits (VerifierUnaryBinary.digits l)
      v inp₀ base inp work out) :
    ∃ b, out = one .start b ∧ (b = true ↔ m = k ∧ n = l ∧ v = true) := by
  obtain ⟨mid,_,_,a,b,_,_,_,_,_,ho⟩ := h
  refine ⟨_,ho,?_⟩
  simp only [Bool.and_eq_true,VerifierBinaryEquality.equality_iff,
    VerifierUnaryBinary.digits_value,BinaryFields.readNat_bits]
  constructor
  · rintro ⟨hn,hm,hv⟩; exact ⟨hm.symm,hn.symm,hv⟩
  · rintro ⟨hm,hn,hv⟩; exact ⟨hn.symm,hm.symm,hv⟩

end UnconstrainedPACDetection.VerifierDimensionCompare
