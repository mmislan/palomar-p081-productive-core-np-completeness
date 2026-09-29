module

public import proofs.UnconstrainedPACDetection.FormulaTargetEmitter
public import proofs.UnconstrainedPACDetection.VerifierOutputRouting
public import proofs.UnconstrainedPACDetection.VerifierWorkPermutation
public import proofs.UnconstrainedPACDetection.VerifierPairRestore

@[expose] public section

namespace UnconstrainedPACDetection.FormulaTargetRouting
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def swap : Equiv.Perm (Fin 6) := Equiv.swap 3 5
def original (b : Bool) : TM 5 := FormulaTargetEmitter.machine 3 b
def routed (b : Bool) : TM 6 :=
  VerifierWorkPermutation.machine (original b).retargetOutput swap

def after (v : Nat) (b : Bool) (inp₀ : Tape) (work₀ : Fin 6 → Tape)
    (emitted : List Bool) : Complexity.TM.TapePred 6 := fun inp work out =>
  inp = inp₀ ∧ (∀ j, j ≠ 3 → work j = work₀ j) ∧
  OutAcc (FormulaLookupMatching.marked (FormulaLookupMatching.target v b)) (work 3) ∧
  OutAcc emitted out

/-- Read live register 5 and append the exact marked target to scratch tape 3. -/
theorem routed_hoare (v : Nat) (b : Bool) (inp₀ : Tape) (work₀ : Fin 6 → Tape)
    (emitted : List Bool) (hi : Parked inp₀) (hp : ∀ j, Parked (work₀ j))
    (hv : work₀ 5 = regTape v) (he : work₀ 3 = word []) :
    (routed b).HoareTime (EmitPred inp₀ work₀ emitted)
      (after v b inp₀ work₀ emitted) (4*v+6) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  let small : Fin 5 → Tape := fun j => work (swap (Fin.castSucc j))
  have hsmall : ∀ j, Parked (small j) := fun j => hp _
  have hv' : small 3 = regTape v := by simpa [small,swap] using hv
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := FormulaTargetEmitter.target_hoare
    (3 : Fin 5) b v inp small [] hi hsmall hv' inp small (word [])
    ⟨rfl,rfl,outAcc_nil_init⟩
  have hr := VerifierOutputRouting.run_frame (original b) out ho.parked.read_ne_start hd
  have hs := VerifierWorkPermutation.run_commute (original b).retargetOutput swap hr
  let final := VerifierWorkPermutation.wrap (original b).retargetOutput swap
    (VerifierOutputRouting.wrap (original b) out d)
  refine ⟨final,t,ht,?_,hh,hdi,?_,?_,ho⟩
  unfold routed
  · convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [VerifierWorkPermutation.wrap,VerifierOutputRouting.wrap,
        retargetCfg,swap,Equiv.swap_apply_def,small,he]
    · rfl
  · intro j hj
    fin_cases j <;> simp_all [final,VerifierWorkPermutation.wrap,VerifierOutputRouting.wrap,
      retargetCfg,swap,Equiv.swap_apply_def,small]
  · simpa [final,VerifierWorkPermutation.wrap,VerifierOutputRouting.wrap,retargetCfg,swap]
      using hdo

def ready (v : Nat) (b : Bool) (inp₀ : Tape) (work₀ : Fin 6 → Tape)
    (emitted : List Bool) : Complexity.TM.TapePred 6 := fun inp work out =>
  inp = inp₀ ∧ (∀ j, j ≠ 3 → work j = work₀ j) ∧
  work 3 = word (FormulaLookupMatching.marked (FormulaLookupMatching.target v b)) ∧
  OutAcc emitted out

theorem after_parked (v : Nat) (b : Bool) (inp₀ : Tape) (work₀ : Fin 6 → Tape)
    (emitted : List Bool) (hp : ∀ j, Parked (work₀ j))
    {inp : Tape} {work : Fin 6 → Tape} {out : Tape}
    (h : after v b inp₀ work₀ emitted inp work out) : ∀ j, Parked (work j) := by
  intro j
  by_cases hj : j = 3
  · subst j; exact h.2.2.1.parked
  · rw [h.2.1 j hj]; exact hp j

theorem rewind_hoare (v : Nat) (b : Bool) (inp₀ : Tape) (work₀ : Fin 6 → Tape)
    (emitted : List Bool) (hi : Parked inp₀) (hp : ∀ j, Parked (work₀ j)) :
    (rewindWorkTM (3 : Fin 6)).HoareTime (after v b inp₀ work₀ emitted)
      (ready v b inp₀ work₀ emitted) (v+5) := by
  intro inp work out h
  have hw := after_parked v b inp₀ work₀ emitted hp h
  obtain ⟨hin,hothers,htarget,ho⟩ := h
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := VerifierPairRestore.restore_word (3 : Fin 6)
    _ emitted inp work (hin ▸ hi) hw htarget _ _ _ ⟨rfl,rfl,ho⟩
  refine ⟨d,t,?_,hd,hh,hdi.trans hin,?_,?_,hdo⟩
  · simpa [FormulaLookupMatching.marked,FormulaLookupMatching.target,SAT.Lit.encodeRaw,
      SAT.Unary.encode,List.length_append,Nat.add_assoc] using ht
  · intro j hj
    rw [hdw,Function.update_of_ne hj]; exact hothers j hj
  · rw [hdw]; simp

def prepared (b : Bool) : TM 6 := seqTM (routed b) (rewindWorkTM 3)

theorem ready_hoare (v : Nat) (b : Bool) (inp₀ : Tape) (work₀ : Fin 6 → Tape)
    (emitted : List Bool) (hi : Parked inp₀) (hp : ∀ j, Parked (work₀ j))
    (hv : work₀ 5 = regTape v) (he : work₀ 3 = word []) :
    (prepared b).HoareTime (EmitPred inp₀ work₀ emitted)
      (ready v b inp₀ work₀ emitted) (5*v+12) := by
  have hs : ∀ inp work out, after v b inp₀ work₀ emitted inp work out →
      after v b inp₀ work₀ emitted (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
    intro inp work out h
    have hw := after_parked v b inp₀ work₀ emitted hp h
    obtain ⟨hin,hwork,hout⟩ := phaseTransition_eq_self_of_reads_ne_start
      (h.1 ▸ hi.read_ne_start) (fun j => (hw j).read_ne_start) h.2.2.2.parked.read_ne_start
    simpa only [hin,hwork,hout] using h
  have h := seqTM_hoareTime _ _ (routed_hoare v b inp₀ work₀ emitted hi hp hv he)
    hs (rewind_hoare v b inp₀ work₀ emitted hi hp)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.FormulaTargetRouting
