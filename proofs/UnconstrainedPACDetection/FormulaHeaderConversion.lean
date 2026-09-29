module

public import proofs.UnconstrainedPACDetection.FormulaHeaderBinaryDigits
public import proofs.UnconstrainedPACDetection.VerifierCountPrepare

@[expose] public section

namespace UnconstrainedPACDetection.FormulaHeaderConversion
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierUnaryBinary (frame frame_parked body digits digits_length)

theorem body_hoare (i : ℕ) (fuel inp₀ : Tape) (hf : Parked fuel) (hi : Parked inp₀) (ys : List Bool) :
    body.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = frame i fuel ∧ OutAcc ys out)
      (fun inp work out => inp = inp₀ ∧ work = frame (i+1) fuel ∧ OutAcc ys out)
      (1+2*max 1 (digits i).length+6) := by
  rintro inp work out ⟨hin,hwork,hout⟩
  subst inp; subst work
  obtain ⟨d,t,ht,hd,hh,hdi,hd0,hd1,hdo⟩ := VerifierBufferedAccumulate.prepared_hoare [true] (digits i)
    inp₀ out hi.read_ne_start hout.parked.read_ne_start inp₀ ![wordTape (digits i),wordTape [true]] out
    ⟨rfl,rfl,rfl,rfl⟩
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal VerifierBufferedAccumulate.machine
    0 1 (frame i fuel) hd (by intro j _; exact (frame_parked i fuel hf j).read_ne_start)
  refine ⟨placeWorkCfg VerifierBufferedAccumulate.machine 0 1 (frame i fuel) d,t,ht,?_,hh,hdi,?_,?_⟩
  · convert hp using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,frame,digits,hd0,hd1]
    all_goals rfl
  · change OutAcc ys d.output
    simpa only [hdo] using hout

def machine : TM 3 := forRegTM body 2

theorem core_hoare (v : ℕ) (inp₀ : Tape) (hi : Parked inp₀) (ys : List Bool) :
    machine.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = frame 0 (regTape v) ∧ OutAcc ys out)
      (fun inp work out => inp = inp₀ ∧ work = frame v (regTape v) ∧ OutAcc ys out)
      (20*(v+1)^2) := by
  have h := forRegTM_hoareTime body (2 : Fin 3) v inp₀
    (fun i => frame i (regTape v)) (fun _ => ys) (2*v+9) hi
    (by intro i; rfl)
    (by intro i j _; exact frame_parked i _ (parked_regTape v) j) (by
      intro i hiv
      let fuel : Tape := ⟨i+2,regCells v⟩
      have hf : Parked fuel := ⟨by change 1 ≤ i+2; omega,(parked_regTape v).2⟩
      have he (k : ℕ) : Function.update (frame k (regTape v)) 2 fuel = frame k fuel := by
        funext j; fin_cases j <;> simp [frame]
      have hb := body_hoare i fuel inp₀ hf hi ys
      have hb' := hb.mono_bound (show 1+2*max 1 (digits i).length+6 ≤ 2*v+9 by
        have hl := digits_length i
        have hm : max 1 (digits i).length ≤ v := max_le (by omega) (by omega)
        omega)
      change body.HoareTime
        (fun inp work out => inp = inp₀ ∧ work = Function.update (frame i (regTape v)) 2 fuel ∧ OutAcc ys out)
        (fun inp work out => inp = inp₀ ∧ work = Function.update (frame (i+1) (regTape v)) 2 fuel ∧ OutAcc ys out) _
      simpa only [he] using hb')
  exact h.mono_bound (by nlinarith)

theorem conversion_hoare (v : ℕ) (inp₀ : Tape) (hi : Parked inp₀) (ys : List Bool) :
    VerifierCountPrepare.machine.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = VerifierCountPrepare.initial v ∧ OutAcc ys out)
      (fun inp work out => inp = inp₀ ∧ work = VerifierUnaryBinary.frame v (regTape v) ∧ OutAcc ys out)
      (20*(v+1)^2+2) := by
  have hseed : VerifierCountPrepare.seed.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = VerifierCountPrepare.initial v ∧ OutAcc ys out)
      (fun inp work out => inp = inp₀ ∧ work = VerifierUnaryBinary.frame 0 (regTape v) ∧ OutAcc ys out) 1 := by
    rintro inp work out ⟨hin,hwork,ho⟩
    subst inp; subst work
    exact ⟨_,1,le_rfl,VerifierCountPrepare.seed_run v inp₀ out hi.read_ne_start ho.parked,rfl,rfl,rfl,ho⟩
  have stable : ∀ inp work out,
      (inp = inp₀ ∧ work = VerifierUnaryBinary.frame 0 (regTape v) ∧ OutAcc ys out) →
      transitionInput inp = inp₀ ∧
      (fun j => transitionTape (work j)) = VerifierUnaryBinary.frame 0 (regTape v) ∧
      OutAcc ys (transitionTape out) := by
    rintro inp work out ⟨rfl,rfl,ho⟩
    obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start
      (fun j => (VerifierUnaryBinary.frame_parked 0 _ (parked_regTape v) j).read_ne_start)
      ho.parked.read_ne_start
    exact ⟨hi',hw',by simpa only [ho'] using ho⟩
  have h := seqTM_hoareTime _ _ hseed stable (core_hoare v inp₀ hi ys)
  exact h.mono_bound (by omega)


/-- Canonical binary digits from a physical unary register, preserving any output prefix. -/
theorem canonical_hoare (v : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    VerifierCountPrepare.machine.HoareTime
      (EmitPred inp (VerifierCountPrepare.initial v) ys)
      (EmitPred inp ![wordTape v.bits,wordTape [true],regTape v] ys)
      (20*(v+1)^2+2) := by
  unfold EmitPred
  simpa only [VerifierUnaryBinary.frame,FormulaHeaderBinaryDigits.digits_eq_bits]
    using conversion_hoare v inp hi ys

end UnconstrainedPACDetection.FormulaHeaderConversion
