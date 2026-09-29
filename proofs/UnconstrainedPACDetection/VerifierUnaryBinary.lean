module

public import proofs.UnconstrainedPACDetection.VerifierSourceRegisters

@[expose] public section

namespace UnconstrainedPACDetection.VerifierUnaryBinary
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)

def digits : ℕ → List Bool
  | 0 => []
  | n+1 => VerifierBinaryAdd.add false [true] (digits n)

theorem digits_value (n : ℕ) : BinaryFields.readNat (digits n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [digits,VerifierBinaryAdd.add_value,ih]
    change 1+n+0 = n+1
    omega

theorem digits_length (n : ℕ) : (digits n).length ≤ n+1 := by
  induction n with
  | zero => simp [digits]
  | succ n ih =>
    have h := VerifierBinaryAdd.add_length false [true] (digits n)
    change (digits (n+1)).length ≤ max 1 (digits n).length+1 at h
    have hm : max 1 (digits n).length ≤ n+1 := max_le (by omega) ih
    omega

def frame (i : ℕ) (fuel : Tape) : Fin 3 → Tape := ![wordTape (digits i),wordTape [true],fuel]

theorem frame_parked (i : ℕ) (fuel : Tape) (hf : Parked fuel) : ∀ j, Parked (frame i fuel j) := by
  intro j
  fin_cases j
  · exact VerifierReactionLoop.word_parked _
  · exact VerifierReactionLoop.word_parked _
  · exact hf

@[reducible] def body : TM 3 := placeWorkTM 0 1 VerifierBufferedAccumulate.machine

theorem body_hoare (i : ℕ) (fuel inp₀ : Tape) (hf : Parked fuel) (hi : Parked inp₀) (b : Bool) :
    body.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = frame i fuel ∧ OutAcc [b] out)
      (fun inp work out => inp = inp₀ ∧ work = frame (i+1) fuel ∧ OutAcc [b] out)
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
  · change OutAcc [b] d.output
    simpa only [hdo] using hout

@[reducible] def machine : TM 3 := forRegTM body 2

theorem conversion_hoare (v : ℕ) (inp₀ : Tape) (hi : Parked inp₀) (b : Bool) :
    machine.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = frame 0 (regTape v) ∧ OutAcc [b] out)
      (fun inp work out => inp = inp₀ ∧ work = frame v (regTape v) ∧ OutAcc [b] out)
      (20*(v+1)^2) := by
  have h := forRegTM_hoareTime body (2 : Fin 3) v inp₀
    (fun i => frame i (regTape v)) (fun _ => [b]) (2*v+9) hi
    (by intro i; rfl)
    (by intro i j _; exact frame_parked i _ (parked_regTape v) j) (by
      intro i hiv
      let fuel : Tape := ⟨i+2,regCells v⟩
      have hf : Parked fuel := ⟨by change 1 ≤ i+2; omega,(parked_regTape v).2⟩
      have he (k : ℕ) : Function.update (frame k (regTape v)) 2 fuel = frame k fuel := by
        funext j; fin_cases j <;> simp [frame]
      have hb := body_hoare i fuel inp₀ hf hi b
      have hb' := hb.mono_bound (show 1+2*max 1 (digits i).length+6 ≤ 2*v+9 by
        have hl := digits_length i
        have hm : max 1 (digits i).length ≤ v := max_le (by omega) (by omega)
        omega)
      change body.HoareTime
        (fun inp work out => inp = inp₀ ∧ work = Function.update (frame i (regTape v)) 2 fuel ∧ OutAcc [b] out)
        (fun inp work out => inp = inp₀ ∧ work = Function.update (frame (i+1) (regTape v)) 2 fuel ∧ OutAcc [b] out) _
      simpa only [he] using hb')
  exact h.mono_bound (by nlinarith)

end UnconstrainedPACDetection.VerifierUnaryBinary
