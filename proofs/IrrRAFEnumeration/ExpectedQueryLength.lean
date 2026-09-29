module

public import proofs.IrrRAFEnumeration.TotalQueryHeaders
public import proofs.Complexitylib.Models.TuringMachine.Registers.Horner

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open Complexity Complexity.TM

def expectedLength (g d r : Nat) := 3+g+2*d+2*r+g*r+3*d*r
def lengthCap (g d r : Nat) := expectedLength g d r+g+d+r
def sourceValue (g d r : Nat) (i : Fin 4) := if i = 0 then g else if i = 1 then d else r
def lengthWork (g d r a : Nat) (i : Fin 4) : Tape :=
  regTape (if i = 3 then a else sourceValue g d r i)

theorem lengthWork_parked (g d r a : Nat) : ∀ i, Parked (lengthWork g d r a i) := by
  intro i
  exact parked_regTape _

theorem lengthWork_update (g d r a b : Nat) :
    Function.update (lengthWork g d r a) 3 (regTape b) = lengthWork g d r b := by
  funext i
  by_cases h : i = 3 <;> simp [lengthWork, h]

theorem length_add_spec (q : Fin 4) (hq : q ≠ 3) (g d r a M : Nat)
    (ha : sourceValue g d r q ≤ M) (hb : a+sourceValue g d r q ≤ M)
    (inp : Tape) (ys : List Bool) (hp : Parked inp) :
    (addIntoTM q 3).HoareTime (EmitPred inp (lengthWork g d r a) ys)
      (EmitPred inp (lengthWork g d r (a+sourceValue g d r q)) ys) (opBudget M) := by
  have h := addIntoTM_hoareTime q 3 hq (sourceValue g d r q) a inp (lengthWork g d r a) ys hp
    (fun i _ => lengthWork_parked g d r a i)
    (by simp [lengthWork,hq]) (by simp [lengthWork])
  rw [lengthWork_update] at h
  exact TM.HoareTime.mono_bound h (addIntoTM_le_opBudget ha hb)

theorem length_mul_spec (q s : Fin 4) (hqs : q ≠ s) (hq : q ≠ 3) (hs : s ≠ 3)
    (g d r a M : Nat) (hqM : sourceValue g d r q ≤ M) (hsM : sourceValue g d r s ≤ M)
    (ha : a+sourceValue g d r q*sourceValue g d r s ≤ M)
    (inp : Tape) (ys : List Bool) (hp : Parked inp) :
    (mulAddIntoTM q s 3).HoareTime (EmitPred inp (lengthWork g d r a) ys)
      (EmitPred inp (lengthWork g d r (a+sourceValue g d r q*sourceValue g d r s)) ys) (opBudget M) := by
  have h := mulAddIntoTM_hoareTime q s 3 hqs hq hs (sourceValue g d r q) (sourceValue g d r s)
    a inp (lengthWork g d r a) ys hp (fun i _ => lengthWork_parked g d r a i)
    (by simp [lengthWork,hq]) (by simp [lengthWork,hs]) (by simp [lengthWork])
  rw [lengthWork_update] at h
  exact TM.HoareTime.mono_bound h (mulAddIntoTM_le_opBudget hqM hsM ha)

def lengthStage (g d r : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 3
  | 2 => 3+g
  | 3 => 3+g+d
  | 4 => 3+g+2*d
  | 5 => 3+g+2*d+r
  | 6 => 3+g+2*d+2*r
  | 7 => 3+g+2*d+2*r+g*r
  | 8 => 3+g+2*d+2*r+g*r+d*r
  | 9 => 3+g+2*d+2*r+g*r+2*d*r
  | _ => expectedLength g d r

def lengthMachines : List (TM 4) :=
  [setConstTM 3 3,addIntoTM 0 3,addIntoTM 1 3,addIntoTM 1 3,
   addIntoTM 2 3,addIntoTM 2 3,mulAddIntoTM 0 2 3,
   mulAddIntoTM 1 2 3,mulAddIntoTM 1 2 3,mulAddIntoTM 1 2 3]
def expectedLengthTM : TM 4 := bigSeqTM lengthMachines

theorem expectedLengthTM_correct (g d r : Nat) (inp : Tape) (ys : List Bool) (hp : Parked inp) :
    expectedLengthTM.HoareTime (EmitPred inp (lengthWork g d r 0) ys)
      (EmitPred inp (lengthWork g d r (expectedLength g d r)) ys)
      (10*(opBudget (lengthCap g d r)+1)+1) := by
  have hset := setConstTM_hoareTime (3 : Fin 4) 3 0 inp (lengthWork g d r 0) ys hp
    (lengthWork_parked g d r 0) (by simp [lengthWork])
  rw [lengthWork_update] at hset
  have hset' := TM.HoareTime.mono_bound hset (setConstTM_le_opBudget
    (M := lengthCap g d r) (by unfold lengthCap expectedLength; omega) (by omega))
  have hadd := fun q hq a ha hb => length_add_spec q hq g d r a (lengthCap g d r) ha hb inp ys hp
  have hmul := fun q s hqs hq hs a ha hb hc => length_mul_spec q s hqs hq hs g d r a
    (lengthCap g d r) ha hb hc inp ys hp
  have hsrc (q : Fin 4) : sourceValue g d r q ≤ lengthCap g d r := by
    by_cases h0 : q = 0
    · simp only [sourceValue,ite_eq_left h0]
      unfold lengthCap expectedLength
      omega
    · by_cases h1 : q = 1
      · simp only [sourceValue,ite_eq_right h0,ite_eq_left h1]
        unfold lengthCap expectedLength
        omega
      · simp only [sourceValue,ite_eq_right h0,ite_eq_right h1]
        unfold lengthCap expectedLength
        omega
  have hall := bigSeqTM_hoareTime lengthMachines inp
    (fun k => lengthWork g d r (lengthStage g d r k)) (fun _ => ys)
    (opBudget (lengthCap g d r)) hp (fun k => lengthWork_parked g d r (lengthStage g d r k))
    (by
      intro k hk
      have hk' : k < 10 := hk
      interval_cases k <;> simp only [lengthMachines,List.getElem_cons_zero,List.getElem_cons_succ,lengthStage]
      · exact hset'
      · exact hadd 0 (by decide) _ (by simp [sourceValue,lengthCap,expectedLength,Nat.mul_assoc]; omega)
          (by simp [sourceValue,lengthCap,expectedLength,Nat.mul_assoc]; omega)
      · exact hadd 1 (by decide) _ (by simp [sourceValue,lengthCap,expectedLength,Nat.mul_assoc]; omega)
          (by simp [sourceValue,lengthCap,expectedLength,Nat.mul_assoc]; omega)
      · convert hadd 1 (by decide) (3+g+d) (by simp [sourceValue,lengthCap,expectedLength,Nat.mul_assoc]; omega)
          (by simp [sourceValue,lengthCap,expectedLength,Nat.mul_assoc]; omega) using 1
        congr 2
        simp [sourceValue]
        ring
      · exact hadd 2 (by decide) _ (hsrc 2)
          (by simp [sourceValue,lengthCap,expectedLength,Nat.mul_assoc]; omega)
      · convert hadd 2 (by decide) (3+g+2*d+r) (hsrc 2)
          (by simp [sourceValue,lengthCap,expectedLength,Nat.mul_assoc]; omega) using 1
        congr 2
        simp [sourceValue]
        ring
      · exact hmul 0 2 (by decide) (by decide) (by decide) _
          (hsrc 0) (hsrc 2)
          (by simp [sourceValue,lengthCap,expectedLength,Nat.mul_assoc]; omega)
      · exact hmul 1 2 (by decide) (by decide) (by decide) _
          (hsrc 1) (hsrc 2)
          (by simp [sourceValue,lengthCap,expectedLength,Nat.mul_assoc]; omega)
      · convert hmul 1 2 (by decide) (by decide) (by decide) (3+g+2*d+2*r+g*r+d*r)
          (hsrc 1) (hsrc 2)
          (by simp [sourceValue,lengthCap,expectedLength,Nat.mul_assoc]; omega) using 1
        congr 2
        simp [sourceValue]
        ring
      · convert hmul 1 2 (by decide) (by decide) (by decide) (3+g+2*d+2*r+g*r+2*d*r)
          (hsrc 1) (hsrc 2)
          (by simp [sourceValue,lengthCap,expectedLength,Nat.mul_assoc]; omega) using 1
        congr 2
        simp [sourceValue,expectedLength]
        ring)
  exact hall

theorem lengthCap_le (g d r N : Nat) (h : g+d+r ≤ N) :
    lengthCap g d r ≤ 10*(N+1)^2 := by
  have hg : g ≤ N := by omega
  have hd : d ≤ N := by omega
  have hr : r ≤ N := by omega
  have hgr := Nat.mul_le_mul hg hr
  have hdr := Nat.mul_le_mul hd hr
  unfold lengthCap expectedLength
  nlinarith

def lengthTime (N : Nat) := 10*(opBudget (10*(N+1)^2)+1)+1

theorem expectedLengthTM_inputBound (g d r N : Nat) (h : g+d+r ≤ N)
    (inp : Tape) (ys : List Bool) (hp : Parked inp) :
    expectedLengthTM.HoareTime (EmitPred inp (lengthWork g d r 0) ys)
      (EmitPred inp (lengthWork g d r (expectedLength g d r)) ys) (lengthTime N) := by
  apply TM.HoareTime.mono_bound (expectedLengthTM_correct g d r inp ys hp)
  have hc := lengthCap_le g d r N h
  unfold lengthTime opBudget
  gcongr

theorem expectedLength_parse (z : List Bool) :
    expectedLength (parse z).knownCount (parse z).moleculeCount (parse z).reactionCount =
      (parse z).knownCount+(parse z).moleculeCount+(parse z).reactionCount+3+expectedBodyLength (parse z) := by
  unfold expectedLength expectedBodyLength
  ring

end IrrRAFEnumeration.CompletionQuery
