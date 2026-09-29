module

public import proofs.UnconstrainedPACDetection.FormulaParameters
public import proofs.Complexitylib.Models.TuringMachine.Registers.RegisterOps

@[expose] public section

namespace UnconstrainedPACDetection.FormulaEndpointRegisters
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

theorem unary_word (v : Nat) : word (List.replicate v true) = regTape v := by
  apply IsReg.eq_regT
  have h := Tape.init_move_right_hasBinaryString (List.replicate v true)
  refine ⟨h.1,rfl,?_,?_⟩
  · intro i hi
    have hc := h.2.1 i (by simpa using hi)
    simpa [word,Γ.ofBool] using hc
  · intro j hj
    obtain ⟨i,rfl⟩ : ∃ i, j = i+1 := ⟨j-1,by omega⟩
    exact h.2.2 i (by simpa using (show v ≤ i by omega))

def frame (src : List Bool) (v : Fin 4 → Nat) (saved emitted : List Bool) :
    Complexity.TM.TapePred 4 := fun inp work out =>
  inp = word src ∧ (∀ j, j ≠ 3 → work j = regTape (v j)) ∧
    OutAcc saved (work 3) ∧ OutAcc emitted out

theorem parked (src : List Bool) (v : Fin 4 → Nat) (saved emitted : List Bool)
    {inp : Tape} {work : Fin 4 → Tape} {out : Tape}
    (h : frame src v saved emitted inp work out) : ∀ j, Parked (work j) := by
  intro j
  by_cases hj : j = 3
  · subst j; exact h.2.2.1.parked
  · rw [h.2.1 j hj]; exact parked_regTape _

theorem increment_hoare (q : Fin 4) (hq : q ≠ 3) (src : List Bool)
    (v : Fin 4 → Nat) (saved emitted : List Bool) : (incRegTM q).HoareTime
    (frame src v saved emitted)
    (frame src (Function.update v q (v q+1)) saved emitted) (2*v q+4) := by
  intro inp work out h
  have hp := parked src v saved emitted h
  obtain ⟨rfl,hv,hs,ho⟩ := h
  obtain ⟨d,t,ht,hr,hh,hi,hw,hout⟩ := incRegTM_hoareTime q (v q) (word src) work emitted
    (word_parked src) (fun j _ => hp j) (hv q hq) _ _ _ ⟨rfl,rfl,ho⟩
  refine ⟨d,t,ht,hr,hh,hi,?_,?_,hout⟩
  · intro j hj
    rw [hw]
    by_cases he : j = q
    · subst j; simp
    · simpa only [Function.update_of_ne he] using hv j hj
  · rw [hw]
    simpa only [Function.update_of_ne (Ne.symm hq)] using hs

theorem stable (src : List Bool) (v : Fin 4 → Nat) (saved emitted : List Bool) :
    ∀ inp work out, frame src v saved emitted inp work out →
      frame src v saved emitted (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have hp := parked src v saved emitted h
  have hold := h
  obtain ⟨hi,_,_,ho⟩ := h
  obtain ⟨hin,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start
    (hi ▸ (word_parked src).read_ne_start) (fun j => (hp j).read_ne_start) ho.parked.read_ne_start
  simpa only [hin,hw,hout] using hold

def values (src : List Bool) : Fin 4 → Nat :=
  ![FormulaTokenCount.run true none src,FormulaTokenCount.run false none src,
    FormulaMaximumFrame.value src,0]

theorem parameter_frame (src : List Bool) : FormulaParameters.machine.HoareTime
    (FormulaParameters.initial src) (frame src (values src) (FormulaMaximum.maximumBits src) [])
    (15*src.length+37) := by
  apply (FormulaParameters.ordinary_hoare src).consequence
  · intro inp work out h; exact h
  · rintro inp work out ⟨hi,h0,h1,h2,hs,ho⟩
    refine ⟨hi,?_,hs,ho⟩
    intro j hj
    fin_cases j
    · simpa [values,FormulaTokenCount.countBits,unary_word] using h0
    · simpa [values,FormulaTokenCount.countBits,unary_word] using h1
    · exact h2
    · exact False.elim (hj rfl)
  · omega

def adjusted (v : Fin 4 → Nat) : Fin 4 → Nat :=
  Function.update (Function.update v 1 (v 1+1)) 2 (v 2+1)

def increments : TM 4 := seqTM (incRegTM 1) (incRegTM 2)

theorem increments_hoare (src : List Bool) (v : Fin 4 → Nat) (saved emitted : List Bool) :
    increments.HoareTime (frame src v saved emitted) (frame src (adjusted v) saved emitted)
      (2*v 1+2*v 2+9) := by
  have h := seqTM_hoareTime _ _ (increment_hoare 1 (by decide) src v saved emitted)
    (stable src _ saved emitted) (increment_hoare 2 (by decide) src _ saved emitted)
  simpa [increments,adjusted] using h.mono_bound (by simp; omega)

def machine : TM 4 := seqTM FormulaParameters.machine increments

/-- Raw-input measured parameters become the endpoint bounds used by enumeration. -/
theorem ordinary_hoare (src : List Bool) : machine.HoareTime
    (FormulaParameters.initial src)
    (frame src (adjusted (values src)) (FormulaMaximum.maximumBits src) [])
    (23*src.length+51) := by
  have h := seqTM_hoareTime _ _ (parameter_frame src)
    (stable src _ _ []) (increments_hoare src _ _ [])
  apply h.mono_bound
  have hb := FormulaCountRegisters.count_length false src
  have hm := FormulaMaximumRestore.value_bound src
  simp only [FormulaTokenCount.countBits,List.length_replicate] at hb
  change (15*src.length+37)+1+
    (2*FormulaTokenCount.run false none src+2*FormulaMaximumFrame.value src+9) ≤ _
  omega

/-- The adjusted raw registers are exactly the formula graph's endpoint parameters. -/
theorem decoded_hoare (φ : SAT.CNF) : machine.HoareTime
    (FormulaParameters.initial φ.encode)
    (frame φ.encode ![φ.length,FormulaWiring.levels φ,FormulaWiring.varCount φ,0]
      (List.replicate φ.maxVar true) []) (23*φ.encode.length+51) := by
  obtain ⟨hc,ho⟩ := FormulaTokenCount.decoded_output φ.encode φ (SAT.CNF.decode?_encode φ)
  have hc' := congrArg List.length hc
  have ho' := congrArg List.length ho
  simp only [FormulaTokenCount.countBits,List.length_replicate] at hc' ho'
  have hm := FormulaMaximum.decoded_maximum φ.encode φ (SAT.CNF.decode?_encode φ)
  apply (ordinary_hoare φ.encode).consequence
  · intro inp work out h; exact h
  · rintro inp work out ⟨hi,hv,hs,he⟩
    refine ⟨hi,?_,?_,he⟩
    · intro j hj
      have h := hv j hj
      fin_cases j <;> simpa [adjusted,values,FormulaMaximumFrame.value,hc',ho',hm,
        FormulaWiring.levels,FormulaWiring.varCount] using h
    · simpa only [FormulaMaximum.maximumBits,hm] using hs
  · omega

end UnconstrainedPACDetection.FormulaEndpointRegisters
