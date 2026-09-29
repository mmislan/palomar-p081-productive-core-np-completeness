module

public import proofs.UnconstrainedPACDetection.VerifierEntityLoopBody

@[expose] public section

namespace UnconstrainedPACDetection.VerifierEntityOuterLoop
open Complexity Complexity.TM
open VerifierEntityLoopBody (frame sourcePred)

def factor (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (w : BinaryWitnessData.Witness) (i : ℕ) : Bool :=
  if h : i < s.entities then
    if w.mask.getD i false then VerifierEntityCheck.verdict s hn ⟨i,h⟩ w else true
  else true

def accumulator (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (w : BinaryWitnessData.Witness) (initial : Bool) : ℕ → Bool
  | 0 => initial
  | i+1 => factor s hn w i && accumulator s hn w initial i

def iterationBound (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) : ℕ :=
  VerifierMaskedEntity.bodyBound s w s.entities+5*s.entities+19

def machine : TM 14 := forRegTM VerifierEntityLoopBody.machine 13

/-- The actual complete entity loop has independent fuel and a charged rewind.
The prepared source and witness remain assumptions; this does not claim raw
binary input validation or full NP membership. -/
theorem loop_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) (hm : w.mask.length = s.entities) (initial : Bool) :
    machine.HoareTime
      (VerifierEntityLoopBody.pred s w 2 (regTape s.entities) initial)
      (VerifierEntityLoopBody.pred s w (2+s.entities) (regTape s.entities)
        (accumulator s hn w initial s.entities))
      (s.entities*(iterationBound s w+2)+(s.entities+2)) := by
  have h := VerifierMovingInputLoop.input_predicate_hoareTime VerifierEntityLoopBody.machine
    (13 : Fin 14) s.entities (fun _ => sourcePred s)
    (fun i => frame s w (2+i) (regTape s.entities))
    (fun i => [accumulator s hn w initial i]) (iterationBound s w)
    (by intro i inp hin; exact ⟨hin.1.1,hin.1.2.2.2⟩)
    (by intro i; rfl)
    (by intro i j _; exact VerifierEntityLoopBody.frame_parked s w (2+i) _ (parked_regTape _) j)
    (by
      intro i hi
      let fuel : Tape := ⟨i+2,regCells s.entities⟩
      have hf : Parked fuel := ⟨by change 1 ≤ i+2; omega,(parked_regTape s.entities).2⟩
      have hb := VerifierEntityLoopBody.entity_hoare s hs hn ⟨i,hi⟩ w hw hm fuel hf.read_ne_start
        (accumulator s hn w initial i)
      have ha : (if w.mask.getD i false then
          VerifierEntityCheck.verdict s hn ⟨i,hi⟩ w && accumulator s hn w initial i
          else accumulator s hn w initial i) = accumulator s hn w initial (i+1) := by
        simp only [accumulator,factor,dite_eq_left hi]
        cases hmask : w.mask.getD i false <;> simp
      have hb' := hb.mono_bound (show
          VerifierMaskedEntity.bodyBound s w i+5*i+19 ≤ iterationBound s w by
        unfold iterationBound VerifierMaskedEntity.bodyBound
        omega)
      unfold VerifierEntityLoopBody.pred at hb'
      simpa only [fuel,VerifierEntityLoopBody.update_fuel,
        Nat.add_assoc,ha] using hb')
  exact h

theorem accumulator_true_iff (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (w : BinaryWitnessData.Witness) (initial : Bool) (i : ℕ) :
    accumulator s hn w initial i = true ↔ initial = true ∧ ∀ j, j < i → factor s hn w j = true := by
  induction i with
  | zero => simp [accumulator]
  | succ i ih =>
    simp only [accumulator,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨hlast,hinit,hprev⟩
      refine ⟨hinit,?_⟩
      intro j hj
      by_cases hji : j < i
      · exact hprev j hji
      · have he : j = i := by omega
        simpa only [he] using hlast
    · rintro ⟨hinit,hall⟩
      exact ⟨hall i (by omega),hinit,fun j hj => hall j (by omega)⟩

/-- The loop accumulator is exactly the conjunction of the selected entity
verdicts, including the empty-selection case (which must be rejected separately). -/
theorem selected_verdicts_iff (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (w : BinaryWitnessData.Witness) :
    accumulator s hn w true s.entities = true ↔
      ∀ x : Fin s.entities, w.mask.getD x.val false = true → VerifierEntityCheck.verdict s hn x w = true := by
  rw [accumulator_true_iff]
  simp only [true_and]
  constructor
  · intro h x hm
    have hx := h x.val x.isLt
    simp only [factor,dite_eq_left x.isLt,hm,↓reduceIte] at hx
    exact hx
  · intro h i hi
    simp only [factor,dite_eq_left hi]
    cases hm : w.mask.getD i false
    · rfl
    · exact h ⟨i,hi⟩ hm

end UnconstrainedPACDetection.VerifierEntityOuterLoop
