module

public import proofs.UnconstrainedPACDetection.VerifierActivationBody

@[expose] public section

namespace UnconstrainedPACDetection.VerifierActivationLoop
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierActivationBody (frame pred)

abbrev Row := List (List Bool × Bool)

def suffix (rows : List Row) (tail : List Bool) (i : ℕ) : List Bool :=
  BinaryFields.encode ((rows.drop i).flatMap (fun es => es.map Prod.fst)) ++ tail

theorem suffix_step (rows : List Row) (tail : List Bool) (i : ℕ) (hi : i < rows.length) :
    suffix rows tail i = BinaryFields.encode (rows[i].map Prod.fst) ++ suffix rows tail (i+1) := by
  simp only [suffix,List.drop_eq_getElem_cons hi,List.flatMap_cons,BinaryFields.encode,
    List.flatMap_append,List.append_assoc]

def emitted (rows : List Row) (initial : List Bool) : ℕ → List Bool
  | 0 => initial
  | i+1 => emitted rows initial i ++ [VerifierActivationSide.hit (rows.getD i []) false]

def machine : TM 3 := forRegTM VerifierActivationBody.machine 2

theorem loop_hoare (rows : List Row) (tail mask witTail initial : List Bool) (B : ℕ)
    (hm : ∀ es ∈ rows, es.map Prod.snd = mask)
    (hb : ∀ es ∈ rows, (BinaryFields.encode (es.map Prod.fst)).length+4*es.length+10 ≤ B) :
    machine.HoareTime
      (pred (suffix rows tail 0) (wordTape (BinaryFields.encodeField mask ++ witTail))
        (regTape rows.length) initial)
      (pred tail (wordTape (BinaryFields.encodeField mask ++ witTail))
        (regTape rows.length) (emitted rows initial rows.length))
      (rows.length*(B+2)+(rows.length+2)) := by
  let wt := wordTape (BinaryFields.encodeField mask ++ witTail)
  have h := VerifierMovingInputLoop.input_predicate_hoareTime VerifierActivationBody.machine
    (2 : Fin 3) rows.length (fun i inp => inp.HasBinarySuffix (suffix rows tail i))
    (fun _ => frame wt (regTape rows.length)) (emitted rows initial) B
    (by intro i inp hin; exact ⟨hin.1,hin.2.2.2⟩)
    (by intro i; rfl)
    (by intro i j _; exact VerifierActivationBody.frame_parked _ _ (parked_regTape _) j)
    (by
      intro i hi
      let fuel : Tape := ⟨i+2,regCells rows.length⟩
      have hf : Parked fuel := ⟨by change 1 ≤ i+2; omega,(parked_regTape rows.length).2⟩
      have hmem : rows[i] ∈ rows := List.getElem_mem hi
      have hmask := hm rows[i] hmem
      have he : emitted rows initial (i+1) =
          emitted rows initial i ++ [VerifierActivationSide.hit rows[i] false] := by
        simp [emitted,List.getD,hi]
      have hr := (VerifierActivationBody.row_hoare rows[i] (suffix rows tail (i+1)) witTail
        (emitted rows initial i) fuel hf.read_ne_start).mono_bound (hb rows[i] hmem)
      unfold VerifierActivationBody.pred at hr
      simpa only [VerifierActivationBody.update_fuel,
        hmask,← suffix_step rows tail i hi,← he] using hr)
  unfold machine VerifierActivationBody.pred
  simpa only [wt,emitted,suffix,List.drop_length,List.flatMap_nil,
    BinaryFields.encode,List.nil_append] using h

end UnconstrainedPACDetection.VerifierActivationLoop
