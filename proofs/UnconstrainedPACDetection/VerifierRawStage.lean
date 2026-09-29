module

public import proofs.UnconstrainedPACDetection.VerifierRawDecision

@[expose] public section

namespace UnconstrainedPACDetection.VerifierRawStage
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)

abbrev original := VerifierRawCardinality.machine
def routed : TM 12 := original.retargetOutput
def machine : TM 30 := placeWorkTM 18 0 routed

def initialWork (wit : List Bool) : Fin 30 → Tape :=
  fun j => if j = 27 then wordTape wit else wordTape []

def initial (src wit : List Bool) : Complexity.TM.TapePred 30 := fun inp work out =>
  inp = wordTape src ∧ work = initialWork wit ∧ out = wordTape []

def budget (src wit : List Bool) : Nat :=
  13*src.length+42*(wit.length+1)^2+4*wit.length+4*opBudget (2*(wit.length+1)^2)+102

theorem stage_hoare (src wit : List Bool) : machine.HoareTime (initial src wit)
    (VerifierRawDecision.ready src wit (budget src wit+1)) (budget src wit) := by
  rintro inp work out ⟨rfl,rfl,rfl⟩
  let W := VerifierJointWitness.layout (fun _ => wordTape []) (fun _ => wordTape [])
    (wordTape wit) (wordTape [])
  obtain ⟨d,t,ht,hd,hh,hraw⟩ := VerifierRawCardinality.validation_hoare src wit
    (wordTape src) W (wordTape []) ⟨rfl,rfl,rfl⟩
  have hrouted := VerifierOutputRouting.run_frame original (wordTape [])
    (VerifierReactionLoop.word_parked []).read_ne_start hd
  have hplaced := placeWorkTM_reachesIn_placeWorkCfg_stable_internal routed 18 0
    (initialWork wit) hrouted (by
      intro j _
      dsimp [initialWork]
      split <;> exact (VerifierReactionLoop.word_parked _).read_ne_start)
  have hstart : placeWorkCfg routed 18 0 (initialWork wit)
      (VerifierOutputRouting.wrap original (wordTape [])
        ⟨original.qstart,wordTape src,W,wordTape []⟩) =
      (⟨machine.qstart,wordTape src,initialWork wit,wordTape []⟩ : Cfg 30 machine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  rw [hstart] at hplaced
  let final := placeWorkCfg routed 18 0 (initialWork wit)
    (VerifierOutputRouting.wrap original (wordTape []) d)
  have hwork : VerifierValidatedEntry.rawWork final.work = d.work := by
    funext j; fin_cases j <;> rfl
  have hinput : final.input = d.input := rfl
  have hverdict : final.work 29 = d.output := rfl
  have hcells := input_cells_eq_of_reachesIn hd
  have hhead := (head_le_start_add_of_reachesIn original hd).2.2 (9 : Fin 11)
  change (d.work 9).head ≤ 1+t at hhead
  refine ⟨final,t,ht,hplaced,hh,?_,?_,?_,?_,?_⟩
  · simpa only [hinput,hwork,hverdict] using hraw
  · intro j hj
    have hnot : ¬placeWorkInMiddle 18 12 (post := 0) j := by simp [placeWorkInMiddle]; omega
    have he := placeWorkCfg_work_extra routed 18 0 (initialWork wit)
      (VerifierOutputRouting.wrap original (wordTape []) d) j hnot
    have hj27 : j ≠ 27 := by intro he'; subst j; omega
    exact he.trans (by simp only [initialWork,ite_eq_right hj27]; exact VerifierCountPrepare.unary_eq_reg 0)
  · exact hcells
  · change (d.work 9).head ≤ budget src wit+1
    change t ≤ budget src wit at ht
    omega
  · exact VerifierActivationProduce.ended_acc []

end UnconstrainedPACDetection.VerifierRawStage
