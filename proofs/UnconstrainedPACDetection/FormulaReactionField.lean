module

public import proofs.UnconstrainedPACDetection.FormulaEntityHeader

@[expose] public section

namespace UnconstrainedPACDetection.FormulaReactionField
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def swap : Equiv.Perm (Fin 7) := (Equiv.swap 4 6).trans ((Equiv.swap 4 5).trans (Equiv.swap 4 3))
@[reducible] def numberPlaced : TM 7 := placeWorkTM 4 0 FormulaNumberField.machine
@[reducible] def emit : TM 7 := VerifierWorkPermutation.machine numberPlaced swap

def afterWork (w : Fin 7 → Tape) (v : Nat) : Fin 7 → Tape :=
  Function.update (Function.update w 3 (word [true])) 6 (word v.bits)

theorem emit_hoare (v : Nat) (inp : Tape) (w : Fin 7 → Tape) (ys : List Bool)
    (hi : Parked inp) (hp : ∀ j, Parked (w j))
    (h5 : w 5 = regTape v) (h3 : w 3 = word []) (h6 : w 6 = word []) :
    emit.HoareTime (EmitPred inp w ys)
      (EmitPred inp (afterWork w v) (ys ++ BinaryFields.encodeField v.bits))
      (24*(v+1)^2+8) := by
  rintro i ws o ⟨hin,hw,ho⟩
  subst i; subst ws
  let base : Fin 7 → Tape := fun j => w (swap j)
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := FormulaNumberField.field_bounded v inp hi ys
    inp (VerifierCountPrepare.initial v) o ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    FormulaNumberField.machine 4 0 base hr
    (by intro j _; exact (hp (swap j)).read_ne_start)
  have hrouted := VerifierWorkPermutation.run_commute numberPlaced swap hs
  refine ⟨VerifierWorkPermutation.wrap numberPlaced swap (placeWorkCfg _ 4 0 base d),
    t,ht,?_,hh,hdi,?_,hdo⟩
  · convert hrouted using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;>
        simp [VerifierWorkPermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
          base,swap,Equiv.swap_apply_def,Equiv.trans_apply,VerifierCountPrepare.initial,
          VerifierCountPrepare.unary_eq_reg,h5,h3,h6]
      all_goals rfl
    · rfl
  · funext j
    fin_cases j <;>
      simp [VerifierWorkPermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
        base,swap,Equiv.swap_apply_def,Equiv.trans_apply,FormulaNumberField.bank,hdw,afterWork,h5]


end UnconstrainedPACDetection.FormulaReactionField
