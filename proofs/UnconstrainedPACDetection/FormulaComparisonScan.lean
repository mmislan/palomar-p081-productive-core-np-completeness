module

public import proofs.UnconstrainedPACDetection.FormulaComparisonPrepare
public import proofs.UnconstrainedPACDetection.VerifierEqualityCommit

@[expose] public section

namespace UnconstrainedPACDetection.FormulaComparisonScan
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

abbrev base := VerifierEqualityCommit.scan

def after (xs ys : List Bool) (inp₀ : Tape) (emitted : List Bool) :
    Complexity.TM.TapePred 3 := fun inp work out =>
  inp = inp₀ ∧ (work 0).HasBinarySuffix [] ∧ (work 1).HasBinarySuffix [] ∧
  (work 0).cells = (word ys).cells ∧ (work 1).cells = (word xs).cells ∧
  OutAcc [VerifierBinaryEquality.compare true xs ys] (work 2) ∧ OutAcc emitted out

theorem base_hoare (xs ys : List Bool) (inp₀ : Tape) (emitted : List Bool)
    (hi : Parked inp₀) : base.HoareTime
      (EmitPred inp₀ ![word ys,word xs,word []] emitted)
      (after xs ys inp₀ emitted) (max xs.length ys.length+1) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  let s : Cfg 1 VerifierBinaryEquality.machine.Q :=
    ⟨some true,word xs,fun _ => word ys,word []⟩
  obtain ⟨d,hd,hh,hout,hxe,hye,hxc,hyc⟩ := VerifierBinaryEquality.boundary_frame
    xs ys true s rfl (Tape.init_move_right_hasBinaryString xs).hasBinarySuffix
    (Tape.init_move_right_hasBinaryString ys).hasBinarySuffix []
    Tape.init_nil_move_right_hasBinaryPrefix_nil
  have hb := VerifierEqualityCommit.retarget_run hd
    ((Tape.StartInvariant.init_ofBool xs).move .right) inp hi.read_ne_start
  have hr := VerifierOutputRouting.run_frame _ out ho.parked.read_ne_start hb
  let embed := fun z : Cfg 1 VerifierBinaryEquality.machine.Q =>
    VerifierOutputRouting.wrap VerifierEqualityCommit.buffered out
      (retargetWrap VerifierBinaryEquality.machine inp z)
  have hstart : embed s =
      (⟨VerifierEqualityCommit.scan.qstart, inp,
        ![word ys, word xs, word []], out⟩ : Cfg 3 VerifierEqualityCommit.scan.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  have h0 := output_cells_zero_eq_start_of_reachesIn hd rfl
  refine ⟨embed d,_,le_rfl,?_,hh,rfl,hye,hxe,hyc,hxc,?_,ho⟩
  · change VerifierEqualityCommit.scan.reachesIn _ (embed s) (embed d) at hr
    simpa only [hstart] using hr
  · exact FormulaLookupFrame.prefix_acc _ _
      (by simpa [embed, VerifierOutputRouting.wrap, retargetCfg] using hout) h0

def machine : TM 6 := placeWorkTM 2 1 base

def result (xs ys : List Bool) (inp₀ : Tape) (work₀ : Fin 6 → Tape)
    (emitted : List Bool) : Complexity.TM.TapePred 6 := fun inp work out =>
  inp = inp₀ ∧ (∀ j, j.val < 2 ∨ 5 ≤ j.val → work j = work₀ j) ∧
  (work 2).HasBinarySuffix [] ∧ (work 3).HasBinarySuffix [] ∧
  (work 2).cells = (word ys).cells ∧ (work 3).cells = (word xs).cells ∧
  OutAcc [VerifierBinaryEquality.compare true xs ys] (work 4) ∧
  OutAcc emitted out

/-- Actual buffered comparison on tapes 2 and 3, retaining its verdict on tape 4. -/
theorem scan_hoare (xs ys : List Bool) (inp₀ : Tape) (work₀ : Fin 6 → Tape)
    (emitted : List Bool) (hi : Parked inp₀) (hp : ∀ j, Parked (work₀ j))
    (h2 : work₀ 2 = word ys) (h3 : work₀ 3 = word xs) (h4 : work₀ 4 = word []) :
    machine.HoareTime (EmitPred inp₀ work₀ emitted)
      (result xs ys inp₀ work₀ emitted) (max xs.length ys.length+1) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  obtain ⟨d,t,ht,hd,hh,hdi,h0,h1,hc0,hc1,hv,hout⟩ := base_hoare xs ys inp emitted hi
    inp ![word ys,word xs,word []] out ⟨rfl,rfl,ho⟩
  have hr := placeWorkTM_reachesIn_placeWorkCfg_stable_internal base 2 1 work hd
    (by intro j _; exact (hp j).read_ne_start)
  refine ⟨placeWorkCfg base 2 1 work d,t,ht,?_,hh,hdi,?_,h0,h1,hc0,hc1,hv,hout⟩
  unfold machine
  · convert hr using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,h2,h3,h4]
    · rfl
  · intro j hj
    exact placeWorkCfg_work_extra base 2 1 work d j (by
      dsimp [placeWorkInMiddle]
      omega)

end UnconstrainedPACDetection.FormulaComparisonScan
