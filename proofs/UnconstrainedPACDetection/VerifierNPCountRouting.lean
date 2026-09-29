module

public import proofs.UnconstrainedPACDetection.VerifierNPCount
public import proofs.UnconstrainedPACDetection.VerifierOutputRouting

@[expose] public section

namespace UnconstrainedPACDetection.VerifierNPCountRouting
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

abbrev original := VerifierNPCount.machine
def routed : TM 1 := original.retargetOutput
def machine : TM 33 := placeWorkTM 30 2 routed

def initial (src : List Bool) : Complexity.TM.TapePred 33 := fun inp work out =>
  inp = word src ∧ work = (fun _ => word []) ∧ out = word []

def after (src : List Bool) : Complexity.TM.TapePred 33 := fun inp work out =>
  inp.cells = (word src).cells ∧ Parked inp ∧ inp.head ≤ src.length+4 ∧
  OutAcc (List.replicate (src.length+1) true) (work 30) ∧
  (∀ j, j ≠ 30 → work j = word []) ∧ OutAcc [] out

theorem count_hoare (src : List Bool) : machine.HoareTime (initial src) (after src) (src.length+3) := by
  rintro inp work out ⟨rfl,rfl,rfl⟩
  obtain ⟨d,t,ht,hd,hh,hi,hcount⟩ := VerifierNPCount.count_hoare src
    (word src) VerifierNPCount.noWork (word [])
    ⟨(Tape.init_move_right_hasBinaryString src).hasBinarySuffix,outAcc_nil_init⟩
  have hrouted := VerifierOutputRouting.run_frame original (word []) (word_parked []).read_ne_start hd
  have hplaced := placeWorkTM_reachesIn_placeWorkCfg_stable_internal routed 30 2
    (fun _ => word []) hrouted (by intro _ _; exact (word_parked []).read_ne_start)
  have hstart : placeWorkCfg routed 30 2 (fun _ => word [])
      (VerifierOutputRouting.wrap original (word [])
        ⟨original.qstart,word src,VerifierNPCount.noWork,word []⟩) =
      (⟨machine.qstart,word src,fun _ => word [],word []⟩ : Cfg 33 machine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  rw [hstart] at hplaced
  let final := placeWorkCfg routed 30 2 (fun _ => word [])
    (VerifierOutputRouting.wrap original (word []) d)
  have hbound := (head_le_start_add_of_reachesIn original hd).1
  change d.input.head ≤ 1+t at hbound
  refine ⟨final,t,ht,hplaced,hh,input_cells_eq_of_reachesIn hd,⟨hi.1,hi.2.2.2⟩,
    by change d.input.head ≤ src.length+4; omega,hcount,?_,outAcc_nil_init⟩
  intro j hj
  have hnot : ¬placeWorkInMiddle 30 1 (post := 2) j := by
    intro h
    have hv : j.val = 30 := by dsimp [placeWorkInMiddle] at h; omega
    exact hj (Fin.ext hv)
  exact placeWorkCfg_work_extra routed 30 2 (fun _ => word [])
    (VerifierOutputRouting.wrap original (word []) d) j hnot

end UnconstrainedPACDetection.VerifierNPCountRouting
