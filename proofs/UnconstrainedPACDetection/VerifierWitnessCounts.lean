module

public import proofs.UnconstrainedPACDetection.VerifierCountPrepare
public import proofs.UnconstrainedPACDetection.VerifierWorkPermutation

@[expose] public section

namespace UnconstrainedPACDetection.VerifierWitnessCounts
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierCountPrepare (pairFrame)

def placed : TM 6 := placeWorkTM 0 4 VerifierWitnessRegisters.machine
def permutation : Equiv.Perm (Fin 6) := (Equiv.swap 0 2).trans (Equiv.swap 1 5)
def scan : TM 6 := VerifierWorkPermutation.machine placed permutation

def stage (bits : List Bool) (converted : Bool) : Complexity.TM.TapePred 6 :=
  fun inp work out => Parked inp ∧ inp.cells = (wordTape bits).cells ∧
    ∃ m n b, VerifierWitnessRegisters.Meaning bits m n b ∧
      work = pairFrame m n converted converted ∧ OutAcc [b] out

theorem scan_hoare (bits : List Bool) : scan.HoareTime
    (fun inp work out => inp = wordTape bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (stage bits false) (2*bits.length+9) := by
  rintro inp work out ⟨rfl,rfl,rfl⟩
  obtain ⟨d,t,ht,hd,hh,hi,m,n,b,hm,hw,ho⟩ := VerifierWitnessRegisters.validation_hoare bits
    (wordTape bits) (fun _ => wordTape []) (wordTape [])
    ⟨(Tape.init_move_right_hasBinaryString bits).hasBinarySuffix,rfl,rfl⟩
  have hc := input_cells_eq_of_reachesIn hd
  have hge : 1 ≤ d.input.head := by
    have hne : d.input.head ≠ 0 := by
      intro hz
      apply hi.read_ne_start
      change d.input.cells d.input.head = Γ.start
      rw [hz,hc]; rfl
    omega
  have hpark : Parked d.input := by
    refine ⟨hge,?_⟩
    intro j hj
    rw [hc]
    exact ((Tape.StartInvariant.init_ofBool bits).move .right).2 j hj
  let base : Fin 6 → Tape := fun _ => wordTape []
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierWitnessRegisters.machine 0 4 base hd
    (by intro j _; exact (VerifierReactionLoop.word_parked []).read_ne_start)
  have hr := VerifierWorkPermutation.run_commute placed permutation hp
  let embed := fun c : Cfg 2 VerifierWitnessRegisters.machine.Q =>
    VerifierWorkPermutation.wrap placed permutation
      (placeWorkCfg VerifierWitnessRegisters.machine 0 4 base c)
  have he : embed ⟨VerifierWitnessRegisters.machine.qstart,wordTape bits,fun _ => wordTape [],wordTape []⟩ =
      (⟨scan.qstart,wordTape bits,fun _ => wordTape [],wordTape []⟩ : Cfg 6 scan.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  change scan.reachesIn t (embed _) (embed d) at hr
  rw [he] at hr
  refine ⟨embed d,t,ht,hr,hh,hpark,hc,m,n,b,hm,?_,?_⟩
  · funext j; fin_cases j <;>
      simp [embed,VerifierWorkPermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
        permutation,Equiv.swap_apply_def,base,hw,VerifierWitnessRegisters.pair,pairFrame]
  · change OutAcc [b] d.output
    rw [ho]
    exact VerifierEntityLoopBody.acc_of_prefix _ _ (VerifierVerdictCommit.one_prefix _ _) rfl

theorem stage_stable (bits : List Bool) (c : Bool) :
    ∀ inp work out, stage bits c inp work out →
      stage bits c (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have horig := h
  obtain ⟨hi,_,m,n,b,_,hw,ho⟩ := h
  have hp : ∀ j, (work j).read ≠ .start := by
    rw [hw]; intro j; exact (VerifierCountPrepare.pair_parked m n c c j).read_ne_start
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start hp ho.parked.read_ne_start
  simpa only [hi',hw',ho'] using horig

theorem convert_hoare (bits : List Bool) : VerifierCountPrepare.pairMachine.HoareTime
    (stage bits false) (stage bits true) (40*(bits.length+1)^2+5) := by
  rintro inp work out ⟨hi,hc,m,n,b,hm,hw,ho⟩
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := VerifierCountPrepare.pair_hoare m n inp hi b
    inp work out ⟨rfl,hw,ho⟩
  have hmL : m ≤ bits.length := by have := hm.1; omega
  have hnL : n ≤ bits.length := by have := hm.1; omega
  have hm2 : (m+1)^2 ≤ (bits.length+1)^2 := by gcongr
  have hn2 : (n+1)^2 ≤ (bits.length+1)^2 := by gcongr
  refine ⟨d,t,by omega,hd,hh,?_,?_,m,n,b,hm,hdw,hdo⟩
  · simpa only [hdi] using hi
  · exact congrArg Tape.cells hdi |>.trans hc

def machine : TM 6 := seqTM scan VerifierCountPrepare.pairMachine

theorem validation_hoare (bits : List Bool) : machine.HoareTime
    (fun inp work out => inp = wordTape bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (stage bits true) (40*(bits.length+1)^2+2*bits.length+15) := by
  have h := seqTM_hoareTime _ _ (scan_hoare bits) (stage_stable bits false) (convert_hoare bits)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierWitnessCounts
