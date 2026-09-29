module

public import proofs.UnconstrainedPACDetection.VerifierVerdictAnd

@[expose] public section

namespace UnconstrainedPACDetection.VerifierVerdictCommit
open Complexity Complexity.TM
open VerifierVerdictAnd (one empty)

def machine : TM 12 := placeWorkTM 11 0 VerifierVerdictAnd.machine

theorem one_prefix (m : Γ) (b : Bool) : (one m b).HasBinaryPrefix [b] := by
  refine ⟨rfl,?_,?_⟩
  · intro i hi
    have h : i = 0 := by simpa using hi
    subst i; simp [one]
  · intro i hi
    have h0 : i ≠ 0 := by simp only [List.length_singleton] at hi; omega
    simp [one,h0]

theorem empty_start : empty .start = VerifierBufferedProduct.wordTape [] := by
  apply Tape.ext
  · rfl
  · funext i
    by_cases h : i = 0 <;> simp [empty,VerifierBufferedProduct.wordTape,Tape.init,Tape.move,h]

theorem commit_hoare (v a : Bool) (w : Fin 12 → Tape) (inp₀ out₀ : Tape)
    (hv : (w 11).HasBinaryPrefix [v]) (ha : out₀.HasBinaryPrefix [a])
    (hm : (w 11).cells 0 = .start)
    (hf : ∀ j, j ≠ 11 → (w j).read ≠ .start) (hi : inp₀.read ≠ .start) :
    machine.HoareTime (VerifierTapeCleanup.frame w inp₀ out₀)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update w 11 (VerifierBufferedProduct.wordTape []) ∧
        out.HasBinaryPrefix [v && a] ∧ out.cells 0 = out₀.cells 0) 2 := by
  rintro inp work out ⟨hin,hwork,hout⟩
  subst inp; subst work; subst out
  have hv' : w 11 = one .start v := by
    rw [VerifierVerdictAnd.prefix_eq (w 11) v hv,hm]
  have ha' := VerifierVerdictAnd.prefix_eq out₀ a ha
  let c : Cfg 1 (Fin 3) := ⟨0,inp₀,fun _ => one .start v,one (out₀.cells 0) a⟩
  let d : Cfg 1 (Fin 3) := ⟨2,inp₀,fun _ => empty .start,one (out₀.cells 0) (v && a)⟩
  have hr := VerifierVerdictAnd.run inp₀ hi .start (out₀.cells 0) v a
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal VerifierVerdictAnd.machine 11 0 w hr (by
    intro j hj
    apply hf j
    intro h; subst j; simp [placeWorkInMiddle] at hj)
  have he : placeWorkCfg VerifierVerdictAnd.machine 11 0 w c =
      (⟨machine.qstart,inp₀,w,out₀⟩ : Cfg 12 machine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,c,hv']
    · exact ha'.symm
  refine ⟨placeWorkCfg VerifierVerdictAnd.machine 11 0 w d,2,le_rfl,?_,rfl,rfl,?_,?_,?_⟩
  · change machine.reachesIn 2 (placeWorkCfg VerifierVerdictAnd.machine 11 0 w c)
      (placeWorkCfg VerifierVerdictAnd.machine 11 0 w d) at hp
    simpa only [he] using hp
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,d,empty_start]
  · exact one_prefix _ _
  · simp [placeWorkCfg,d,one]

end UnconstrainedPACDetection.VerifierVerdictCommit
