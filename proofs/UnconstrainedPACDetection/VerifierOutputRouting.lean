module

public import proofs.UnconstrainedPACDetection.VerifierEntityRestart
public import proofs.Complexitylib.Models.TuringMachine.Lift

@[expose] public section

/-! Output routing with an arbitrary preserved real output, adapting the
existing Complexitylib retargetOutput proof (Apache-2.0). -/
namespace UnconstrainedPACDetection.VerifierOutputRouting
open Complexity Complexity.TM
variable {n : ℕ}

def wrap (tm : TM n) (out₀ : Tape) (c : Cfg n tm.Q) : Cfg (n+1) tm.Q :=
  { tm.retargetCfg c with output := out₀ }

theorem step_frame (tm : TM n) (out₀ : Tape) (hout : out₀.read ≠ .start) {c : Cfg n tm.Q}
    {C : Cfg (n + 1) tm.Q}
    (hs : C.state = c.state) (hi : C.input = c.input)
    (hw : ∀ (i : Fin (n + 1)) (h : i.val < n), C.work i = c.work ⟨i.val, h⟩)
    (hlast : C.work (Fin.last n) = c.output)
    (ho : C.output = out₀) :
    (tm.retargetOutput).step C = (tm.step c).map (wrap tm out₀) := by
  by_cases hh : c.state = tm.qhalt
  · -- both machines are halted
    have h1 : (tm.retargetOutput).step C = none := by
      dsimp only [retargetOutput]
      simp only [step, hs, hh, ↓reduceIte]
    have h2 : tm.step c = none := by
      simp only [step, hh, ↓reduceIte]
    rw [h1, h2]; rfl
  · cases hstep : tm.step c with
    | none => exact absurd hstep (by simp [step, hh])
    | some c' =>
      -- extract the explicit stepped configuration
      simp only [step, hh, ↓reduceIte, Option.some.injEq] at hstep
      subst hstep
      have hinner : (fun i : Fin n => (C.work (Fin.castSucc i)).read)
          = fun i => (c.work i).read :=
        funext fun i => by rw [hw (Fin.castSucc i) i.isLt]; rfl
      have hvirt : (C.work (Fin.last n)).read = c.output.read := by rw [hlast]
      dsimp only [retargetOutput]
      simp only [step, Option.map_some]
      dsimp only [wrap, retargetCfg]
      rw [hs, hi, hinner, hvirt, ite_eq_right hh]
      refine congrArg some (Cfg.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, ?_, ?_⟩)
      · funext i
        by_cases hik : i.val < n
        · rw [hw i hik, dite_eq_left hik, dite_eq_left hik, dite_eq_left hik]
        · have hi_last : i = Fin.last n := by
            apply Fin.ext
            have := i.isLt
            simp only [Fin.val_last]
            omega
          rw [dite_eq_right hik, dite_eq_right hik, dite_eq_right hik, hi_last, hlast]
      · rw [ho]; exact transitionTape_eq_self hout


theorem run_frame (tm : TM n) (out₀ : Tape) (hout : out₀.read ≠ .start)
    {t : ℕ} {c d : Cfg n tm.Q} (h : tm.reachesIn t c d) :
    tm.retargetOutput.reachesIn t (wrap tm out₀ c) (wrap tm out₀ d) := by
  induction h with
  | zero => exact .zero
  | @step c₀ _ _ _ hs _ ih =>
    have hh := step_frame tm out₀ hout (c := c₀) (C := wrap tm out₀ c₀) rfl rfl
      (fun _ h => dite_eq_left h) (retargetCfg_work_last tm c₀) rfl
    exact .step (by rw [hh,hs]; rfl) ih

theorem entity_run (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) (out₀ : Tape) (hout : out₀.read ≠ .start)
    (c : Cfg 11 VerifierEntityRestart.machine.Q) (hq : c.state = VerifierEntityRestart.machine.qstart)
    (hp : VerifierReactionLoop.sourcePred (VerifierCanonicalLoop.suffix s hn false x 0) c.input ∧
      c.input.cells = (VerifierBufferedProduct.wordTape s.encode).cells ∧
      c.input.head ≤ s.encode.length+1 ∧
      c.work = VerifierReactionLoop.frame 1 (s.entities-1) (s.reactions-1)
        (VerifierBufferedProduct.wordTape w.encode) [] [] ∧ OutAcc [] c.output) :
    ∃ d t, t ≤ 17000*(VerifierCanonicalBuffers.envelope s w [] []+1)^3 ∧
      VerifierEntityRestart.machine.retargetOutput.reachesIn t
        (wrap VerifierEntityRestart.machine out₀ c) (wrap VerifierEntityRestart.machine out₀ d) ∧
      VerifierEntityRestart.machine.halted d ∧
      VerifierCursorReset.pred [VerifierEntityCheck.verdict s hn x w] 1
        (s.entities-1) (s.reactions-1) (VerifierBufferedProduct.wordTape w.encode) [] [] s.encode
        d.input d.work d.output ∧
      (wrap VerifierEntityRestart.machine out₀ d).output = out₀ ∧
      ((wrap VerifierEntityRestart.machine out₀ d).work (Fin.last 11)).HasBinaryPrefix
        [VerifierEntityCheck.verdict s hn x w] := by
  obtain ⟨d,t,ht,hd,hh,hpost⟩ := VerifierEntityRestart.entity_hoare s hs hn x w hw
    c.input c.work c.output hp
  have hc : (⟨VerifierEntityRestart.machine.qstart,c.input,c.work,c.output⟩ :
      Cfg 11 VerifierEntityRestart.machine.Q) = c := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · rfl
    · rfl
  rw [hc] at hd
  refine ⟨d,t,ht,run_frame _ out₀ hout hd,hh,hpost,rfl,?_⟩
  change (VerifierEntityRestart.machine.retargetCfg d).work (Fin.last 11) |>.HasBinaryPrefix _
  rw [retargetCfg_work_last]
  exact hpost.2.2

end UnconstrainedPACDetection.VerifierOutputRouting
