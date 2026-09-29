module

public import proofs.UnconstrainedPACDetection.FormulaSides
public import proofs.UnconstrainedPACDetection.FormulaHeaders

@[expose] public section

namespace UnconstrainedPACDetection.FormulaHeaderFrame
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def small (src : List Bool) : Fin 7 → Tape :=
  ![regTape (FormulaHeaders.clauses src),regTape (FormulaHeaderPreparation.occurrences src),
    regTape (FormulaHeaderPreparation.maximum src+1),word [true],regTape (FormulaEntityHeader.value src),
    regTape (FormulaHeaders.value src),word (FormulaHeaders.value src).bits]

def frame (src : List Bool) (t : Fin 28) : Tape :=
  if h : t.val<7 then small src ⟨t.val,h⟩ else regTape 0

theorem small_parked (src : List Bool) : ∀ t, Parked (small src t) := by
  intro t; fin_cases t
  all_goals first | exact parked_regTape _ | exact word_parked _

theorem parked (src : List Bool) : ∀ t, Parked (frame src t) := by
  intro t; unfold frame; split
  · exact small_parked _ _
  · exact parked_regTape _

def initial (src : List Bool) : Complexity.TM.TapePred 28 := fun inp w out =>
  inp=Tape.init (src.map Γ.ofBool) ∧ (∀ t, w t=Tape.init []) ∧ out=Tape.init []

def machine : TM 28 := placeWorkTM 0 21 FormulaHeaders.machine

theorem hoare (src : List Bool) : machine.HoareTime (initial src)
    (EmitPred (word src) (frame src) (FormulaHeaders.fields src)) (FormulaHeaders.bound src) := by
  rintro inp w out ⟨rfl,hw,rfl⟩
  have hw' : w = fun _ => Tape.init [] := funext hw
  subst w
  obtain ⟨d,t,ht,hr,hh,hin,h0,h1,h2,h3,h4,h5,h6,ho⟩ := FormulaHeaders.ordinary_hoare src
    (Tape.init (src.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init []) ⟨rfl,fun _ => rfl,rfl⟩
  have hs : d.work = small src := by
    funext j; fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
  have hn : t≠0 := by
    intro he
    subst t
    cases hr
    have he := congrArg Tape.head hin
    change 0=1 at he
    omega
  obtain ⟨D,hD,hstate,hinput,houtput,hshape⟩ := placeWorkTM_reachesIn_init_internal FormulaHeaders.machine 0 21 src hr
  have hd := hshape.resolve_left hn
  refine ⟨D,t,ht,hD,hstate.trans hh,hinput.trans hin,?_,?_⟩
  · rw [hd]
    funext j
    fin_cases j <;> simp [placeWorkParkedCfg,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,hs,frame]
    all_goals exact FormulaParameters.empty_reg
  · rw [houtput]; exact ho

end UnconstrainedPACDetection.FormulaHeaderFrame
