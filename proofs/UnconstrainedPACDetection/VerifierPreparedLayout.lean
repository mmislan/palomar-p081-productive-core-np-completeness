module

public import proofs.UnconstrainedPACDetection.VerifierActivationNonempty

@[expose] public section

namespace UnconstrainedPACDetection.VerifierPreparedLayout
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)

def join (p : Fin 14 → Tape) (a : Fin 4 → Tape) : Fin 18 → Tape :=
  fun j => if h : j.val < 14 then p ⟨j.val,h⟩ else a ⟨j.val-14,by omega⟩

theorem join_parked (p : Fin 14 → Tape) (a : Fin 4 → Tape)
    (hp : ∀ j, Parked (p j)) (ha : ∀ j, Parked (a j)) : ∀ j, Parked (join p a j) := by
  intro j
  by_cases h : j.val < 14
  · simpa only [join,dite_eq_left h] using hp ⟨j.val,h⟩
  · simpa only [join,dite_eq_right h] using ha ⟨j.val-14,by omega⟩

theorem activation_final_parked (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (inp : Tape) (work : Fin 4 → Tape) (out : Tape)
    (h : VerifierActivationNonempty.final s w inp work out) : ∀ j, Parked (work j) := by
  rcases h with ⟨_,h0,h3,hf,_⟩
  intro j
  by_cases hj0 : j = 0
  · subst j; rw [h0]
    exact ⟨by change 1 ≤ 2*w.mask.length+2; omega,
      ((Tape.StartInvariant.init_ofBool _).move .right).2⟩
  by_cases hj3 : j = 3
  · subst j; rw [h3]
    exact ⟨by change 1 ≤ 1+2*s.reactions; omega,
      ((Tape.StartInvariant.init_ofBool _).move .right).2⟩
  rw [hf j hj0 hj3]
  exact VerifierActivationProduce.frame_parked s w _ (VerifierReactionLoop.word_parked _) j

@[reducible] def activation : TM 18 := placeWorkTM 14 0 VerifierActivationNonempty.machine

theorem activation_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (w : BinaryWitnessData.Witness) (hm : w.mask.length = s.entities) (hw : w.flow.length = s.reactions)
    (p : Fin 14 → Tape) (hp : ∀ j, Parked (p j)) :
    activation.HoareTime
      (fun inp work out => inp.HasBinarySuffix (BinaryFields.encode (s.values.map Nat.bits)) ∧
        work = join p (VerifierActivationProduce.frame s w (wordTape [])) ∧ out = wordTape [])
      (fun inp work out => ∃ a, (∀ j, Parked (a j)) ∧ work = join p a ∧
        inp.HasBinarySuffix [] ∧ out = one .start (VerifierActivationNonempty.result s w))
      (50*(s.encode.length+2*w.encode.length+1)^2) := by
  rintro inp work out ⟨hi,hwork,hout⟩
  subst work; subst out
  obtain ⟨d,t,ht,hd,hh,hf⟩ := VerifierActivationNonempty.check_hoare s hs w hm hw
    inp (VerifierActivationProduce.frame s w (wordTape [])) (wordTape []) ⟨hi,rfl,rfl⟩
  let base := join p (VerifierActivationProduce.frame s w (wordTape []))
  have hb : ∀ j, Parked (base j) := join_parked _ _ hp
    (VerifierActivationProduce.frame_parked s w _ (VerifierReactionLoop.word_parked _))
  have hr := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierActivationNonempty.machine 14 0 base hd (by intro j _; exact (hb j).read_ne_start)
  refine ⟨placeWorkCfg VerifierActivationNonempty.machine 14 0 base d,t,ht,?_,hh,
    d.work,activation_final_parked s w _ _ _ hf,?_,hf.1,hf.2.2.2.2⟩
  · convert hr using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  · funext j
    fin_cases j <;> rfl

end UnconstrainedPACDetection.VerifierPreparedLayout
