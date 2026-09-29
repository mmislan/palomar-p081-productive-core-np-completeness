module

public import proofs.UnconstrainedPACDetection.VerifierEntityAccumulate

@[expose] public section

namespace UnconstrainedPACDetection.VerifierEntityNavigate
open Complexity Complexity.TM
open VerifierSourceStride (small small_hoare)
open VerifierIndexedField (counter)
open VerifierCanonicalCoordinates (sourcePrefix source_split sourcePrefix_length valueIndex)
open VerifierCanonicalLoop (reaction suffix)

def machine : TM 13 := placeWorkTM 12 0 small

theorem skip_hoare (fields : List (List Bool)) (suffix : List Bool) (frame : Fin 13 → Tape) (out₀ : Tape)
    (hc : frame 12 = counter fields.length)
    (hf : ∀ j, j ≠ 12 → (frame j).read ≠ .start)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    machine.HoareTime
      (fun inp work out => inp.HasBinarySuffix (BinaryFields.encode fields ++ suffix) ∧ work = frame ∧ out = out₀)
      (fun inp work out => inp.HasBinarySuffix suffix ∧ work = frame ∧ out = out₀)
      ((BinaryFields.encode fields).length+2*fields.length+5) := by
  rintro inp work out ⟨hi,hw,ho'⟩
  subst work
  subst out
  obtain ⟨d,t,hb,hd,hh,hin,hdw,hout⟩ := small_hoare fields suffix out₀ ho hoh
    inp (fun _ => counter fields.length) out₀ ⟨hi,rfl,rfl⟩
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal small 12 0 frame hd (by
    intro j hj
    apply hf j
    intro he
    subst j
    simp [placeWorkInMiddle] at hj)
  have he : placeWorkCfg small 12 0 frame ⟨small.qstart,inp,fun _ => counter fields.length,out₀⟩ =
      (⟨machine.qstart,inp,frame,out₀⟩ : Cfg 13 machine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,hc]
    · rfl
  refine ⟨placeWorkCfg small 12 0 frame d,t,hb,?_,hh,hin,?_,hout⟩
  · change machine.reachesIn _ _ _ at hp
    simpa only [he] using hp
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,hdw,hc]

theorem prefix_length (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) :
    (sourcePrefix s false (reaction s hn 0) x).length = 2+x.val := by
  rw [sourcePrefix_length s hs]
  simp [valueIndex,reaction]

theorem navigate_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : Fin 13 → Tape) (out₀ : Tape)
    (hc : w 12 = counter (2+x.val))
    (hf : ∀ j, j ≠ 12 → (w j).read ≠ .start)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    machine.HoareTime
      (fun inp work out => inp.HasBinarySuffix s.encode ∧ work = w ∧ out = out₀)
      (fun inp work out => inp.HasBinarySuffix (suffix s hn false x 0) ∧ work = w ∧ out = out₀)
      (3*s.encode.length+9) := by
  let fs := sourcePrefix s false (reaction s hn 0) x
  have hsplit : s.encode = BinaryFields.encode fs ++ suffix s hn false x 0 :=
    source_split s hs false (reaction s hn 0) x
  have hlen : fs.length = 2+x.val := prefix_length s hs hn x
  have h := skip_hoare fs (suffix s hn false x 0) w out₀ (by rw [hlen]; exact hc) hf ho hoh
  rw [← hsplit] at h
  have he : (BinaryFields.encode fs).length ≤ s.encode.length := by
    rw [hsplit,List.length_append]; omega
  have hm := VerifierEntitySum.entity_count s hs hn
  have hx := x.isLt
  exact h.mono_bound (by rw [hlen]; omega)

theorem head_bound (src : List Bool) (inp : Tape)
    (hc : inp.cells = (VerifierBufferedProduct.wordTape src).cells)
    (hb : inp.read ≠ .blank) : inp.head ≤ src.length := by
  by_contra h
  have hh : inp.head-1+1 = inp.head := by omega
  have he := Tape.init_cells_ge (src.map Γ.ofBool) (inp.head-1) (by simp; omega)
  apply hb
  change inp.cells inp.head = .blank
  rw [hc]
  change (Tape.init (src.map Γ.ofBool)).cells inp.head = .blank
  simpa only [hh] using he

theorem navigate_prepared (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : Fin 13 → Tape) (out₀ : Tape)
    (hc : w 12 = counter (2+x.val))
    (hf : ∀ j, j ≠ 12 → (w j).read ≠ .start)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    machine.HoareTime
      (fun inp work out => inp.HasBinarySuffix s.encode ∧
        inp.cells = (VerifierBufferedProduct.wordTape s.encode).cells ∧ work = w ∧ out = out₀)
      (fun inp work out => inp.HasBinarySuffix (suffix s hn false x 0) ∧
        inp.cells = (VerifierBufferedProduct.wordTape s.encode).cells ∧ inp.head ≤ s.encode.length+1 ∧
        work = w ∧ out = out₀) (3*s.encode.length+9) := by
  rintro inp work out ⟨hin,hcells,hwork,hout⟩
  obtain ⟨d,t,ht,hd,hh,hi,hw,ho'⟩ := navigate_hoare s hs hn x w out₀ hc hf ho hoh
    inp work out ⟨hin,hwork,hout⟩
  have hcells' : d.input.cells = (VerifierBufferedProduct.wordTape s.encode).cells :=
    (input_cells_eq_of_reachesIn hd).trans hcells
  have hne : suffix s hn false x 0 ≠ [] := by
    unfold suffix
    cases (VerifierCanonicalCoordinates.coefficient s false (reaction s hn 0) x).bits <;>
      simp [BinaryFields.encodeField]
  have hread : d.input.read ≠ .blank := by
    generalize he : suffix s hn false x 0 = bits at hi hne
    cases bits with
    | nil => contradiction
    | cons b bs => cases b <;> simp [hi.read_cons,Γ.ofBool]
  exact ⟨d,t,ht,hd,hh,hi,hcells',by have := head_bound s.encode d.input hcells' hread; omega,hw,ho'⟩

end UnconstrainedPACDetection.VerifierEntityNavigate
