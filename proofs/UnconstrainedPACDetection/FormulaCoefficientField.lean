module

public import proofs.UnconstrainedPACDetection.FormulaClauseCompare

@[expose] public section

namespace UnconstrainedPACDetection.FormulaCoefficientField
open Complexity Complexity.TM

def suffix (double : Bool) : List Bool :=
  if double then [false,true,true,false] else [true,false]

def amount (double v : Bool) : Nat := if v then (if double then 2 else 1) else 0

theorem field_bits (double v : Bool) :
    [v] ++ (if v then suffix double else []) =
      BinaryFields.encodeField (amount double v).bits := by
  cases double <;> cases v <;> decide

/-- Reuse the preceding verdict as the field's first bit, then append its suffix. -/
def machine {n : Nat} (double : Bool) : TM n where
  Q := Fin 2 ⊕ (emitBitsTM (n := n) (suffix double)).Q
  qstart := .inl 0
  qhalt := .inr (emitBitsTM (suffix double)).qhalt
  δ := fun q i w o => match q with
    | .inl k => if k = 0 then
        (.inl 1,fun j => readBackWrite (w j),readBackWrite o,idleDir i,
          fun j => idleDir (w j),moveLeftDir o)
      else
        (.inr (if o = .one then (emitBitsTM (suffix double)).qstart
          else (emitBitsTM (suffix double)).qhalt),
          fun j => readBackWrite (w j),readBackWrite o,idleDir i,
          fun j => idleDir (w j),.right)
    | .inr k =>
      let (q',wr,ow,di,dw,dout) := (emitBitsTM (suffix double)).δ k i w o
      (.inr q',wr,ow,di,dw,dout)
  δ_right_of_start := by
    intro q i w o
    cases q with
    | inl k =>
      by_cases hk : k = 0
      · simp only [hk,↓reduceIte]
        exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,moveLeftDir_right_of_start⟩
      · simp only [hk,↓reduceIte]
        exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,fun _ => True.intro⟩
    | inr k => exact (emitBitsTM (suffix double)).δ_right_of_start k i w o

def wrap {n : Nat} (double : Bool) (c : Cfg n (emitBitsTM (n := n) (suffix double)).Q) :
    Cfg n (machine (n := n) double).Q := ⟨.inr c.state,c.input,c.work,c.output⟩

theorem emit_step {n : Nat} (double : Bool)
    {c d : Cfg n (emitBitsTM (n := n) (suffix double)).Q}
    (h : (emitBitsTM (suffix double)).step c = some d) :
    (machine double).step (wrap double c) = some (wrap double d) := by
  have hn := state_ne_qhalt_of_step h
  simp only [TM.step,hn,↓reduceIte,Option.some.injEq] at h
  subst d
  simp [TM.step,machine,wrap,hn]

theorem emit_run {n : Nat} (double : Bool) {t : Nat}
    {c d : Cfg n (emitBitsTM (n := n) (suffix double)).Q}
    (h : (emitBitsTM (suffix double)).reachesIn t c d) :
    (machine double).reachesIn t (wrap double c) (wrap double d) := by
  induction h with
  | zero => exact .zero
  | step hs _ ih => exact .step (emit_step double hs) ih

theorem inspect_run {n : Nat} (double v : Bool) (inp : Tape) (w : Fin n → Tape)
    (ys : List Bool) (out : Tape) (hi : Parked inp) (hw : ∀ j, Parked (w j))
    (ho : OutAcc (ys ++ [v]) out) :
    (machine double).reachesIn 2 ⟨.inl 0,inp,w,out⟩
      ⟨.inr (if v then (emitBitsTM (suffix double)).qstart else
        (emitBitsTM (suffix double)).qhalt),inp,w,out⟩ := by
  have hh : out.head = ys.length+2 := by simpa using ho.head_eq
  let prev := out.move .left
  have hp : prev.head = ys.length+1 := by simp [prev,Tape.move,hh]
  have hr : prev.read = Γ.ofBool v := by
    change out.cells prev.head = _
    rw [hp]
    simpa using ho.2.2.1 ys.length (by simp)
  have hs1 : (machine double).step ⟨.inl 0,inp,w,out⟩ =
      some ⟨.inl 1,inp,w,prev⟩ := by
    simp only [TM.step,machine,reduceCtorEq,↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · exact transitionInput_eq_self hi.read_ne_start
    · funext j; exact (hw j).writeAndMove_readBack_idle
    · rw [writeAndMove_readBack _ ho.parked.read_ne_start]
      simp [moveLeftDir,ho.read_blank,prev]
  have hs2 : (machine double).step ⟨.inl 1,inp,w,prev⟩ =
      some ⟨.inr (if v then (emitBitsTM (suffix double)).qstart else
        (emitBitsTM (suffix double)).qhalt),inp,w,out⟩ := by
    simp only [TM.step,machine,reduceCtorEq,show (1 : Fin 2) ≠ 0 by decide,↓reduceIte]
    congr 1
    apply Cfg.ext
    · rw [hr]; cases v <;> rfl
    · exact transitionInput_eq_self hi.read_ne_start
    · funext j; exact (hw j).writeAndMove_readBack_idle
    · rw [writeAndMove_readBack _ (by rw [hr]; cases v <;> decide)]
      apply Tape.ext
      · simp [Tape.move,hp,hh]
      · rfl
  exact .step hs1 (.step hs2 .zero)

/-- Actual prefix-preserving expansion of a comparison bit into coefficient 0, 1 or 2. -/
theorem field_hoare {n : Nat} (double v : Bool) (inp : Tape) (w : Fin n → Tape)
    (ys : List Bool) (hi : Parked inp) (hw : ∀ j, Parked (w j)) :
    (machine double).HoareTime (EmitPred inp w (ys ++ [v]))
      (EmitPred inp w (ys ++ BinaryFields.encodeField (amount double v).bits)) 6 := by
  rintro i work out ⟨hin,hwork,ho⟩
  subst i
  subst work
  have hs := inspect_run double v inp w ys out hi hw ho
  cases v with
  | false =>
    refine ⟨_,2,by omega,hs,rfl,rfl,rfl,?_⟩
    simpa [amount,BinaryFields.encodeField] using ho
  | true =>
    obtain ⟨d,hd,hh,hdi,hdw,hdo⟩ := emitBitsTM_reachesIn_frame (suffix double) inp w
      out (ys ++ [true]) hi hw ho
    refine ⟨wrap double d,2+(suffix double).length,?_,reachesIn_trans _ hs (emit_run double hd),
      ?_,hdi,hdw,?_⟩
    · cases double <;> decide
    · change Sum.inr d.state = (Sum.inr (emitBitsTM (suffix double)).qhalt : (machine double).Q)
      exact congrArg Sum.inr hh
    · have he : [true] ++ suffix double =
          BinaryFields.encodeField (amount double true).bits := by simpa using field_bits double true
      change OutAcc (ys ++ BinaryFields.encodeField (amount double true).bits) d.output
      rw [← he]
      simpa only [List.append_assoc] using hdo

end UnconstrainedPACDetection.FormulaCoefficientField
