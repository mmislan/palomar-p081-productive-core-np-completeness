module

public import proofs.IrrRAFEnumeration.CompletionClauseRange

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

def selectRead {k : Nat} (reader : Option (Fin k)) (i : Γ) (w : Fin k → Γ) : Γ :=
  match reader with
  | none => i
  | some j => w j

/-- Read an input symbol or saved flag once; preserve all tapes at the branch. -/
def onReadTM {k : Nat} (reader : Option (Fin k)) (symbol : Γ) (body : TM k) : TM k where
  Q := Option body.Q
  qstart := none
  qhalt := some body.qhalt
  δ := fun q i w o => match q with
    | none => (some (if selectRead reader i w = symbol then body.qstart else body.qhalt),
        fun j => readBackWrite (w j), readBackWrite o,
        idleDir i, fun j => idleDir (w j), idleDir o)
    | some q => let (q',w',o',di,dw,do') := body.δ q i w o
                (some q',w',o',di,dw,do')
  δ_right_of_start := by
    intro q i w o
    cases q with
    | none => exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩
    | some q => exact body.δ_right_of_start q i w o

def onReadCfg {k : Nat} (reader : Option (Fin k)) (symbol : Γ) (body : TM k) (c : Cfg k body.Q) :
    Cfg k (onReadTM reader symbol body).Q := ⟨some c.state,c.input,c.work,c.output⟩

theorem onRead_step {k : Nat} (reader : Option (Fin k)) (symbol : Γ) (body : TM k) (c : Cfg k body.Q) :
    (onReadTM reader symbol body).step (onReadCfg reader symbol body c) =
      (body.step c).map (onReadCfg reader symbol body) := by
  by_cases hh : c.state = body.qhalt
  · simp [TM.step,onReadTM,onReadCfg,hh]
    rfl
  · simp [TM.step,onReadTM,onReadCfg,hh]
    rfl

theorem onRead_entry {k : Nat} (reader : Option (Fin k)) (symbol : Γ) (body : TM k)
    (inp : Tape) (work : Fin k → Tape) (out : Tape)
    (hp : Parked inp) (hw : ∀ j, Parked (work j)) (ho : Parked out) :
    (onReadTM reader symbol body).step ⟨none,inp,work,out⟩ = some
      ⟨some (if selectRead reader inp.read (fun j => (work j).read) = symbol then body.qstart else body.qhalt),inp,work,out⟩ := by
  simp only [TM.step,onReadTM,reduceCtorEq,↓reduceIte]
  apply congrArg some
  refine Cfg.ext rfl hp.move_idle ?_ ho.writeAndMove_readBack_idle
  funext j
  exact (hw j).writeAndMove_readBack_idle

theorem onRead_emit_correct {k : Nat} (reader : Option (Fin k)) (symbol : Γ) (body : TM k)
    (inp : Tape) (work : Fin k → Tape) (ys zs : List Bool) (b : Nat)
    (hp : Parked inp) (hw : ∀ j, Parked (work j))
    (hb : body.HoareTime (EmitPred inp work ys) (EmitPred inp work (ys++zs)) b) :
    (onReadTM reader symbol body).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys++if selectRead reader inp.read (fun j => (work j).read) = symbol then zs else [])) (b+1) := by
  rintro inp' work' out ⟨hi,hw',ho⟩
  subst inp'
  subst work'
  have he := onRead_entry reader symbol body inp work out hp hw ho.parked
  by_cases hs : selectRead reader inp.read (fun j => (work j).read) = symbol
  · rw [ite_eq_left hs] at he
    obtain ⟨c,t,ht,hr,hh,hi,hw',hout⟩ := hb inp work out ⟨rfl,rfl,ho⟩
    have hl : (onReadTM reader symbol body).reachesIn t
        (onReadCfg reader symbol body ⟨body.qstart,inp,work,out⟩) (onReadCfg reader symbol body c) := by
      exact reachesIn_map (onReadCfg reader symbol body)
        (fun a b h => by rw [onRead_step,h]; rfl) hr
    refine ⟨onReadCfg reader symbol body c,t+1,by omega,.step he hl,?_,hi,hw',?_⟩
    · change some c.state = some body.qhalt
      exact congrArg some hh
    · simpa [hs,onReadCfg] using hout
  · rw [ite_eq_right hs] at he
    refine ⟨⟨some body.qhalt,inp,work,out⟩,1,by omega,.step he .zero,rfl,rfl,rfl,?_⟩
    simpa [hs] using ho

def unitClauseTM {k : Nat} (sign : Bool) (index : Fin k) : TM k :=
  seqTM (emitLitTM sign index) (emitBitsTM [true,false])

theorem unitClauseTM_correct {k : Nat} (sign : Bool) (index : Fin k) (v : Nat)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ j, Parked (work j)) (hi : work index = regTape v) :
    (unitClauseTM sign index).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys++SAT.CNF.encode [[⟨sign,v⟩]])) (3*v+12) := by
  have h1 := emitLitTM_hoareTime sign index v inp work ys hp (fun j _ => hw j)
    (by rw [hi]; exact reg_regT v)
  have h2 := emitBitsTM_hoareTime [true,false] inp work
    (ys++([sign,sign]++List.replicate (2*v) true++[false,true])) hp hw
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw _) h2
  unfold EmitPred at h ⊢
  simpa [unitClauseTM,SAT.CNF.encode_cons,SAT.Clause.encode_cons',List.append_assoc,
    Nat.add_assoc] using h

def excludedUnitTM {k : Nat} (index : Fin k) : TM k :=
  onReadTM none Γ.zero (unitClauseTM false index)

theorem excludedUnitTM_correct {k : Nat} (index : Fin k) (v : Nat) (bit : Bool)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ j, Parked (work j)) (hi : work index = regTape v)
    (hbit : inp.read = Γ.ofBool bit) :
    (excludedUnitTM index).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys++SAT.CNF.encode (if bit then [] else [[⟨false,v⟩]])))
      (3*v+13) := by
  have h := onRead_emit_correct none Γ.zero (unitClauseTM false index) inp work ys
    (SAT.CNF.encode [[⟨false,v⟩]]) (3*v+12) hp hw
    (unitClauseTM_correct false index v inp work ys hp hw hi)
  cases bit <;> simpa [excludedUnitTM,selectRead,hbit,Γ.ofBool,Nat.add_assoc] using h

/-- A saved 0/1 membership flag controls the negative unit clause. -/
def excludedFlagTM {k : Nat} (flag index : Fin k) : TM k :=
  onReadTM (some flag) Γ.blank (unitClauseTM false index)

theorem excludedFlagTM_correct {k : Nat} (flag index : Fin k) (v : Nat) (bit : Bool)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ j, Parked (work j)) (hi : work index = regTape v)
    (hflag : work flag = regTape (if bit then 1 else 0)) :
    (excludedFlagTM flag index).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys++SAT.CNF.encode (if bit then [] else [[⟨false,v⟩]])))
      (3*v+13) := by
  have h := onRead_emit_correct (some flag) Γ.blank (unitClauseTM false index) inp work ys
    (SAT.CNF.encode [[⟨false,v⟩]]) (3*v+12) hp hw
    (unitClauseTM_correct false index v inp work ys hp hw hi)
  cases bit <;> simpa [excludedFlagTM,selectRead,hflag,Tape.read,regTape,regCells,
    Nat.add_assoc] using h

end IrrRAFEnumeration.CompletionQuery
