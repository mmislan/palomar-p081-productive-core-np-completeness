module

public import proofs.UnconstrainedPACDetection.FormulaRuntimeBranch

@[expose] public section

namespace UnconstrainedPACDetection.FormulaNegativeChain
open Complexity Complexity.TM

def machine {n : Nat} (queries : List (TM n)) (body : TM n) : TM n :=
  queries.foldr (fun q m => seqTM q (FormulaNegativeGate.gate m)) body

def cost {n : Nat} (checks : List (TM n × Bool × Nat)) (B : Nat) : Nat :=
  (checks.map (fun q => q.2.2+3)).sum+B

theorem hoare {n : Nat} (checks : List (TM n × Bool × Nat)) (body : TM n)
    (inp : Tape) (w : Fin n → Tape) (zs : List Bool) (B : Nat)
    (hi : Parked inp) (hp : ∀ t, Parked (w t))
    (hq : ∀ q ∈ checks, ∀ ys, q.1.HoareTime (EmitPred inp w ys) (EmitPred inp w (ys ++ [q.2.1])) q.2.2)
    (hb : (∀ q ∈ checks, q.2.1=false) → ∀ ys,
      body.HoareTime (EmitPred inp w ys) (EmitPred inp w (ys ++ zs)) B) (ys : List Bool) :
    (machine (checks.map Prod.fst) body).HoareTime (EmitPred inp w ys)
      (EmitPred inp w (ys ++ if ∀ q ∈ checks, q.2.1=false then zs else [])) (cost checks B) := by
  induction checks with
  | nil =>
    simpa only [List.map_nil,machine,List.foldr_nil,List.not_mem_nil,IsEmpty.forall_iff,implies_true,
      forall_const,ite_true,cost,List.sum_nil,Nat.zero_add] using hb (by simp) ys
  | cons q qs ih =>
    obtain ⟨q,b,A⟩ := q
    have hq0 := hq (q,b,A) (by simp) ys
    cases b with
    | true =>
      have hs := FormulaRuntimeBranch.negative_skip (machine (qs.map Prod.fst) body) inp w ys hi hp
      have h := seqTM_hoareTime _ _ hq0 (emitPred_transition hi hp _) hs
      have hn : ¬(∀ z ∈ (q,true,A)::qs, z.2.1=false) := by
        intro hz; have hf := hz (q,true,A) (by simp); contradiction
      simpa only [machine,List.map_cons,List.foldr_cons,hn,ite_false,List.append_nil] using
        h.mono_bound (show A+1+2 ≤ cost ((q,true,A)::qs) B by simp [cost]; omega)
    | false =>
      have ht := ih (by intro z hz; exact hq z (by simp [hz])) (by
        intro hz; apply hb; intro z hmem
        rcases List.mem_cons.mp hmem with he | he
        · subst z; rfl
        · exact hz z he)
      have hg := FormulaNegativeGate.gate_hoare (machine (qs.map Prod.fst) body) false inp w ys
        (if ∀ z ∈ qs, z.2.1=false then zs else []) (cost qs B) hi hp ht
      simp only [Bool.false_eq_true,ite_false] at hg
      have h := seqTM_hoareTime _ _ hq0 (emitPred_transition hi hp _) hg
      have he : (∀ z ∈ (q,false,A)::qs, z.2.1=false) ↔ (∀ z ∈ qs, z.2.1=false) := by simp
      simpa only [machine,List.map_cons,List.foldr_cons,he] using
        h.mono_bound (show A+1+(cost qs B+2) ≤ cost ((q,false,A)::qs) B by simp [cost]; omega)

end UnconstrainedPACDetection.FormulaNegativeChain
