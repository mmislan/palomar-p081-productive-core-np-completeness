module

public import proofs.IrrRAFEnumeration.PositiveCompletionReduction
public import proofs.IrrRAFEnumeration.PositiveEnumeration

@[expose] public section

namespace IrrRAFEnumeration.PositiveCompletionCNF
open RAF Complexity.SAT

/-- The chemistry is fixed throughout enumeration. -/
def baseFormula {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] : CNF :=
  formula Q C [] Finset.univ

/-- A completed minimal output excludes its entire upward cone. -/
def outputBlockers {r : Nat} (G : List (Finset (Fin r))) : CNF :=
  G.map (fun I => negative (members (fun j => j ∈ I) selectVar))

/-- These clauses are temporary: each trial starts with fresh exclusions. -/
def containerExclusions {r : Nat} (U : Finset (Fin r)) : CNF :=
  each r (fun j => if j ∈ U then [] else [negative [selectVar j]])

def baseQuery {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) : CNF :=
  baseFormula Q C ++ outputBlockers G ++ containerExclusions U

/-- Reordering the dynamic clauses preserves every assignment, not just SAT. -/
theorem baseQuery_eval_iff {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) (a : Assignment) :
    CNF.eval a (baseQuery Q C G U) = true ↔
      CNF.eval a (formula Q C G U) = true := by
  simp only [baseQuery,baseFormula,outputBlockers,containerExclusions,formula,
    eval_append,List.map_nil,Finset.mem_univ,ite_true]
  have he : each r (fun _ : Fin r => ([] : CNF)) = [] := by simp [each]
  rw [he]
  simp only [CNF.eval,List.all_nil]
  tauto

theorem baseQuery_satisfiable_iff {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) :
    (baseQuery Q C G U).Satisfiable ↔
      PositiveCompletion.Available (IsRAF Q C) G.toFinset U := by
  rw [← formula_satisfiable_iff Q C G U]
  exact exists_congr (fun a => baseQuery_eval_iff Q C G U a)

theorem outputBlockers_append {r : Nat} (G : List (Finset (Fin r)))
    (I : Finset (Fin r)) :
    outputBlockers (G ++ [I]) = outputBlockers G ++
      [negative (members (fun j => j ∈ I) selectVar)] := by
  simp [outputBlockers]

/-- Only projected reaction sets are queried. The SAT procedure need not expose
or enumerate its auxiliary satisfying assignments. This is finite semantics;
the actual SAT invocation and enumeration machine costs remain separate. -/
noncomputable def baseEnumerate {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (sat : CNF → Bool) (fuel : Nat) : List (Finset (Fin r)) × Nat :=
  PositiveCompletion.enumerate (fun G U => sat (baseQuery Q C G.toList U))
    (List.finRange r) fuel ∅

theorem baseQuery_enumerate_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C]
    (sat : CNF → Bool) (hsat : ∀ f, sat f = true ↔ f.Satisfiable)
    (fuel : Nat) (hfuel : (irrRAFFamily Q C).card < fuel) :
    (baseEnumerate Q C sat fuel).1.Nodup ∧
      (baseEnumerate Q C sat fuel).1.toFinset = irrRAFFamily Q C ∧
      (baseEnumerate Q C sat fuel).2 = (r+1)*(baseEnumerate Q C sat fuel).1.length+1 := by
  let oracle : Finset (Finset (Fin r)) → Finset (Fin r) → Bool :=
    fun G U => sat (baseQuery Q C G.toList U)
  change (PositiveCompletion.enumerate oracle (List.finRange r) fuel ∅).1.Nodup ∧
    (PositiveCompletion.enumerate oracle (List.finRange r) fuel ∅).1.toFinset =
      irrRAFFamily Q C ∧
    (PositiveCompletion.enumerate oracle (List.finRange r) fuel ∅).2 =
      (r+1)*(PositiveCompletion.enumerate oracle (List.finRange r) fuel ∅).1.length+1
  have ho : ∀ (G : Finset (Finset (Fin r))) U,
      oracle G U = true ↔
        PositiveCompletion.Available (IsRAF Q C) G U := by
    intro G U
    unfold oracle
    rw [hsat,baseQuery_satisfiable_iff,Finset.toList_toFinset]
  simpa only [List.length_finRange] using PositiveCompletion.enumerate_irrRAFs_correct Q C
    oracle ho (List.finRange r)
    (fun j => List.mem_finRange j) fuel hfuel

end IrrRAFEnumeration.PositiveCompletionCNF
