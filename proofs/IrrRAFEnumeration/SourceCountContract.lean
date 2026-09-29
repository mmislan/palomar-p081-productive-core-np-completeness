module

public import proofs.IrrRAFEnumeration.SATCountTimeout
public import proofs.IrrRAFEnumeration.PointwiseComposition
public import proofs.IrrRAFEnumeration.HeaderComparison

@[expose] public section

namespace IrrRAFEnumeration.SATSource
open Complexity Complexity.TM RAF SATCompletion CircuitSource HeaderComparison

noncomputable def sourceCount {n m : Nat} (Φ : Fin m → Finset (Choice n)) : Nat :=
  (irrRAFFamily (crs (rules Φ)) catalysis).card

/-- A necessary count/output-size consequence of exact enumeration in unary
count and fixed-width reaction-mask format. This condition alone will suffice
for the lower bound; it does not assert correctness of individual masks. -/
def SourceCountBound {k : Nat} (E : TM k) (p : Polynomial Nat) : Prop :=
  ∀ (n m : Nat) (Φ : Fin m → Finset (Choice n)), 2 ≤ n →
    ∃ (body : List Bool) (c : Cfg k E.Q) (t : Nat),
      body.length = sourceCount Φ * reactionCount n m ∧
      t ≤ p.eval ((sourceBits Φ).length + fixedWidthOutputLength (reactionCount n m) (sourceCount Φ)) ∧
      E.reachesIn t (E.initCfg (sourceBits Φ)) c ∧ E.halted c ∧
      c.output.HasOutput (List.replicate (sourceCount Φ) true ++ false :: body)

theorem sourceCount_eq_baseline {n m : Nat} (hn : 2 ≤ n)
    (Φ : Fin m → Finset (Choice n)) :
    sourceCount Φ = n ↔ ¬ ∃ f : Fin n → Bool, Satisfies Φ f :=
  irrRAFFamily_card_eq_iff_cnf_unsat hn Φ

theorem SourceCountBound.start_ne_halt {k : Nat} {E : TM k} {p : Polynomial Nat}
    (hE : SourceCountBound E p) : E.qstart ≠ E.qhalt := by
  intro hzero
  obtain ⟨body,c,t,_,_,hr,_,ho⟩ := hE 2 0 (fun _ => ∅) (by decide)
  have ht := E.reachesIn_le_halt hr TM.reachesIn.zero hzero
  have he : t = 0 := by omega
  subst t
  cases hr
  have hbit := ho.1 0 (by simp)
  exact Γ.ofBool_ne_blank _ hbit.symm

theorem halted_runs_equal {k : Nat} (tm : TM k) {x : List Bool}
    {c d : Cfg k tm.Q} {t u : Nat}
    (hc : tm.reachesIn t (tm.initCfg x) c) (hd : tm.reachesIn u (tm.initCfg x) d)
    (hhc : tm.halted c) (hhd : tm.halted d) : c = d := by
  have htu := tm.reachesIn_le_halt hc hd hhd
  have hut := tm.reachesIn_le_halt hd hc hhc
  have he : t = u := by omega
  subst u
  exact TM.reachesIn_right_unique hc hd

end IrrRAFEnumeration.SATSource
