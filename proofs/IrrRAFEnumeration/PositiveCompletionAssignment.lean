module

public import proofs.IrrRAFEnumeration.PositiveCompletionCNF
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace IrrRAFEnumeration.PositiveCompletionCNF
open Complexity.SAT

abbrev Atom (d r : Nat) := Fin r ⊕ ((Fin (d+1) × Fin d) ⊕ (Fin d × Fin r))
def atomCount (d r : Nat) := r+((d+1)*d+d*r)
def atomCode (d r : Nat) : Atom d r ≃ Fin (atomCount d r) :=
  (Equiv.sumCongr (Equiv.refl (Fin r))
    ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv

def assignment {d r : Nat} (v : Atom d r → Bool) : Assignment :=
  List.ofFn (fun i => v ((atomCode d r).symm i))

theorem assignment_lookup {d r : Nat} (v : Atom d r → Bool) (z : Atom d r) :
    (assignment v).get ((atomCode d r z).val) = v z := by
  simp [assignment,Assignment.get]

theorem assignment_select {d r : Nat} (v : Atom d r → Bool) (j : Fin r) :
    (assignment v).get (selectVar j) = v (.inl j) := by
  have h := assignment_lookup v (.inl j)
  change (assignment v).get j.val = v (.inl j) at h
  simpa [selectVar] using h

theorem assignment_row {d r : Nat} (v : Atom d r → Bool)
    (i : Fin (d+1)) (x : Fin d) :
    (assignment v).get (rowVar r i x) = v (.inr (.inl (i,x))) := by
  have h := assignment_lookup v (.inr (.inl (i,x)))
  change (assignment v).get (r+(x.val+d*i.val)) = _ at h
  simpa [rowVar,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm] using h

theorem assignment_fire {d r : Nat} (v : Atom d r → Bool) (i : Fin d) (j : Fin r) :
    (assignment v).get (fireVar d i j) = v (.inr (.inr (i,j))) := by
  have h := assignment_lookup v (.inr (.inr (i,j)))
  change (assignment v).get (r+((d+1)*d+(j.val+r*i.val))) = _ at h
  simpa [fireVar,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm] using h

end IrrRAFEnumeration.PositiveCompletionCNF
