module

public import Mathlib

@[expose] public section

namespace RAF

structure CRS (M R : Type*) [DecidableEq M] where
  inputs : R → Finset M
  outputs : R → Finset M
  food : Finset M

def Catalysis (M R : Type*) := M → R → Prop

end RAF
