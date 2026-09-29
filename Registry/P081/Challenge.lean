module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# NP-completeness of unconstrained productive autocatalytic core detection
Binary input encodes finite reversible sources with nonnegative integer
complexes. The input specifies neither a target species nor an allowed food
set. A core is a minimal nonempty productive motif with signed reversible flux.
The complete computational model and polynomial many-one reduction definition
are included below, preserving the original Complexitylib declaration names.
Complexitylib definitions: copyright 2025 Samuel Schlesinger, Apache-2.0.
-/

namespace Complexity
inductive Γ where
  | zero | one | blank | start
  deriving Repr, DecidableEq

instance : Fintype Γ where
  elems := {.zero, .one, .blank, .start}
  complete := fun x => by cases x <;> simp

instance : Inhabited Γ := ⟨Γ.blank⟩

/-- The writable alphabet Γw = {0, 1, □}. The start symbol `▷` cannot be written by a
    transition function — this is enforced structurally by using `Γw` in the output of `δ`. -/
inductive Γw where
  | zero | one | blank
  deriving Repr, DecidableEq

instance : Fintype Γw where
  elems := {.zero, .one, .blank}
  complete := fun x => by cases x <;> simp

/-- Embed a writable symbol into the full alphabet. -/
@[simp] def Γw.toΓ : Γw → Γ
  | .zero => .zero
  | .one => .one
  | .blank => .blank

instance : Coe Γw Γ where coe := Γw.toΓ

def Γ.ofBool : Bool → Γ
  | false => .zero
  | true => .one

inductive Dir3 where
  | left | right | stay
  deriving Repr, DecidableEq

instance : Fintype Dir3 where
  elems := {.left, .right, .stay}
  complete := fun x => by cases x <;> simp

structure Tape where
  /-- The head position; cell 0 is the leftmost cell. -/
  head : ℕ
  /-- The tape contents, one symbol per cell. -/
  cells : ℕ → Γ

namespace Tape
def read (t : Tape) : Γ := t.cells t.head

def write (t : Tape) (s : Γ) : Tape :=
  if t.head = 0 then t
  else { t with cells := Function.update t.cells t.head s }

def move (t : Tape) (d : Dir3) : Tape :=
  match d with
  | .left => { t with head := t.head - 1 }
  | .right => { t with head := t.head + 1 }
  | .stay => t

def HasOutput (t : Tape) (y : List Bool) : Prop :=
  (∀ (i : ℕ) (h : i < y.length),
    t.cells (i + 1) = Γ.ofBool (y[i]'h)) ∧
  t.cells (y.length + 1) = Γ.blank

abbrev writeAndMove (t : Tape) (s : Γ) (d : Dir3) : Tape :=
  (t.write s).move d

end Tape
def Tape.init (contents : List Γ) : Tape where
  head := 0
  cells := fun i =>
    if i = 0 then Γ.start
    else (contents[i - 1]?).getD Γ.blank

abbrev Language := Set (List Bool)

structure Cfg (n : ℕ) (Q : Type) where
  /-- The current machine state. -/
  state : Q
  /-- The read-only input tape. -/
  input : Tape
  /-- The `n` read-write work tapes. -/
  work : Fin n → Tape
  /-- The read-write output tape. -/
  output : Tape

namespace Cfg
abbrev init (qstart : Q) (x : List Bool) : Cfg n Q :=
  { state := qstart
    input := Tape.init (x.map Γ.ofBool)
    work := fun _ => Tape.init []
    output := Tape.init [] }

abbrev isHalted (qhalt : Q) (c : Cfg n Q) : Prop :=
  c.state = qhalt

end Cfg
structure TM (n : ℕ) where
  /-- The (finite) type of machine states. -/
  Q : Type
  [decEq : DecidableEq Q]
  [finQ : Fintype Q]
  /-- The designated start state. -/
  qstart : Q
  /-- The designated halt state. -/
  qhalt : Q
  /-- The transition function: from the current state and the symbols under
      the input, work, and output heads, produce the next state, the symbols
      to write on the work and output tapes, and a direction for every head. -/
  δ : Q → Γ → (Fin n → Γ) → Γ →
      Q × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3
  /-- Reading the left-end marker forces that head to move right, so no head
      ever falls off the left edge. -/
  δ_right_of_start : ∀ (q : Q) (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ),
    let (_, _, _, inDir, workDirs, outDir) := δ q iHead wHeads oHead
    (iHead = Γ.start → inDir = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → workDirs i = Dir3.right) ∧
    (oHead = Γ.start → outDir = Dir3.right)

attribute [instance] TM.decEq TM.finQ

structure NTM (n : ℕ) where
  /-- The (finite) type of machine states. -/
  Q : Type
  [decEq : DecidableEq Q]
  [finQ : Fintype Q]
  /-- The designated start state. -/
  qstart : Q
  /-- The designated halt state. -/
  qhalt : Q
  /-- The two transition functions, selected by the `Bool` choice bit; each
      has the same shape as the deterministic `TM.δ`. -/
  δ : Bool → Q → Γ → (Fin n → Γ) → Γ →
      Q × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3
  /-- Reading the left-end marker forces that head to move right, on both
      branches. -/
  δ_right_of_start : ∀ (b : Bool) (q : Q) (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ),
    let (_, _, _, inDir, workDirs, outDir) := δ b q iHead wHeads oHead
    (iHead = Γ.start → inDir = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → workDirs i = Dir3.right) ∧
    (oHead = Γ.start → outDir = Dir3.right)

attribute [instance] NTM.decEq NTM.finQ

namespace TM
variable {n : ℕ}
def step (tm : TM n) (c : Cfg n tm.Q) : Option (Cfg n tm.Q) :=
  if c.state = tm.qhalt then none
  else
    let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
      tm.δ c.state c.input.read (fun i => (c.work i).read) c.output.read
    some
      { state := q'
        input := c.input.move inDir
        work := fun i => (c.work i).writeAndMove (workWrites i) (workDirs i)
        output := c.output.writeAndMove outWrite outDir }

abbrev initCfg (tm : TM n) (x : List Bool) : Cfg n tm.Q :=
  Cfg.init tm.qstart x

abbrev halted (tm : TM n) (c : Cfg n tm.Q) : Prop :=
  Cfg.isHalted tm.qhalt c

inductive reachesIn (tm : TM n) : ℕ → Cfg n tm.Q → Cfg n tm.Q → Prop where
  | zero : reachesIn tm 0 c c
  | step : tm.step c = some c'' → reachesIn tm t c'' c' → reachesIn tm (t + 1) c c'

def ComputesInTime (tm : TM n) (f : List Bool → List Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x, ∃ c' t, t ≤ T x.length ∧ tm.reachesIn t (tm.initCfg x) c' ∧ tm.halted c' ∧
    c'.output.HasOutput (f x)

end TM
namespace NTM
variable {n : ℕ}
def trace (tm : NTM n) :
    (T : ℕ) → (Fin T → Bool) → Cfg n tm.Q → Cfg n tm.Q
  | 0, _, c => c
  | T + 1, choices, c =>
    if c.state = tm.qhalt then c
    else
      let b := choices ⟨0, Nat.zero_lt_succ T⟩
      let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
        tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read
      let c' : Cfg n tm.Q :=
        { state := q'
          input := c.input.move inDir
          work := fun i => (c.work i).writeAndMove (workWrites i) (workDirs i)
          output := c.output.writeAndMove outWrite outDir }
      tm.trace T (fun i => choices ⟨i.val + 1, by omega⟩) c'

abbrev initCfg (tm : NTM n) (x : List Bool) : Cfg n tm.Q :=
  Cfg.init tm.qstart x

abbrev halted (tm : NTM n) (c : Cfg n tm.Q) : Prop :=
  Cfg.isHalted tm.qhalt c

def AcceptsInTime (tm : NTM n) (x : List Bool) (T : ℕ) : Prop :=
  ∃ choices : Fin T → Bool,
    let c' := tm.trace T choices (tm.initCfg x)
    tm.halted c' ∧ c'.output.cells 1 = Γ.one

def AllPathsHaltIn (tm : NTM n) (T : ℕ → ℕ) : Prop :=
  ∀ x (choices : Fin (T x.length) → Bool),
    tm.halted (tm.trace (T x.length) choices (tm.initCfg x))

def DecidesInTime (tm : NTM n) (L : Language) (T : ℕ → ℕ) : Prop :=
  tm.AllPathsHaltIn T ∧
  (∀ x, x ∈ L ↔ tm.AcceptsInTime x (T x.length))

end NTM
open Asymptotics Filter
def BigO (f g : ℕ → ℕ) : Prop :=
  (fun n => (f n : ℝ)) =O[atTop] (fun n => (g n : ℝ))

infix:50 " =O " => BigO
def NTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ),
    tm.DecidesInTime L f ∧ f =O T}

def NP : Set Language :=
  ⋃ k : ℕ, NTIME (· ^ k)

def FP : Set (List Bool → List Bool) :=
  {f | ∃ (d k : ℕ) (tm : TM k) (T : ℕ → ℕ),
    tm.ComputesInTime f T ∧ T =O (· ^ d)}

def MapReducesPoly (L L' : Language) : Prop :=
  ∃ f : List Bool → List Bool, f ∈ FP ∧ ∀ x, x ∈ L ↔ f x ∈ L'

infix:50 " ≤ₚ " => MapReducesPoly
def NPHard (L : Language) : Prop := ∀ L' ∈ NP, L' ≤ₚ L

def NPComplete (L : Language) : Prop := L ∈ NP ∧ NPHard L

end Complexity
namespace UnconstrainedPACDetection
structure ReversibleSource (Entity Reaction : Type*) where
  left : Reaction → Entity → ℕ
  right : Reaction → Entity → ℕ

variable {Entity Reaction : Type*}

variable {Entity Reaction : Type*}
def ReversibleSource.net (source : ReversibleSource Entity Reaction)
    (reaction : Reaction) (entity : Entity) : ℝ :=
  (source.right reaction entity : ℝ) - (source.left reaction entity : ℝ)

def ReversibleSource.sideAdmissible [DecidableEq Entity]
    (source : ReversibleSource Entity Reaction) (entities : Finset Entity)
    (reaction : Reaction) : Prop :=
  (∃ entity ∈ entities, 0 < source.left reaction entity) ∧
    ∃ entity ∈ entities, 0 < source.right reaction entity

variable [Fintype Entity] [DecidableEq Entity] [Fintype Reaction] [DecidableEq Reaction]
abbrev Candidate (Entity Reaction : Type*) := Finset Entity × Finset Reaction

def ReversibleSource.Productive (source : ReversibleSource Entity Reaction)
    (entities : Finset Entity) (reactions : Finset Reaction) : Prop :=
  ∃ flow : Reaction → ℝ,
    (∀ reaction, reaction ∉ reactions → flow reaction = 0) ∧
    ∀ entity ∈ entities,
      0 < Finset.univ.sum (fun reaction =>
        source.net reaction entity * flow reaction)

def ReversibleSource.Motif (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) : Prop :=
  candidate.1.Nonempty ∧
    candidate.2.Nonempty ∧
    (∀ reaction ∈ candidate.2,
      source.sideAdmissible candidate.1 reaction) ∧
    source.Productive candidate.1 candidate.2

def ReversibleSource.PAC (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) : Prop :=
  source.Motif candidate ∧
    ∀ ⦃smaller⦄, smaller < candidate → ¬ source.Motif smaller

namespace BinaryFields
def encodeField : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: encodeField bs

def encode (fields : List (List Bool)) : List Bool := fields.flatMap encodeField

def decode : List Bool → Option (List (List Bool))
  | [] => some []
  | false :: rest => (List.cons []) <$> decode rest
  | [true] => none
  | true :: b :: rest => do
      let fields ← decode rest
      match fields with
      | [] => none
      | field :: fields => some ((b :: field) :: fields)

def readNat : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (readNat bs)

end BinaryFields
namespace BinarySourceData
structure DenseSource where
  entities : ℕ
  reactions : ℕ
  values : List ℕ
  deriving DecidableEq

def DenseSource.toSource (s : DenseSource) : ReversibleSource (Fin s.entities) (Fin s.reactions) where
  left r x := s.values.getD (r.val * s.entities + x.val) 0
  right r x := s.values.getD (s.entities * s.reactions + r.val * s.entities + x.val) 0

def DenseSource.encode (s : DenseSource) : List Bool :=
  BinaryFields.encode (s.entities.bits :: s.reactions.bits :: s.values.map Nat.bits)

def decode (bits : List Bool) : Option DenseSource := do
  let fields ← BinaryFields.decode bits
  match fields with
  | m :: n :: values =>
      let s : DenseSource := ⟨BinaryFields.readNat m, BinaryFields.readNat n,
        values.map BinaryFields.readNat⟩
      if s.values.length = 2 * (s.entities * s.reactions) ∧ s.encode = bits then some s else none
  | _ => none

end BinarySourceData
namespace BinaryPACVerifier
def language : Set (List Bool) :=
  {input | ∃ s, BinarySourceData.decode input = some s ∧ ∃ c, s.toSource.PAC c}

end BinaryPACVerifier
open Complexity
theorem complexity_root : NPComplete BinaryPACVerifier.language := by
  sorry
end UnconstrainedPACDetection
