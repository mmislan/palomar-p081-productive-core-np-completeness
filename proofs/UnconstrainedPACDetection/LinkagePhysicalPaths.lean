module

public import proofs.UnconstrainedPACDetection.LinkageArcPaths
public import proofs.UnconstrainedPACDetection.LinkageColumnKernel

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource

inductive PhysicalVertex (V : Type*) where
  | source : Bool → PhysicalVertex V
  | sink : Bool → PhysicalVertex V
  | internal : V → PhysicalVertex V

def tailVertex {V : Type*} : Bool ⊕ V → PhysicalVertex V
  | Sum.inl b => .source b
  | Sum.inr v => .internal v

def headVertex {V : Type*} : Bool ⊕ V → PhysicalVertex V
  | Sum.inl b => .sink b
  | Sum.inr v => .internal v

theorem tailVertex_injective {V : Type*} : Function.Injective (@tailVertex V) := by
  intro x y h
  cases x <;> cases y <;> simp_all [tailVertex]

theorem tailVertex_ne_sink {V : Type*} (x : Bool ⊕ V) (b : Bool) :
    tailVertex x ≠ PhysicalVertex.sink b := by
  cases x <;> simp [tailVertex]

namespace ArcPath

variable {V E : Type*} {D : Network V E} {s t u v : Bool}

def vertices (P : ArcPath D s t) : Set (PhysicalVertex V) :=
  Set.range (fun i => tailVertex (D.tail (P.arcs i))) ∪ {PhysicalVertex.sink t}

theorem physical_consecutive (P : ArcPath D s t) (i : ℕ) (hi : i + 1 < P.length) :
    headVertex (D.head (P.arcs ⟨i, by omega⟩)) =
      tailVertex (D.tail (P.arcs ⟨i + 1, hi⟩)) := by
  rw [P.consecutive i hi]
  obtain ⟨w, hw⟩ := P.internal ⟨i + 1, hi⟩ (by change 0 < i + 1; omega)
  rw [hw]
  rfl

/-- All pre-final vertices are distinct, and the final physical sink is new. -/
theorem physical_simple (P : ArcPath D s t) :
    Function.Injective (fun i => tailVertex (D.tail (P.arcs i))) ∧
      PhysicalVertex.sink t ∉ Set.range (fun i => tailVertex (D.tail (P.arcs i))) := by
  refine ⟨tailVertex_injective.comp P.tail_injective, ?_⟩
  rintro ⟨i, hi⟩
  exact tailVertex_ne_sink _ _ hi

theorem physical_disjoint (P : ArcPath D s t) (R : ArcPath D u v)
    (htv : t ≠ v) (hdis : ∀ i j, D.tail (P.arcs i) ≠ D.tail (R.arcs j)) :
    Disjoint P.vertices R.vertices := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with ⟨i, rfl⟩ | hx
  · rcases hy with ⟨j, hj⟩ | hy
    · exact hdis i j (tailVertex_injective hj.symm)
    · exact tailVertex_ne_sink _ _ hy
  · have hx' : x = PhysicalVertex.sink t := hx
    subst x
    rcases hy with ⟨j, hj⟩ | hy
    · exact tailVertex_ne_sink _ _ hj
    · have hy' : PhysicalVertex.sink t = PhysicalVertex.sink v := hy
      cases hy'
      exact htv rfl

end ArcPath

/-- A closed, mixed, degree-two selection containing the source row yields
two vertex-disjoint directed simple paths, preserving the original arc type.
The arithmetic lemma downstream must decide which sink pairing occurs. -/
theorem selected_physical_paths {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (D : Network V E) (rs : Finset (Bool ⊕ V))
    (hrow : ∀ r ∈ rs, (Finset.univ.filter (fun e => matrix D r e ≠ 0)).card ≤ 2)
    (hmixed : ∀ r ∈ rs, (∃ e, matrix D r e < 0) ∧ ∃ e, 0 < matrix D r e)
    (hcol : ∀ e, (rs.filter (fun r => matrix D r e ≠ 0)).card = 2)
    (hs : Sum.inl false ∈ rs) :
    ∃ t u : Bool, t ≠ u ∧ ∃ (P : ArcPath D false t) (R : ArcPath D true u),
      Disjoint P.vertices R.vertices := by
  classical
  let Q := endpointEquivs D rs hrow hmixed hcol hs
  have hb : ∀ b : Bool, Sum.inl b ∈ rs := by
    intro b
    cases b
    · exact hs
    · exact (terminal_mem_iff D rs hrow hmixed hcol).mp hs
  obtain ⟨t, u, htu, P, R, hdis⟩ := Q.two_arc_paths hb
  exact ⟨t, u, htu, P, R, P.physical_disjoint R htu hdis⟩

theorem independent_selection_physical_paths
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (D : Network V E) (rs : Finset (Bool ⊕ V)) (hne : rs.Nonempty)
    (hrow : ∀ r ∈ rs, (Finset.univ.filter (fun e => matrix D r e ≠ 0)).card ≤ 2)
    (hmixed : ∀ r ∈ rs, (∃ e, matrix D r e < 0) ∧ ∃ e, 0 < matrix D r e)
    (hcol : ∀ e, (rs.filter (fun r => matrix D r e ≠ 0)).card = 2)
    (hind : LinearIndependent ℝ (fun r : rs => fun e : E => (matrix D r.1 e : ℝ))) :
    ∃ t u : Bool, t ≠ u ∧ ∃ (P : ArcPath D false t) (R : ArcPath D true u),
      Disjoint P.vertices R.vertices :=
  selected_physical_paths D rs hrow hmixed hcol
    (independent_has_source D rs hne hrow hmixed hcol hind)

end UnconstrainedPACDetection.DirectedLinkageSource
