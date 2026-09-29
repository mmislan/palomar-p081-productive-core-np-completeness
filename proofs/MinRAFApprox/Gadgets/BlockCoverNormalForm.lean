module

public import proofs.MinRAFApprox.Basic

@[expose] public section

namespace MinRAFApprox

universe u v w

open Reaction

variable {U : Type u} {J : Type v} {K : Type w}
  [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- The four exact structural consequences of the literal RAF gadget:
nonemptiness, block-to-backbone provenance, gate coverage, and cyclic
all-or-none block support. -/
def IsBlockCoverRAF (I : SetCoverInstance U J)
    (S : Finset (Reaction U J K)) : Prop :=
  S.Nonempty ∧
  (∀ j k, block j k ∈ S → ∀ u, gate u ∈ S) ∧
  (∀ u, gate u ∈ S → ∃ j k, block j k ∈ S ∧ u ∈ I.sets j) ∧
  (∀ j k, block j k ∈ S → ∀ l, block j l ∈ S)

omit [DecidableEq U] [DecidableEq J] [DecidableEq K] in
@[simp] theorem gate_mem_canonicalRAF (C : Finset J) (u : U) :
    gate (K := K) u ∈ canonicalRAF C := by
  classical
  simp [canonicalRAF]

omit [DecidableEq U] [DecidableEq J] [DecidableEq K] in
@[simp] theorem block_mem_canonicalRAF (C : Finset J) (j : J) (k : K) :
    block (U := U) j k ∈ canonicalRAF C ↔ j ∈ C := by
  classical
  simp [canonicalRAF]

omit [DecidableEq U] [DecidableEq J] [DecidableEq K] in
theorem canonicalRAF_nonempty [Nonempty U] (C : Finset J) :
    (canonicalRAF (U := U) (K := K) C).Nonempty := by
  let u : U := Classical.choice (inferInstance : Nonempty U)
  exact ⟨gate u, gate_mem_canonicalRAF C u⟩

/-- Exact block-cover normal form.  This is the combinatorial target of the
literal closure/catalysis adapter. -/
theorem blockCoverRAF_iff_cover [Nonempty U] [Nonempty K]
    (I : SetCoverInstance U J) (S : Finset (Reaction U J K)) :
    IsBlockCoverRAF I S ↔
      ∃ C : Finset J, I.Covers C ∧ S = canonicalRAF C := by
  constructor
  · rintro ⟨hne, hbackbone, hcover, hall⟩
    let C : Finset J := Finset.univ.filter fun j => ∃ k, block (U := U) j k ∈ S
    have hblock : ∀ j k, block (U := U) j k ∈ S ↔ j ∈ C := by
      intro j k
      constructor
      · intro hjk
        exact Finset.mem_filter.2 ⟨Finset.mem_univ j, ⟨k, hjk⟩⟩
      · intro hj
        obtain ⟨_, ⟨l, hjl⟩⟩ := Finset.mem_filter.1 hj
        exact hall j l hjl k
    have hsomeBlock : ∃ j k, block (U := U) j k ∈ S := by
      obtain ⟨r, hr⟩ := hne
      cases r with
      | block j k => exact ⟨j, k, hr⟩
      | gate u =>
          obtain ⟨j, k, hjk, _⟩ := hcover u hr
          exact ⟨j, k, hjk⟩
    obtain ⟨j0, k0, hj0⟩ := hsomeBlock
    have hgate : ∀ u, gate (K := K) u ∈ S := hbackbone j0 k0 hj0
    refine ⟨C, ?_, ?_⟩
    · intro u
      obtain ⟨j, k, hjk, huj⟩ := hcover u (hgate u)
      exact ⟨j, (hblock j k).1 hjk, huj⟩
    · ext r
      cases r with
      | gate u => simp [hgate u]
      | block j k => simp [hblock j k]
  · rintro ⟨C, hC, rfl⟩
    refine ⟨canonicalRAF_nonempty C, ?_, ?_, ?_⟩
    · intro j k _ u
      exact gate_mem_canonicalRAF C u
    · intro u _
      obtain ⟨j, hjC, huj⟩ := hC u
      let k : K := Classical.choice (inferInstance : Nonempty K)
      exact ⟨j, k, (block_mem_canonicalRAF C j k).2 hjC, huj⟩
    · intro j k hj l
      exact (block_mem_canonicalRAF C j l).2
        ((block_mem_canonicalRAF C j k).1 hj)

end MinRAFApprox
