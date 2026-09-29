module

public import proofs.UnconstrainedPACDetection.DirectedLinkageSource
public import proofs.UnconstrainedPACDetection.LinkagePACForward
public import proofs.UnconstrainedPACDetection.Reindexing
public import proofs.UnconstrainedPACDetection.BinarySourceData
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.GetD
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace UnconstrainedPACDetection.GraphSourceTable

def table {m n : ℕ} (f : Fin n → Fin m → ℕ) : List ℕ :=
  List.ofFn fun i : Fin (n*m) =>
    f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

theorem table_length {m n : ℕ} (f : Fin n → Fin m → ℕ) :
    (table f).length = n*m := by simp [table]

theorem table_get {m n : ℕ} (f : Fin n → Fin m → ℕ) (r : Fin n) (x : Fin m) :
    (table f).getD (r.val*m+x.val) 0 = f r x := by
  have hi : r.val*m+x.val = (finProdFinEquiv (r,x)).val := by
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  have hg (i : Fin (n*m)) : (table f).getD i.val 0 =
      f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 := by
    simp only [table,List.getD,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]
  rw [hi]
  simpa only [Equiv.symm_apply_apply] using hg (finProdFinEquiv (r,x))

@[reducible] def dense {m n : ℕ} (s : ReversibleSource (Fin m) (Fin n)) : BinarySourceData.DenseSource :=
  ⟨m,n,table s.left ++ table s.right⟩

theorem wellFormed {m n : ℕ} (s : ReversibleSource (Fin m) (Fin n)) :
    (dense s).WellFormed := by
  simp [BinarySourceData.DenseSource.WellFormed,table_length,Nat.mul_comm,two_mul]

theorem toSource_dense {m n : ℕ} (s : ReversibleSource (Fin m) (Fin n)) :
    (dense s).toSource = s := by
  have bound (r : Fin n) (x : Fin m) : r.val*m+x.val < n*m := by
    calc
      r.val*m+x.val < r.val*m+m := Nat.add_lt_add_left x.isLt _
      _ = (r.val+1)*m := by ring
      _ ≤ n*m := Nat.mul_le_mul_right m r.isLt
  cases s with
  | mk l rr =>
    change ReversibleSource.mk _ _ = ReversibleSource.mk l rr
    congr 1
    · funext r x
      change (table l ++ table rr).getD (r.val*m+x.val) 0 = l r x
      rw [List.getD_append _ _ _ _ (by rw [table_length]; exact bound r x),table_get]
    · funext r x
      change (table l ++ table rr).getD (m*n+r.val*m+x.val) 0 = rr r x
      rw [List.getD_append_right _ _ _ _ (by rw [table_length]; nlinarith),table_length]
      have he : m*n+r.val*m+x.val-n*m = r.val*m+x.val := by
        rw [Nat.mul_comm m n]; omega
      rw [he,table_get]

theorem decode_encode {m n : ℕ} (s : ReversibleSource (Fin m) (Fin n)) :
    BinarySourceData.decode (dense s).encode = some (dense s) :=
  BinarySourceData.decode_encode _ (wellFormed s)

def graphTable {v e r : ℕ} (D : DirectedLinkageSource.Network (Fin v) (Fin e))
    (rows : Fin r → Bool ⊕ Fin v) : BinarySourceData.DenseSource :=
  dense ⟨fun i j => (DirectedLinkageSource.source D).left (rows i) j,
    fun i j => (DirectedLinkageSource.source D).right (rows i) j⟩

theorem graphTable_source {v e r : ℕ} (D : DirectedLinkageSource.Network (Fin v) (Fin e))
    (rows : Fin r → Bool ⊕ Fin v) :
    (graphTable D rows).toSource =
      ⟨fun i j => (DirectedLinkageSource.source D).left (rows i) j,
       fun i j => (DirectedLinkageSource.source D).right (rows i) j⟩ :=
  toSource_dense _

def rowEquiv (v : ℕ) : Fin (2+v) ≃ Bool ⊕ Fin v :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr finTwoEquiv (Equiv.refl _))

def encodeNetwork {v e : ℕ} (D : DirectedLinkageSource.Network (Fin v) (Fin e)) :
    BinarySourceData.DenseSource := graphTable D (rowEquiv v)

theorem encodeNetwork_source {v e : ℕ} (D : DirectedLinkageSource.Network (Fin v) (Fin e)) :
    (encodeNetwork D).toSource =
      ⟨fun i j => (DirectedLinkageSource.source D).left (rowEquiv v i) j,
       fun i j => (DirectedLinkageSource.source D).right (rowEquiv v i) j⟩ :=
  graphTable_source D _

theorem encodeNetwork_wellFormed {v e : ℕ} (D : DirectedLinkageSource.Network (Fin v) (Fin e)) :
    (encodeNetwork D).WellFormed := wellFormed _

theorem encodeNetwork_decode {v e : ℕ} (D : DirectedLinkageSource.Network (Fin v) (Fin e)) :
    BinarySourceData.decode (encodeNetwork D).encode = some (encodeNetwork D) :=
  BinarySourceData.decode_encode _ (encodeNetwork_wellFormed D)

theorem table_bound {m n B : ℕ} (f : Fin n → Fin m → ℕ)
    (h : ∀ r x, f r x ≤ B) : ∀ z ∈ table f, z ≤ B := by
  intro z hz
  simp only [table,List.mem_ofFn] at hz
  obtain ⟨i,rfl⟩ := hz
  exact h _ _

theorem encodeNetwork_coefficients {v e : ℕ}
    (D : DirectedLinkageSource.Network (Fin v) (Fin e)) :
    ∀ z ∈ (encodeNetwork D).values, z ≤ 4 := by
  have hl (r : Fin (2+v)) (x : Fin e) :
      (DirectedLinkageSource.source D).left (rowEquiv v r) x ≤ 4 := by
    have h := (abs_le.mp (DirectedLinkageSource.matrix_abs_le_four D (rowEquiv v r) x)).1
    change Int.toNat (-DirectedLinkageSource.matrix D (rowEquiv v r) x) ≤ 4
    omega
  have hr (r : Fin (2+v)) (x : Fin e) :
      (DirectedLinkageSource.source D).right (rowEquiv v r) x ≤ 4 := by
    have h := (abs_le.mp (DirectedLinkageSource.matrix_abs_le_four D (rowEquiv v r) x)).2
    change Int.toNat (DirectedLinkageSource.matrix D (rowEquiv v r) x) ≤ 4
    omega
  intro z hz
  change z ∈ table _ ++ table _ at hz
  exact (List.mem_append.mp hz).elim (table_bound _ hl z) (table_bound _ hr z)

theorem encoded_values_bound (ns : List ℕ) (h : ∀ z ∈ ns, z ≤ 4) :
    (BinaryFields.encode (ns.map Nat.bits)).length ≤ 7*ns.length := by
  induction ns with
  | nil => simp [BinaryFields.encode]
  | cons z ns ih =>
    have hz := h z (by simp)
    have hb : z.bits.length ≤ 3 := by interval_cases z <;> decide
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.map_cons,BinaryFields.encode,List.flatMap_cons,List.length_append,
      BinaryFields.encodeField_length,List.length_cons] at ht ⊢
    omega

theorem encodeNetwork_wire_bound {v e : ℕ}
    (D : DirectedLinkageSource.Network (Fin v) (Fin e)) :
    (encodeNetwork D).encode.length ≤ 14*e*(v+2)+2*e+2*v+6 := by
  have ht := encoded_values_bound (encodeNetwork D).values (encodeNetwork_coefficients D)
  have hlen : (encodeNetwork D).values.length = 2*(e*(2+v)) := encodeNetwork_wellFormed D
  have hb (n : ℕ) : n.bits.length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have he := hb e
  have hv := hb (2+v)
  change (BinaryFields.encode (e.bits :: (2+v).bits :: (encodeNetwork D).values.map Nat.bits)).length ≤ _
  simp only [BinaryFields.encode,List.flatMap_cons,List.length_append,
    BinaryFields.encodeField_length] at ht ⊢
  rw [hlen] at ht
  nlinarith

theorem encodeNetwork_pac_iff_linkage {v e : ℕ}
    (D : DirectedLinkageSource.Network (Fin v) (Fin e)) :
    (∃ candidate, (encodeNetwork D).toSource.PAC candidate) ↔
      ∃ (P : DirectedLinkageSource.ArcPath D false false)
        (Q : DirectedLinkageSource.ArcPath D true true), Disjoint P.vertices Q.vertices := by
  have hs : (encodeNetwork D).toSource =
      (DirectedLinkageSource.source D).reindex (Equiv.refl _) (rowEquiv v) :=
    encodeNetwork_source D
  rw [hs]
  have back : ((DirectedLinkageSource.source D).reindex (Equiv.refl _) (rowEquiv v)).reindex
      (Equiv.refl _) (rowEquiv v).symm = DirectedLinkageSource.source D := by
    simp only [ReversibleSource.reindex,Equiv.refl_apply,Equiv.apply_symm_apply]
  have hiff :
      (∃ candidate, ((DirectedLinkageSource.source D).reindex (Equiv.refl _) (rowEquiv v)).PAC candidate) ↔
      ∃ candidate, (DirectedLinkageSource.source D).PAC candidate := by
    constructor
    · exact exists_pac_of_reindex _ _ _
    · intro h
      apply exists_pac_of_reindex _ (Equiv.refl _) (rowEquiv v).symm
      rw [back]
      exact h
  exact hiff.trans (DirectedLinkageSource.pac_iff_linkage D)

end UnconstrainedPACDetection.GraphSourceTable
