import PlaneOrdered

namespace GateElim.Plane
open Desk2008 Desk2008.Fanout Finset Classical
attribute [-simp] Fin.natAdd_eq_addNat
variable {q N : ℕ}

def allowedLines (N q : ℕ) : Finset (Finset (Fin N)) := univ.powerset.filter (fun S => S.card≤q)
@[simp] theorem mem_allowed (S : Finset (Fin N)) : S∈allowedLines N q ↔ S.card≤q := by
  simp [allowedLines]

def unionPoints (I : Fin N→Fin N→Prop) [DecidableRel I] (S : Finset (Fin N)) :=
  univ.filter (fun p => ∃ l∈S, I p l)

/-- The unique clause falsified by the maximal legal negative for this line set. -/
noncomputable def forcedClause (I : Fin N→Fin N→Prop) [DecidableRel I] (S : Finset (Fin N)) :=
  box (unionPoints I S) (univ\S)

noncomputable def maximumNegative (I : Fin N→Fin N→Prop) [DecidableRel I] (S : Finset (Fin N)) :=
  box (univ\unionPoints I S) S

theorem complement_clause (I : Fin N→Fin N→Prop) [DecidableRel I] (S : Finset (Fin N)) :
    univ\maximumNegative I S=forcedClause I S := by
  ext i; cases i using Fin.addCases <;> simp [forcedClause,maximumNegative]

theorem private_point (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (S : Finset (Fin N)) (small : S.card≤q) (l : Fin N) (no : l∉S) :
    ∃ p,I p l ∧ p∉unionPoints I S := by
  obtain ⟨deg,linear⟩ := row_geometry I ord hd hj false
  let row := rowSet false I
  let covered := S.biUnion (fun t => row l ∩ row t)
  have cost : covered.card≤S.card := calc
    covered.card ≤ ∑ t∈S,(row l ∩ row t).card := card_biUnion_le
    _ ≤ ∑ _t∈S,1 := sum_le_sum (fun t ht => linear l t (fun e => no (e ▸ ht)))
    _ = S.card := by simp
  have strict : covered.card<(row l).card := by rw [deg]; omega
  obtain ⟨p,hp,miss⟩ := exists_mem_notMem_of_card_lt_card strict
  refine ⟨p,by simpa [row,rowSet] using hp,?_⟩
  intro h; obtain ⟨t,ht,pr⟩ := (mem_filter.mp h).2
  exact miss (mem_biUnion.mpr ⟨t,ht,mem_inter.mpr ⟨hp,by simpa [row,rowSet] using pr⟩⟩)

def coversEdges (I : Fin N→Fin N→Prop) (D : Finset (Vertex N)) :=
  ∀ p l,I p l → left p∈D ∨ right l∈D

/-- On a maximal negative, an edge-covering disjunction is false only if its
support is *exactly* the displayed forced clause. -/
theorem clause_unique (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (S : Finset (Fin N)) (small : S.card≤q)
    (D : Finset (Vertex N)) (hits : coversEdges I D) (off : Disjoint D (maximumNegative I S)) :
    D=forcedClause I S := by
  apply Subset.antisymm
  · intro i hi; rw [←complement_clause]; exact mem_sdiff.mpr ⟨mem_univ _,fun hx => disjoint_left.mp off hi hx⟩
  · intro i hi; cases i using Fin.addCases with
    | left p =>
      obtain ⟨l,hl,inc⟩ := (mem_filter.mp ((in_left ..).mp hi)).2
      exact (hits p l inc).resolve_right (fun h => disjoint_left.mp off h ((in_right ..).mpr hl))
    | right l =>
      have absent := (mem_sdiff.mp ((in_right ..).mp hi)).2
      obtain ⟨p,inc,no⟩ := private_point I ord hd hj S small l absent
      exact (hits p l inc).resolve_left (fun h => disjoint_left.mp off h ((in_left ..).mpr (mem_sdiff.mpr ⟨mem_univ _,no⟩)))

theorem max_negative_valid (I : Fin N→Fin N→Prop) [DecidableRel I] (S : Finset (Fin N)) :
    ¬EdgeIn (adj I) (maximumNegative I S) := by
  rintro h; obtain ⟨p,hp,l,hl,inc⟩ := (edge_iff I _).mp h
  have no := (mem_sdiff.mp ((in_left ..).mp hp)).2
  exact no (mem_filter.mpr ⟨mem_univ _,l,(in_right ..).mp hl,inc⟩)

theorem clause_inj (I : Fin N→Fin N→Prop) [DecidableRel I] :
    Function.Injective (forcedClause I) := by
  intro A B eq; ext l
  have h := congrArg (fun D : Finset (Vertex N) => right l∈D) eq
  have n : l∉A ↔ l∉B := by simpa [forcedClause] using Eq.to_iff h
  tauto

def CNF (F : Finset (Finset (Vertex N))) (X : Finset (Vertex N)) : Prop :=
  ∀ C∈F, ¬Disjoint C X

noncomputable def clauses (I : Fin N→Fin N→Prop) [DecidableRel I] (q : ℕ) :=
  (allowedLines N q).image (forcedClause I)

theorem clause_count (N q : ℕ) : (allowedLines N q).card=∑ i∈range (q+1), N.choose i := by
  let F (i : ℕ) := (univ : Finset (Fin N)).powersetCard i
  have split : allowedLines N q=(range (q+1)).biUnion F := by
    ext S; simp [F,Nat.lt_succ_iff]
  rw [split,card_biUnion]; simp [F]
  intro i _ j _ ne; apply disjoint_left.mpr
  intro S hi hj; exact ne ((mem_powersetCard.mp hi).2.symm.trans (mem_powersetCard.mp hj).2)

theorem all_clauses_necessary (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (F : Finset (Finset (Vertex N)))
    (pos : ∀ p l,I p l → CNF F {left p,right l})
    (neg : ∀ X,(lns X).card≤q → ¬EdgeIn (adj I) X → ¬CNF F X) :
    clauses I q ⊆ F := by
  classical
  rintro D mem
  obtain ⟨S,hs,rfl⟩ := mem_image.mp mem
  have small := (mem_allowed S).mp hs
  have fails := neg (maximumNegative I S) (by simpa [maximumNegative] using small) (max_negative_valid I S)
  obtain ⟨D,hd',off⟩ : ∃ D∈F,Disjoint D (maximumNegative I S) := by simpa [CNF] using fails
  have hits : coversEdges I D := by
    intro p l inc
    have h := pos p l inc D hd'
    simp [Finset.disjoint_insert_right,Finset.disjoint_singleton_right] at h
    tauto
  exact clause_unique I ord hd hj S small D hits off ▸ hd'

theorem canonical_cnf (I : Fin N→Fin N→Prop) [DecidableRel I] (q : ℕ) (X : Finset (Vertex N)) :
    CNF (clauses I q) X ↔ EdgeIn (adj I) X ∨ q<(lns X).card := by
  classical
  constructor
  · intro h; by_contra! no
    let S := lns X
    have member : forcedClause I S∈clauses I q := mem_image.mpr ⟨S,(mem_allowed S).mpr (by dsimp [S]; omega),rfl⟩
    have bad := h _ member
    apply bad; apply disjoint_left.mpr
    intro i hi on
    cases i using Fin.addCases with
    | left p =>
      obtain ⟨l,hl,inc⟩ := (mem_filter.mp ((in_left ..).mp hi)).2
      exact no.1 ((edge_iff I _).mpr ⟨p,on,l,(in_lns ..).mp hl,inc⟩)
    | right l => exact (mem_sdiff.mp ((in_right ..).mp hi)).2 ((in_lns ..).mpr on)
  · intro yes D hd
    obtain ⟨S,hs,rfl⟩ := mem_image.mp hd
    rw [Finset.not_disjoint_iff]
    rcases yes with e|large
    · obtain ⟨p,hp,l,hl,inc⟩ := (edge_iff I _).mp e
      by_cases h : l∈S
      · exact ⟨left p,(in_left ..).mpr (mem_filter.mpr ⟨mem_univ _,l,h,inc⟩),hp⟩
      · exact ⟨right l,(in_right ..).mpr (mem_sdiff.mpr ⟨mem_univ _,h⟩),hl⟩
    · have small := (mem_allowed S).mp hs
      obtain ⟨l,hl,no⟩ := exists_mem_notMem_of_card_lt_card (show S.card<(lns X).card by omega)
      exact ⟨right l,(in_right ..).mpr (mem_sdiff.mpr ⟨mem_univ _,no⟩),(in_lns ..).mp hl⟩

end GateElim.Plane
#print axioms GateElim.Plane.all_clauses_necessary
#print axioms GateElim.Plane.canonical_cnf
