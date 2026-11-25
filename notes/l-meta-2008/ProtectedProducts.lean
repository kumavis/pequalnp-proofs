import MixedSources

namespace GateElim.Products
open Reverse Cuts Rows Block Finset Classical Plane
variable {N : ℕ} {K : Type*} [Fintype K] [DecidableEq K]

def protects (S : Finset (Fin N)) (t : ℕ) (f : Fn (Fin N)) :=
  ∀ U : Finset (Fin N), Disjoint U S → U.card≤t → f (onSet U)=false

noncomputable def labels (S : Fin N→Finset (Fin N)) (t : ℕ) (a b : Fn (Fin N)) :=
  sumRow ((foot a).filter fun j => protects (S j) t b)

@[simp] theorem label_mem (S : Fin N→Finset (Fin N)) (t : ℕ) (a b : Fn (Fin N)) (j : Fin N) :
    j∈foot (labels S t a b) ↔ j∈foot a ∧ protects (S j) t b := by
  simp [labels,foot,sumRow,onSet]

private theorem safe_single (S : Finset (Fin N)) {t : ℕ} (ht : 1≤t) (f : Fn (Fin N))
    (good : protects S t f) (l : Fin N) (on : l∈foot f) : l∈S := by
  by_contra no
  have off := good {l} (by simpa using no) (by simpa using ht)
  exact Bool.noConfusion (((mem_filter.mp on).2).symm.trans off)

noncomputable def protectedRows (I : Fin N→Fin N→Prop) [DecidableRel I] (t : ℕ)
    (a b : K→Fn (Fin N)) := edges
      (fun i => labels (rowSet true I) t (a i) (b i))
      (fun i => labels (rowSet false I) t (b i) (a i))

/-- Protection is tested only at the endpoints of the particular edge.
Other singleton pairs of this very same product may already be spurious. -/
theorem local_protection (q t : ℕ) (ht : 1≤t) (tq : t≤q) (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (a b : K→Fn (Fin N))
    (gs hs : List (Node (Fin N))) (ga : Built (base univ) gs) (gb : Built (base univ) hs)
    (ha : ∀ i,a i∈pool (base univ) gs) (hb : ∀ i,b i∈pool (base univ) hs) :
    (t+1)*(∑ p,(protectedRows I t a b p).card)≤(q+1)*(gs.length+hs.length+2*Fintype.card K+2*N) := by
  classical
  let A (i : K) := labels (rowSet true I) t (a i) (b i)
  let B (i : K) := labels (rowSet false I) t (b i) (a i)
  have point (j : Fin N) (i : K) (own : i∈owned A j) : protects (rowSet true I j) t (b i) := by
    have h : j∈foot (A i) := by rw [(mem_filter.mp own).2]; simp
    exact (label_mem ..).mp h |>.2
  have line (j : Fin N) (i : K) (own : i∈owned B j) : protects (rowSet false I j) t (a i) := by
    have h : j∈foot (B i) := by rw [(mem_filter.mp own).2]; simp
    exact (label_mem ..).mp h |>.2
  obtain ⟨dg,lin⟩ := row_geometry I ord hd hj true
  obtain ⟨df,dual⟩ := row_geometry I ord hd hj false
  have rows := owned_scaled hs.length q t tq (rowSet true I) A b hs le_rfl gb hb lin dg (by
    intro p l h; obtain ⟨i,own,hl⟩ := mem_biUnion.mp h
    exact safe_single _ ht _ (point p i own) l hl) point
  have cols := owned_scaled gs.length q t tq (rowSet false I) B a gs le_rfl ga ha dual df (by
    intro l p h; obtain ⟨i,own,hp⟩ := mem_biUnion.mp h
    exact safe_single _ ht _ (line l i own) p hp) line
  let col (p : Fin N) := univ.filter fun l => p∈covered B a l
  have split (p : Fin N) : protectedRows I t a b p⊆covered A b p∪col p := by
    intro l hl; obtain ⟨i,hp,hl⟩ := (mem_filter.mp hl).2
    have bic (p) (pos : p∈foot (A i)) (l) (yes : l∈foot (B i)) : I p l := by
      have mem := safe_single _ ht _ ((label_mem ..).mp pos).2 l ((label_mem ..).mp yes).1
      simpa [rowSet] using mem
    rcases GateElim.Products.star I hj (foot (A i)) (foot (B i)) bic with one|one
    · have eq : foot (A i)={p} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hp,fun t ht => card_le_one.mp one t ht p hp⟩
      exact mem_union_left _ (mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,eq⟩,((label_mem ..).mp hl).1⟩)
    · have eq : foot (B i)={l} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hl,fun t ht => card_le_one.mp one t ht l hl⟩
      exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,mem_biUnion.mpr
        ⟨i,mem_filter.mpr ⟨mem_univ _,eq⟩,((label_mem ..).mp hp).1⟩⟩)
  have cap := sum_le_sum (s:=univ) (fun p _ => (card_le_card (split p)).trans (card_union_le ..))
  have swap : ∑ p,(col p).card=∑ l,(covered B a l).card := by simp only [col,card_filter]; rw [sum_comm]; simp
  simp only [sum_add_distrib,swap] at cap
  simp only [Fintype.card_fin] at rows cols
  have scaled := Nat.mul_le_mul_left (t+1) cap
  nlinarith only [scaled,rows,cols]

end GateElim.Products
#print axioms GateElim.Products.local_protection
