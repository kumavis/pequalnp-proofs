import RectangleRows

namespace GateElim.Products
open Reverse Cuts Rows Block Finset Classical Plane
variable {N q : ℕ} {K : Type*} [Fintype K] [DecidableEq K]

def sound (I : Fin N→Fin N→Prop) (q : ℕ) (a b : Fn (Fin N)) :=
  ∀ X Y : Finset (Fin N), X.card≤q → Y.card≤q → (X.card=1 ∨ Y.card=1) → a (onSet X)=true → b (onSet Y)=true →
    ∃ p∈X,∃ l∈Y,I p l

noncomputable def edges (a b : K→Fn (Fin N)) (p : Fin N) :=
  univ.filter fun l => ∃ i,p∈foot (a i) ∧ l∈foot (b i)

theorem star (I : Fin N→Fin N→Prop) (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l)
    (A B : Finset (Fin N)) (inc : ∀ p∈A,∀ l∈B,I p l) :
    A.card≤1 ∨ B.card≤1 := by
  by_cases h : A.card≤1
  · exact Or.inl h
  · obtain ⟨p,hp,r,hr,ne⟩ := Finset.one_lt_card.mp (by omega : 1<A.card)
    exact Or.inr (card_le_one.mpr (fun l hl t ht => (hj p r ne).unique
      ⟨inc p hp l hl,inc r hr l hl⟩ ⟨inc p hp t ht,inc r hr t ht⟩))

/-- The sound functional rectangles may use arbitrary AND/OR gates and share
all their computations on each side. Bound the actual singleton edges covered. -/
theorem sound_product_scaled (q t : ℕ) (ht : 1≤t) (smallT : t≤q) (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (a b : K→Fn (Fin N)) (good : ∀ i,sound I t (a i) (b i))
    (gs hs : List (Node (Fin N))) (ga : Built (base univ) gs) (gb : Built (base univ) hs)
    (ha : ∀ i,a i∈pool (base univ) gs) (hb : ∀ i,b i∈pool (base univ) hs) :
    (t+1)*(∑ p,(edges a b p).card)≤(q+1)*(gs.length+hs.length+2*Fintype.card K+2*N) := by
  classical
  have pair (i : K) (p : Fin N) (hp : p∈foot (a i)) (l : Fin N) (hl : l∈foot (b i)) : I p l := by
    simpa using good i {p} {l} (by simpa using ht) (by simpa using ht) (by simp) (mem_filter.mp hp).2 (mem_filter.mp hl).2
  have point (j : Fin N) (i : K) (own : i∈owned a j) : j∈foot (a i) := by rw [(mem_filter.mp own).2]; simp
  have line (j : Fin N) (i : K) (own : i∈owned b j) : j∈foot (b i) := by rw [(mem_filter.mp own).2]; simp
  obtain ⟨dg,lin⟩ := row_geometry I ord hd hj true
  obtain ⟨df,dual⟩ := row_geometry I ord hd hj false
  have rows := owned_scaled hs.length q t smallT (rowSet true I) a b hs le_rfl gb hb lin dg (by
    intro p l h; obtain ⟨i,own,hl⟩ := mem_biUnion.mp h
    simpa [rowSet] using pair i p (point p i own) l hl) (by
    intro p i own Y dis small; apply Bool.eq_false_iff.mpr; intro yes
    obtain ⟨u,hu,l,hl,inc⟩ := good i {p} Y (by simpa using ht) small (by simp) (mem_filter.mp (point p i own)).2 yes
    obtain rfl := mem_singleton.mp hu
    exact disjoint_left.mp dis hl (by simpa [rowSet] using inc))
  have cols := owned_scaled gs.length q t smallT (rowSet false I) b a gs le_rfl ga ha dual df (by
    intro l p h; obtain ⟨i,own,hp⟩ := mem_biUnion.mp h
    simpa [rowSet] using pair i p hp l (line l i own)) (by
    intro l i own X dis small; apply Bool.eq_false_iff.mpr; intro yes
    obtain ⟨p,hp,t,ht,inc⟩ := good i X {l} small (by simpa using ht) (by simp) yes (mem_filter.mp (line l i own)).2
    obtain rfl := mem_singleton.mp ht
    exact disjoint_left.mp dis hp (by simpa [rowSet] using inc))
  let col (p : Fin N) := univ.filter fun l => p∈covered b a l
  have split (p : Fin N) : edges a b p⊆covered a b p∪col p := by
    intro l hl; obtain ⟨i,hp,hl⟩ := (mem_filter.mp hl).2
    rcases star I hj (foot (a i)) (foot (b i)) (pair i) with one|one
    · have eq : foot (a i)={p} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hp,fun t ht => card_le_one.mp one t ht p hp⟩
      exact mem_union_left _ (mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,eq⟩,hl⟩)
    · have eq : foot (b i)={l} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hl,fun t ht => card_le_one.mp one t ht l hl⟩
      exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,eq⟩,hp⟩⟩)
  have cap := sum_le_sum (s:=univ) (fun p _ => (card_le_card (split p)).trans (card_union_le ..))
  have swap : ∑ p,(col p).card=∑ l,(covered b a l).card := by simp only [col,card_filter]; rw [sum_comm]; simp
  simp only [sum_add_distrib,swap] at cap
  simp only [Fintype.card_fin] at rows cols
  have scaled := Nat.mul_le_mul_left (t+1) cap
  simp only [Nat.mul_add] at scaled rows cols ⊢
  nlinarith only [scaled,rows,cols]

theorem sound_product_bound (q : ℕ) (hq : 1≤q) (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (a b : K→Fn (Fin N)) (good : ∀ i,sound I q (a i) (b i))
    (gs hs : List (Node (Fin N))) (ga : Built (base univ) gs) (gb : Built (base univ) hs)
    (ha : ∀ i,a i∈pool (base univ) gs) (hb : ∀ i,b i∈pool (base univ) hs) :
    (∑ p,(edges a b p).card)≤gs.length+hs.length+2*Fintype.card K+2*N := by
  have h := sound_product_scaled q q hq le_rfl I ord hd hj a b good gs hs ga gb ha hb
  exact Nat.le_of_mul_le_mul_left h (by omega)

end GateElim.Products
#print axioms GateElim.Products.sound_product_bound
