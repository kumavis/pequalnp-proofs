import DeskBlocks

namespace GateElim.Products
open Reverse Cuts Rows Block Finset Classical
variable {V J K : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

noncomputable def owned (a : K→Fn J) (j : J) := univ.filter fun i => foot (a i)={j}
noncomputable def covered (a : K→Fn J) (b : K→Fn V) (j : J) :=
  (owned a j).biUnion fun i => foot (b i)
noncomputable def agg (a : K→Fn J) (b : K→Fn V) (j : J) : Fn V :=
  fun y => decide (∃ i∈owned a j,b i y=true)

theorem owners (a : K→Fn J) : (∑ j,(owned a j).card)≤Fintype.card K := by
  simp only [owned,card_filter]; rw [sum_comm]
  have per (i : K) : (∑ j : J, if foot (a i)={j} then 1 else 0)≤1 := by
    rw [←card_filter]; apply card_le_one.mpr
    intro p hp r hr
    exact Finset.singleton_inj.mp ((mem_filter.mp hp).2.symm.trans (mem_filter.mp hr).2)
  simpa using sum_le_sum (s:=univ) (fun i _ => per i)

theorem owned_partial (s q : ℕ) (S : J→Finset V) (a : K→Fn J) (b : K→Fn V)
    (gs : List (Node V)) (sz : gs.length ≤ s) (built : Built (base univ) gs)
    (has : ∀ i,b i∈pool (base univ) gs)
    (linear : ∀ i j,i≠j → (S i∩S j).card≤1) (kept : J→Finset V)
    (inside : ∀ j,kept j⊆covered a b j) (cap : ∀ j,(kept j).card≤q+1)
    (safe : ∀ j i,i∈owned a j → ∀ U,Disjoint U (S j) → U.card≤q → b i (onSet U)=false) :
    (∑ j,(kept j).card) ≤ s+Fintype.card K+Fintype.card J := by
  let U := pool (base (univ : Finset V)) gs
  obtain ⟨hs,len,bu,av⟩ := gather (univ : Finset J) U (fun j => {agg a b j}) (fun j => (owned a j).card) (by
    intro j _ T incl
    obtain ⟨ls,f,l,built',ready,eq⟩ := join_values (owned a j) b T (fun i _ => incl (has i))
      (incl (pool_grows _ _ (Or.inl ⟨false,rfl⟩)))
    have e : f=agg a b j := by funext y; apply Bool.eq_iff_iff.mpr; simp [eq,agg]
    exact ⟨ls,l.le,built',Set.singleton_subset_iff.mpr (e ▸ ready)⟩)
  have ready (j : J) : Ready (base univ) (gs++hs) (agg a b j) := by
    apply ready_of_built (build_append built bu); rw [pool_append]; exact av j (mem_univ _) (Set.mem_singleton _)
  have lower := circuit_bound S kept (agg a b) (gs++hs) univ linear ready (by
    intro j v hv; obtain ⟨i,hi,yes⟩ := mem_biUnion.mp (inside j hv)
    exact decide_eq_true ⟨i,hi,(mem_filter.mp yes).2⟩) (by
    intro j V' dis small
    have card := cap j
    apply Bool.eq_false_iff.mpr; intro h
    obtain ⟨i,hi,yes⟩ := of_decide_eq_true h
    exact Bool.noConfusion (yes.symm.trans (safe j i hi V' dis (by omega))))
  have each (j : J) : (kept j).card≤((kept j).card-1)+1 := by omega
  have add := sum_le_sum (s:=univ) (fun j _ => each j)
  simp only [sum_add_distrib,sum_const,card_univ,smul_eq_mul,mul_one] at add
  simp only [List.length_append] at lower
  have spent := len.trans (owners a)
  omega

theorem owned_bound (s q : ℕ) (S : J→Finset V) (a : K→Fn J) (b : K→Fn V)
    (gs : List (Node V)) (sz : gs.length ≤ s) (built : Built (base univ) gs)
    (has : ∀ i,b i∈pool (base univ) gs)
    (linear : ∀ i j,i≠j → (S i∩S j).card≤1) (deg : ∀ j,(S j).card=q+1)
    (inside : ∀ j,covered a b j⊆S j)
    (safe : ∀ j i,i∈owned a j → ∀ U,Disjoint U (S j) → U.card≤q → b i (onSet U)=false) :
    (∑ j,(covered a b j).card) ≤ s+Fintype.card K+Fintype.card J := by
  exact owned_partial s q S a b gs sz built has linear (covered a b) (fun _ => Subset.rfl)
    (fun j => (card_le_card (inside j)).trans (deg j).le) safe

theorem owned_scaled (s q t : ℕ) (small : t≤q) (S : J→Finset V) (a : K→Fn J) (b : K→Fn V)
    (gs : List (Node V)) (sz : gs.length ≤ s) (built : Built (base univ) gs)
    (has : ∀ i,b i∈pool (base univ) gs)
    (linear : ∀ i j,i≠j → (S i∩S j).card≤1) (deg : ∀ j,(S j).card=q+1)
    (inside : ∀ j,covered a b j⊆S j)
    (safe : ∀ j i,i∈owned a j → ∀ U,Disjoint U (S j) → U.card≤t → b i (onSet U)=false) :
    (t+1)*(∑ j,(covered a b j).card) ≤ (q+1)*(s+Fintype.card K+Fintype.card J) := by
  classical
  have sel (j : J) := Finset.exists_subset_card_eq (s:=covered a b j) (min_le_left (covered a b j).card (t+1))
  choose kept sub size using sel
  have cost := owned_partial s t S a b gs sz built has linear kept sub (fun j => (size j).trans_le (min_le_right ..)) safe
  have per (j : J) : (t+1)*(covered a b j).card≤(q+1)*(kept j).card := by
    rw [size]
    have cap := (card_le_card (inside j)).trans (deg j).le
    rcases le_total (covered a b j).card (t+1) with h|h
    · rw [min_eq_left h]; exact Nat.mul_le_mul_right _ (by omega)
    · rw [min_eq_right h,Nat.mul_comm (t+1)]; exact Nat.mul_le_mul_right _ cap
  have bound := sum_le_sum (s:=univ) (fun j _ => per j)
  simp only [←mul_sum] at bound
  exact bound.trans (Nat.mul_le_mul_left _ cost)

end GateElim.Products
#print axioms GateElim.Products.owned_bound
