import DeskProducts

namespace GateElim.Plane
open Desk2008 Reverse Block Cuts Rows Products Finset Classical
variable {N n : ℕ}
abbrev SideFn (N n : ℕ) := Fin n→Fn (Fin N)

noncomputable def goodAt (I : Fin N→Fin N→Prop) (t : ℕ) (P : Prog n) (x z : SideFn N n) :=
  (sources P x z).toFinset.filter fun g => sound I t g.1 g.2
noncomputable def edgesAt (I : Fin N→Fin N→Prop) (t : ℕ) (P : Prog n) (x z : SideFn N n) (p : Fin N) :=
  edges (fun g : ↥(goodAt I t P x z) => g.val.1) (fun g => g.val.2) p

/-- Allow any constants and any residual subsets as the two side projections.
The leakage threshold t can be smaller than the original sparsity cap q. -/
theorem coverage_at (q t : ℕ) (ht : 1≤t) (tq : t≤q) (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (P : Prog n) (x z : SideFn N n)
    (ax : ∀ i,x i∈base univ) (az : ∀ i,z i∈base univ) :
    (t+1)*(∑ p,(edgesAt I t P x z p).card)≤(q+1)*(6*P.size+2*N) := by
  classical
  let A := goodAt I t P x z
  obtain ⟨gs,hs,gl,hl,gb,hb,ready⟩ := banks P x z (base univ) (base univ) ax az
  have mem (g : A) : g.val∈sources P x z := List.mem_toFinset.mp (mem_filter.mp g.property).1
  have h := sound_product_scaled q t ht tq I ord hd hj (fun g : A => g.val.1) (fun g => g.val.2)
    (fun g => (mem_filter.mp g.property).2) gs hs gb hb (fun g => (ready g.val (mem g)).1)
    (fun g => (ready g.val (mem g)).2)
  have cap : A.card≤2*P.size := (Finset.card_filter_le (sources P x z).toFinset (fun g => sound I t g.1 g.2)).trans
    ((List.toFinset_card_le _).trans (sources_len P x z))
  change (t+1)*(∑ p,(edgesAt I t P x z p).card)≤(q+1)*(gs.length+hs.length+2*Fintype.card A+2*N) at h
  simp only [gl,hl,Fintype.card_coe] at h
  exact h.trans (Nat.mul_le_mul_left _ (by omega))

theorem bad_at (I : Fin N→Fin N→Prop) (t : ℕ) (P : Prog n) (x z : SideFn N n) (p l : Fin N)
    (missing : l∉edgesAt I t P x z p)
    (g : Fn (Fin N)×Fn (Fin N)) (occ : g∈sources P x z) (a : g.1 (onSet {p})=true) (b : g.2 (onSet {l})=true) :
    ∃ X Y : Finset (Fin N),X.card≤t ∧ Y.card≤t ∧ (X.card=1 ∨ Y.card=1) ∧
      g.1 (onSet X)=true ∧ g.2 (onSet Y)=true ∧ ¬∃ p∈X,∃ l∈Y,I p l := by
  classical
  have notGood : ¬sound I t g.1 g.2 := by
    intro yes; apply missing
    have member : g∈goodAt I t P x z := mem_filter.mpr ⟨List.mem_toFinset.mpr occ,yes⟩
    exact mem_filter.mpr ⟨mem_univ _,⟨g,member⟩,mem_filter.mpr ⟨mem_univ _,a⟩,mem_filter.mpr ⟨mem_univ _,b⟩⟩
  unfold sound at notGood; push Not at notGood ⊢; exact notGood

end GateElim.Plane
#print axioms GateElim.Plane.coverage_at
