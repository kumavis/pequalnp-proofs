import ProtectedProducts
import GateActivation

namespace GateElim.Plane
open Desk2008 Reverse Block Cuts Products Rows Finset Classical
variable {N n q : ℕ}

noncomputable def endpointRows (I : Fin N→Fin N→Prop) [DecidableRel I] (t : ℕ) (P : Prog n) (x z : SideFn N n) :=
  protectedRows I t (fun g : ↥(sources P x z).toFinset => g.val.1) (fun g => g.val.2)

theorem endpoint_cost (q t : ℕ) (ht : 1≤t) (tq : t≤q) (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (P : Prog n) (x z : SideFn N n)
    (ax : ∀ i,x i∈base univ) (az : ∀ i,z i∈base univ) :
    (t+1)*(∑ p,(endpointRows I t P x z p).card)≤(q+1)*(6*P.size+2*N) := by
  let K := (sources P x z).toFinset
  obtain ⟨gs,hs,gl,hl,gb,hb,ready⟩ := banks P x z (base univ) (base univ) ax az
  have h := local_protection q t ht tq I ord hd hj (fun g : K => g.val.1) (fun g => g.val.2) gs hs gb hb
    (fun g => (ready g.val (List.mem_toFinset.mp g.property)).1) (fun g => (ready g.val (List.mem_toFinset.mp g.property)).2)
  have cap : K.card≤2*P.size := (List.toFinset_card_le _).trans (sources_len P x z)
  change (t+1)*(∑ p,(endpointRows I t P x z p).card)≤(q+1)*(gs.length+hs.length+2*Fintype.card K+2*N) at h
  simp only [gl,hl,Fintype.card_coe] at h
  exact h.trans (Nat.mul_le_mul_left _ (by omega))

/-- A failed protection test has a witness on a single side, and that
witness avoids the pencil at the *same endpoint* of the edge in question. -/
theorem one_sided_witness (I : Fin N→Fin N→Prop) [DecidableRel I] (t : ℕ) (P : Prog n) (x z : SideFn N n)
    (p l : Fin N) (miss : l∉endpointRows I t P x z p) (g : Birth (Fin N)) (mem : g∈births P 0 x z)
    (fires : g.fires (onSet {p}) (onSet {l})) :
    (∃ Y : Finset (Fin N),Disjoint Y (rowSet true I p) ∧ Y.card≤t ∧ g.line (onSet Y)=true) ∨
    (∃ X : Finset (Fin N),Disjoint X (rowSet false I l) ∧ X.card≤t ∧ g.point (onSet X)=true) := by
  classical
  by_contra! none
  have prove (D : Finset (Fin N)) (f : Fn (Fin N))
      (h : ∀ U : Finset (Fin N),Disjoint U D → U.card≤t → f (onSet U)≠true) : protects D t f :=
    fun U d s => Bool.eq_false_iff.mpr (h U d s)
  let v : ↥(sources P x z).toFinset := ⟨(g.point,g.line),List.mem_toFinset.mpr (birth_mem P 0 x z g mem).1⟩
  apply miss; apply mem_filter.mpr
  exact ⟨mem_univ _,v,(label_mem ..).mpr ⟨mem_filter.mpr ⟨mem_univ _,fires.1⟩,prove _ _ none.1⟩,
    (label_mem ..).mpr ⟨mem_filter.mpr ⟨mem_univ _,fires.2.1⟩,prove _ _ none.2⟩⟩

end GateElim.Plane
#print axioms GateElim.Plane.endpoint_cost
#print axioms GateElim.Plane.one_sided_witness
