import ResidualGeometry

namespace Desk2008.Residual

/-- Derive the dual axioms from the exact two incidence axioms in the desk. -/
theorem dual_axioms {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (order : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (join : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) :
    (∀ p, Fintype.card {l : Fin N // I p l}=q+1) ∧
    (∀ a b : Fin N, a≠b → ∃! p, I p a ∧ I p b) := by
  classical
  have v := variance I order hd join Finset.univ
  simp only [Finset.card_univ,Fintype.card_fin,sub_self,mul_zero] at v
  have hN : 0<N := by omega
  have point (p : Fin N) : Fintype.card {l : Fin N // I p l}=q+1 := by
    have single := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun r => ((N : ℤ)*degree I Finset.univ r-N*(q+1))^2)
      (fun r _ => sq_nonneg _) (Finset.mem_univ p)
    have zero := le_antisymm (single.trans v) (sq_nonneg _)
    have root : (N : ℤ)*degree I Finset.univ p = N*(q+1) :=
      sub_eq_zero.mp ((sq_eq_zero_iff).mp zero)
    have e : (degree I Finset.univ p : ℤ) = (q : ℤ)+1 :=
      mul_left_cancel₀ (show (N:ℤ)≠0 by exact_mod_cast hN.ne') root
    rw [Fintype.card_subtype]
    exact_mod_cast e
  refine ⟨point,?_⟩
  intro a b ab
  let S := Finset.univ.filter (fun p => I p a)
  let other (p : Fin N) := (Finset.univ.filter (I p)).erase a
  have cs : S.card=q+1 := by simpa [S,Fintype.card_subtype] using hd a
  have cp (p : Fin N) (hp : p∈S) : (other p).card=q := by
    have ha : a∈Finset.univ.filter (I p) := Finset.mem_filter.mpr ⟨by simp,(Finset.mem_filter.mp hp).2⟩
    have count := Finset.card_erase_add_one ha
    have total : (Finset.univ.filter (I p)).card=q+1 := by
      simpa [Fintype.card_subtype] using point p
    change ((Finset.univ.filter (I p)).erase a).card=q
    omega
  have dis : (↑S : Set (Fin N)).PairwiseDisjoint other := by
    intro p hp r hr ne
    apply Finset.disjoint_left.mpr
    intro t pt rt
    obtain ⟨ta,pMem⟩ := Finset.mem_erase.mp pt
    obtain ⟨_,rMem⟩ := Finset.mem_erase.mp rt
    obtain ⟨m,_,unique⟩ := join p r ne
    exact ta ((unique t ⟨(Finset.mem_filter.mp pMem).2,(Finset.mem_filter.mp rMem).2⟩).trans
      (unique a ⟨(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hr).2⟩).symm)
  have same : S.biUnion other = Finset.univ.erase a := by
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      obtain ⟨p,_,h⟩ := Finset.mem_biUnion.mp ht
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp h).1,by simp⟩
    · rw [Finset.card_biUnion dis,Finset.sum_congr rfl cp]
      simp [cs,order,Nat.add_mul,pow_two]
  have bIn : b∈S.biUnion other := same ▸ Finset.mem_erase.mpr ⟨ab.symm,by simp⟩
  obtain ⟨p,pa,pb⟩ := Finset.mem_biUnion.mp bIn
  have both : I p a ∧ I p b :=
    ⟨(Finset.mem_filter.mp pa).2,(Finset.mem_filter.mp (Finset.mem_erase.mp pb).2).2⟩
  refine ⟨p,both,?_⟩
  intro r hr
  by_contra ne
  obtain ⟨m,_,unique⟩ := join r p ne
  exact ab ((unique a ⟨hr.1,both.1⟩).trans (unique b ⟨hr.2,both.2⟩).symm)

/-- After deleting vertices, poor vertices on each side remain few as long as
at least half the opposite side survives. -/
theorem both_sides {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 8≤q) (order : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (join : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (P L : Finset (Fin N)) (points : N≤2*P.card) (lines : N≤2*L.card) :
    (Finset.univ.filter (fun p => degree I L p≤1)).card ≤ q+3 ∧
    (Finset.univ.filter (fun l => degree (fun a b => I b a) P l≤1)).card ≤ q+3 := by
  obtain ⟨dualSize,dualJoin⟩ := dual_axioms I order hd join
  exact ⟨few_low I hq order hd join L lines, few_low (fun a b => I b a) hq order dualSize dualJoin P points⟩

end Desk2008.Residual
#print axioms Desk2008.Residual.both_sides
