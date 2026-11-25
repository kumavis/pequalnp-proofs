import PlaneModel
import Fraction

namespace GateElim.Plane
open Desk2008 Desk2008.Residual Desk2008.Fanout PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Finset Classical

theorem sides_large {N k : ℕ} (A : Finset (Vertex N)) (large : N+N ≤ A.card+k) :
    N≤(pts A).card+k ∧ N≤(lns A).card+k := by
  have p := (pts A).card_le_univ
  have l := (lns A).card_le_univ
  simp only [Fintype.card_fin] at p l
  rw [split_card A] at large
  omega

theorem weak_sides {q N d K : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (join : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (B : Finset (Vertex N))
    (pbig : N≤d*(pts B).card) (lbig : N≤d*(lns B).card) (dp : 1≤d) (dq : d≤q)
    (num : (d-1)*N*q≤K*(q+1-d)^2) :
    (pts (weak I B)).card≤K ∧ (lns (weak I B)).card≤K := by
  obtain ⟨dual,meet⟩ := dual_axioms I ord hd join
  exact ⟨(Finset.card_le_card (low_left I B)).trans (few_at_fraction I ord hd join _ lbig dp dq num),
    (Finset.card_le_card (low_right I B)).trans
      (few_at_fraction (fun l p => I p l) ord dual meet _ pbig dp dq num)⟩

theorem some_edge {N : ℕ} (I : Fin N → Fin N → Prop) (B : Finset (Vertex N))
    (large : (pts (weak I B)).card < (pts B).card) : EdgeIn (adj I) B := by
  classical
  obtain ⟨p,hp,ok⟩ := Finset.exists_mem_notMem_of_card_lt_card large
  have strong : Strong (adj I) B (left p) := by simpa [pts,weak] using ok
  obtain ⟨a,ha,_,_,_,ia,_⟩ := strong
  exact ⟨left p,(Finset.mem_filter.mp hp).2,a,ha,ia⟩

/-- All intermediate restrictions still have a surviving incidence and admit
the same bound on the number of low-degree vertices. -/
theorem peel_plane {q N d K k : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (ord : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (join : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (hm : Monotone2 C)
    (out : C.output<N+N+C.size) (norm : Normal (N+N) C)
    (fit : Fits (adj I) Finset.univ (circuitFun (N+N) C))
    (density : N≤d*(N-k)) (enough : K+k<N) (dp : 1≤d) (dq : d≤q)
    (num : (d-1)*N*q≤K*(q+1-d)^2) :
    ∃ B : Finset (Vertex N), B.card+k=N+N ∧ ∃ G : Fn (Vertex N), ∃ tail : List (Node (Vertex N)),
      Ready (base B) tail G ∧ Fits (adj I) B G ∧
      tail.length+2*k ≤ C.size + ((weak I B) \ B).card := by
  classical
  obtain ⟨gs,len,ready⟩ := from_desk C norm hm out
  have cont (A : Finset (Vertex N)) (_ : A⊆Finset.univ)
      (big : (Finset.univ : Finset (Vertex N)).card<A.card+k) : EdgeIn (adj I) A := by
    simp only [Finset.card_univ,Fintype.card_fin] at big
    obtain ⟨p,l⟩ := sides_large A big.le
    have pw := (weak_sides I ord hd join A (density.trans (Nat.mul_le_mul_left d (by omega)))
      (density.trans (Nat.mul_le_mul_left d (by omega))) dp dq num).1
    exact some_edge I A (by omega)
  obtain ⟨B,_,card,G,tail,h,f,cost⟩ :=
    peel_many (loopless I) (fun {_ _} h => adjSymm I h) (separated I join) k Finset.univ _ gs ready fit cont
  have eq : ((Finset.univ \ B).filter fun i => ¬Strong (adj I) B i) = (weak I B) \ B := by
    ext u; simp [weak,and_comm]
  exact ⟨B,by simpa using card,G,tail,h,f,by simpa [eq,len] using cost⟩

theorem plane_bound {q N d K k : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (ord : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (join : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (hm : Monotone2 C)
    (out : C.output<N+N+C.size) (norm : Normal (N+N) C)
    (fit : Fits (adj I) Finset.univ (circuitFun (N+N) C))
    (density : N≤d*(N-k)) (enough : K+k<N) (dp : 1≤d) (dq : d≤q)
    (num : (d-1)*N*q≤K*(q+1-d)^2) : N+N+k≤C.size+1+2*K := by
  classical
  obtain ⟨B,card,G,tail,run,good,budget⟩ := peel_plane I C ord hd join hm out norm fit density enough dp dq num
  obtain ⟨p,l⟩ := sides_large B card.ge
  obtain ⟨wp,wl⟩ := weak_sides I ord hd join B (density.trans (Nat.mul_le_mul_left d (by omega)))
    (density.trans (Nat.mul_le_mul_left d (by omega))) dp dq num
  have total := split_card (weak I B)
  have basecost : (B \ weak I B).card≤tail.length+1 := by
    apply support_size B _ tail G run
    intro i hi
    obtain ⟨ib,ig⟩ := Finset.mem_sdiff.mp hi
    have st : Strong (adj I) B i := by simpa [weak] using ig
    obtain ⟨a,ha,_,_,_,ia,_⟩ := st
    exact fits_essential (loopless I) good ib ha ia
  have eq1 := Finset.card_sdiff_add_card_inter B (weak I B)
  have eq2 := Finset.card_sdiff_add_card_inter (weak I B) B
  rw [Finset.inter_comm (weak I B) B] at eq2
  omega

end GateElim.Plane
#print axioms GateElim.Plane.plane_bound
