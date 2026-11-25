import Core
import PlanePeel

namespace GateElim.Plane
open Desk2008 Desk2008.Residual Desk2008.Fanout PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Finset Classical

/-- A surviving core retains the previous 4/3 lower bound per input. Vertices
outside the core or deleted cheaply by peeling are counted together. -/
theorem core_bound {q N d K k t : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (ord : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (join : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (hm : Monotone2 C)
    (out : C.output<N+N+C.size) (norm : Normal (N+N) C)
    (fit : Fits (adj I) Finset.univ (circuitFun (N+N) C))
    (density : N≤d*t) (room : k+t+K≤N) (reserve : K≤t) (tpos : 2≤t)
    (dp : 1≤d) (dq : d≤q) (qpos : 8≤q)
    (num : (d-1)*N*q≤K*(q+1-d)^2) :
    8*N+2*k ≤ 3*C.size+1+4*(K+q+3) := by
  classical
  obtain ⟨B,card,G,tail,run,fits,cost⟩ := peel_plane I C ord hd join hm out norm fit
    (density.trans (Nat.mul_le_mul_left d (by omega))) (by omega : K+k<N) dp dq num
  obtain ⟨bp,bl⟩ := sides_large B card.ge
  let safe (D : Finset (Vertex N)) := t≤(pts D).card ∧ t≤(lns D).card
  have start : safe B := ⟨by omega,by omega⟩
  have bound (D : Finset (Vertex N)) (ok : safe D) := weak_sides I ord hd join D
    (density.trans (Nat.mul_le_mul_left d ok.1)) (density.trans (Nat.mul_le_mul_left d ok.2)) dp dq num
  have keep (D : Finset (Vertex N)) (sub : D⊆B) (ok : safe D)
      (before : ∀ u∈B, u∉D → ¬Strong (adj I) D u)
      (i : Vertex N) (_ : i∈D) (low : ¬Strong (adj I) D i) : safe (D.erase i) := by
    have removed (u : Vertex N) (hu : u∈B) (out : u∉D.erase i) : u∈weak I D := by
      apply Finset.mem_filter.mpr; refine ⟨by simp,?_⟩
      by_cases eq : u=i
      · simpa [eq] using low
      · exact before u hu (fun inside => out (Finset.mem_erase.mpr ⟨eq,inside⟩))
    obtain ⟨pw,lw⟩ := bound D ok
    have sp : pts (D.erase i)⊆pts B := by
      intro p hp; exact Finset.mem_filter.mpr ⟨by simp,sub (Finset.mem_erase.mp (Finset.mem_filter.mp hp).2).2⟩
    have sl : lns (D.erase i)⊆lns B := by
      intro l hl; exact Finset.mem_filter.mpr ⟨by simp,sub (Finset.mem_erase.mp (Finset.mem_filter.mp hl).2).2⟩
    have pp : pts B \ pts (D.erase i) ⊆ pts (weak I D) := by
      intro p h; obtain ⟨yes,no⟩ := Finset.mem_sdiff.mp h
      exact Finset.mem_filter.mpr ⟨by simp,removed _ (Finset.mem_filter.mp yes).2
        (fun h => no (Finset.mem_filter.mpr ⟨by simp,h⟩))⟩
    have ll : lns B \ lns (D.erase i) ⊆ lns (weak I D) := by
      intro l h; obtain ⟨yes,no⟩ := Finset.mem_sdiff.mp h
      exact Finset.mem_filter.mpr ⟨by simp,removed _ (Finset.mem_filter.mp yes).2
        (fun h => no (Finset.mem_filter.mpr ⟨by simp,h⟩))⟩
    have pc := (Finset.card_le_card pp).trans pw
    have lc := (Finset.card_le_card ll).trans lw
    have pe := Finset.card_sdiff_add_card_eq_card sp
    have le := Finset.card_sdiff_add_card_eq_card sl
    exact ⟨by omega,by omega⟩
  obtain ⟨D,sub,ok,deleted,all,F,gs,computes,correct,short⟩ := core B run fits safe start keep
  have smallInput := split_card D
  obtain ⟨dpw,dlw⟩ := bound D ok
  have weakCount := split_card (weak I D)
  have dsize : 2≤D.card := by have := ok.1; omega
  have residual := core_size (loopless I) (fun {_ _} h => adjSymm I h) (separated I join)
    D F gs computes correct dsize all
  have lost : ((weak I B) \ B) ∪ (B \ D) ⊆ weak I D := by
    intro u hu
    rcases Finset.mem_union.mp hu with h|h
    · have l := (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2
      exact Finset.mem_filter.mpr ⟨by simp,fun strong => l (strong_mono sub u strong)⟩
    · obtain ⟨hb,miss⟩ := Finset.mem_sdiff.mp h
      exact Finset.mem_filter.mpr ⟨by simp,deleted u hb miss⟩
  have dis : Disjoint ((weak I B) \ B) (B \ D) := by
    apply Finset.disjoint_left.mpr
    intro u h g; exact (Finset.mem_sdiff.mp h).2 (Finset.mem_sdiff.mp g).1
  have debt := Finset.card_le_card lost
  rw [Finset.card_union_of_disjoint dis] at debt
  have eq := Finset.card_sdiff_add_card_eq_card sub
  have half : N≤2*(pts D).card ∨ N≤2*(lns D).card := by omega
  have total : (weak I D).card≤K+q+3 := by
    rcases half with hp|hl
    · obtain ⟨dual,meet⟩ := dual_axioms I ord hd join
      have few := (Finset.card_le_card (low_right I D)).trans
        (few_low (fun l p => I p l) qpos ord dual meet (pts D) hp)
      omega
    · have few := (Finset.card_le_card (low_left I D)).trans
        (few_low I qpos ord hd join (lns D) hl)
      omega
  omega

end GateElim.Plane
#print axioms GateElim.Plane.core_bound
