import CutBudget
import Through365
import MarkCoverage
import DeskExtraction

namespace GateElim.Plane
open Desk2008 Desk2008.Residual Desk2008.Fanout PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Reverse Cuts Rows Finset Classical
variable {N q : ℕ}

def markedValue (P : Prog (N+N)) (M : ℕ→Bool) (side : Bool) (j : Fin N) (y : Fin N→Bool) :=
  Prog.model P M 0 (fun i => baseline side i y) (selected (baseline side) (pick side j) y)

def captured (P : Prog (N+N)) (M : ℕ→Bool) (side : Bool) (I : Fin N→Fin N→Prop) [DecidableRel I]
    (j : Fin N) := (rowSet side I j).filter fun v => markedValue P M side j (onSet {v})=true

/-- Only incidences surviving the marked evaluation are counted. The
marks may be chosen anywhere, even when the two input scopes overlap elsewhere. -/
theorem captured_tradeoff (q : ℕ) (hq : 1≤q) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (P : Prog (N+N))
    (neg : ∀ x : Vertex N → Bool, Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → P.eval x=false) (side : Bool) (M : ℕ→Bool) :
    ∑ j, ((captured P M side I j).card-1) ≤ rowCost P.size (tally M P.size) N := by
  obtain ⟨gs,len,ready⟩ := extract_marked P M (baseline side) (pick side) (base Finset.univ)
    (base_legal side) (fun b => Or.inl ⟨b,rfl⟩)
  obtain ⟨deg,linear⟩ := row_geometry I ord hd hj side
  have lower := Rows.circuit_bound (rowSet side I) (captured P M side I) (markedValue P M side)
    gs Finset.univ linear ready (fun _ _ h => (Finset.mem_filter.mp h).2) (by
      intro j U dis few
      have sub : (captured P M side I j).card≤(rowSet side I j).card := Finset.card_filter_le ..
      rw [deg] at sub
      have ok := legal q hq I side j U (by omega) dis
      apply Bool.eq_false_iff.mpr
      intro yes
      have on := model_sound P M 0 _ _ _ (fun i h => by simp [selected,h]) (fun _ => id) yes
      rw [neg _ ok.1 ok.2] at on
      contradiction)
  simpa using lower.trans len

theorem captured_card (q : ℕ) (hq : 1≤q) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (P : Prog (N+N))
    (neg : ∀ x : Vertex N → Bool, Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → P.eval x=false) (side : Bool) (M : ℕ→Bool) :
    ∑ j, (captured P M side I j).card ≤ rowCost P.size (tally M P.size) N + N := by
  have h := captured_tradeoff q hq I ord hd hj P neg side M
  have each (j : Fin N) : (captured P M side I j).card≤((captured P M side I j).card-1)+1 := by omega
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => each j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at total
  omega

theorem covered_tradeoff (q : ℕ) (hq : 1≤q) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (P : Prog (N+N))
    (neg : ∀ x : Vertex N → Bool, Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → P.eval x=false) (side : Bool) (M : ℕ→Bool)
    (all : ∀ j, captured P M side I j=rowSet side I j) :
    N*q ≤ rowCost P.size (tally M P.size) N := by
  have h := captured_tradeoff q hq I ord hd hj P neg side M
  simp_rw [all,(row_geometry I ord hd hj side).1] at h
  simpa [Finset.sum_const] using h

theorem cut_tradeoff (q : ℕ) (hq : 1≤q) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (P : Prog (N+N))
    (pos : ∀ p l, I p l → P.eval (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N → Bool, Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → P.eval x=false) (side : Bool) :
    N*q ≤ rowCost P.size (ProgCuts P (initScope (pick (N:=N) side))) N := by
  obtain ⟨M,count,works⟩ := syntactic_marks P (initScope (pick (N:=N) side))
  rw [←count]
  apply covered_tradeoff q hq I ord hd hj P neg side M
  intro j; apply Finset.filter_true_of_mem
  intro v inc; unfold markedValue
  have cover := input_cover (baseline (N:=N) side) (pick side)
  rw [works j _ (selected (baseline side) (pick side j) (onSet {v})) (fun i => (cover j i).1 (onSet {v})) (fun i outside => congrFun ((cover j i).2 outside) _)]
  rw [singleton_selected]
  cases side <;> simp only [Bool.false_eq_true,↓reduceIte]
  · exact pos v j (by simpa [rowSet] using inc)
  · exact pos j v (by simpa [rowSet] using inc)

private theorem small_cost (N q s h : ℕ) (qbig : 308≤q) (hc : h≤7)
    (r : N*q≤rowCost s h N) : N*q≤100*s := by
  have one : (8*h+5)*s≤61*s := Nat.mul_le_mul_right s (by omega)
  have square : h^2≤49 := by simpa using Nat.pow_le_pow_left hc 2
  have two : (2*h^2+3*h+1)*N≤120*N := Nat.mul_le_mul_right N (by omega)
  have room := Nat.mul_le_mul_left N qbig
  unfold rowCost at r
  omega

theorem desk_seven_marked {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 100<q) (ord : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C) (out : C.output<N+N+C.size) (norm : Normal (N+N) C)
    (pos : ∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N → Bool, Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false)
    (side : Bool) (few : ∀ P, decode (N+N) C.gates C.output=some P →
      ∃ M, tally M P.size≤7 ∧ ∀ j, captured P M side I j=rowSet side I j) : N*q≤100*C.size := by
  by_cases low : q≤365
  · exact through_365 q hq low N I C ord hd hj hm out norm pos neg
  obtain ⟨P,par,len,ev⟩ := parse_desk C norm hm out
  obtain ⟨M,count,all⟩ := few P par
  have trade := covered_tradeoff q (by omega) I ord hd hj P (fun x hs hn => (ev x).trans (neg x hs hn)) side M all
  simpa [len] using small_cost N q P.size _ (by omega) count trade

theorem desk_seven {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 100<q) (ord : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C) (out : C.output<N+N+C.size) (norm : Normal (N+N) C)
    (pos : ∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N → Bool, Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false)
    (side : Bool) (few : ∀ P, decode (N+N) C.gates C.output=some P →
      ProgCuts P (initScope (pick (N:=N) side)) ≤ 7) : N*q≤100*C.size := by
  by_cases low : q≤365
  · exact through_365 q hq low N I C ord hd hj hm out norm pos neg
  obtain ⟨P,par,len,ev⟩ := parse_desk C norm hm out
  have trade := cut_tradeoff q (by omega) I ord hd hj P (fun p l hp => (ev _).trans (pos p l hp))
    (fun x hs hn => (ev x).trans (neg x hs hn)) side
  simpa [len] using small_cost N q P.size _ (by omega) (few P par) trade

end GateElim.Plane
#print axioms GateElim.Plane.cut_tradeoff
#print axioms GateElim.Plane.desk_seven

#print axioms GateElim.Plane.captured_card
#print axioms GateElim.Plane.desk_seven_marked
