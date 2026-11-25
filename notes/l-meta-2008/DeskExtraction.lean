import PlaneRows

namespace GateElim.Plane
open Desk2008 Desk2008.Residual Desk2008.Fanout PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Reverse Rows Finset Classical
attribute [-simp] Fin.natAdd_eq_addNat
variable {N q : ℕ}

private theorem zero_side (side : Bool) (v : Fin N) (I : Fin N → Fin N → Prop) (hq : 1≤q)
    (P : Prog (N+N))
    (neg : ∀ x : Vertex N → Bool, Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → P.eval x=false) :
    P.eval (fun i => baseline side i (onSet {v}))=false := by
  apply neg
  · cases side <;> simp [Fintype.card_subtype,baseline,const,var,onSet,right,hq]
  · cases side <;> simp [baseline,left,right,const]

theorem singleton_selected (j v : Fin N) (side : Bool) :
    selected (baseline side) (pick side j) (onSet {v}) =
      fun i => if side then decide (i=left j ∨ i=right v) else decide (i=left v ∨ i=right j) := by
  funext i
  cases side <;> induction i using Fin.addCases with
  | left p => simp [selected,baseline,pick,onSet,var,const,lr]
  | right l => simp [selected,baseline,pick,onSet,var,const,fun l p => (lr p l).symm]

theorem all_simple_of_disjoint (side : Bool) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (P : Prog (N+N)) (hq : 1≤q)
    (pos : ∀ p l, I p l → P.eval (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N → Bool, Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → P.eval x=false)
    (sep : P.disjoint (initScope (pick (N:=N) side))) (j : Fin N) :
    simpleSet P side I j = rowSet side I j := by
  apply Finset.filter_true_of_mem
  intro v incident
  apply disjoint_simple P (baseline side) (pick side) sep j v (zero_side side v I hq P neg)
  rw [singleton_selected]
  cases side <;> simp only [Bool.false_eq_true,↓reduceIte]
  · exact pos v j (by simpa [rowSet] using incident)
  · exact pos j v (by simpa [rowSet] using incident)

/-- In the original desk encoding, any AND-disjointness condition on just
one chosen side suffices for every order q. The other side can repeat freely. -/
theorem desk_disjoint {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 1≤q) (order : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C) (out : C.output<N+N+C.size) (norm : Normal (N+N) C)
    (pos : ∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N → Bool, Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false)
    (side : Bool) (sep : ∀ P, decode (N+N) C.gates C.output=some P →
      P.disjoint (initScope (pick (N:=N) side))) : N*q≤5*C.size := by
  obtain ⟨P,par,len,ev⟩ := parse_desk C norm hm out
  have hn := fun x hl hh => (ev x).trans (neg x hl hh)
  have simps := all_simple_of_disjoint side I P hq (fun p l i => (ev _).trans (pos p l i)) hn (sep P par)
  have h := simple_gate_bound q hq I order hd hj P hn side
  simp_rw [simps,(row_geometry I order hd hj side).1] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_add,mul_one,len] at h
  omega

/-- A candidate smaller than Nq/100 must have many incidences for which
every accepting proof tree repeats the point and repeats the line. -/
noncomputable def doubleSet (P : Prog (N+N)) (I : Fin N → Fin N → Prop) [DecidableRel I] (j : Fin N) :=
  (rowSet true I j).filter fun l => l∉simpleSet P true I j ∧ j∉simpleSet P false I l

theorem desk_double {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 1≤q) (order : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C) (out : C.output<N+N+C.size) (norm : Normal (N+N) C)
    (neg : ∀ x : Vertex N → Bool, Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false) :
    ∃ P, decode (N+N) C.gates C.output=some P ∧
      N*(q+1) ≤ (∑ p, (doubleSet P I p).card)+10*C.size+2*N := by
  classical
  obtain ⟨P,par,len,ev⟩ := parse_desk C norm hm out
  refine ⟨P,par,?_⟩
  have hn := fun x hl hh => (ev x).trans (neg x hl hh)
  have pts := simple_gate_bound q hq I order hd hj P hn true
  have lns := simple_gate_bound q hq I order hd hj P hn false
  let col (p : Fin N) := univ.filter fun l => p∈simpleSet P false I l
  have split (p : Fin N) : rowSet true I p⊆doubleSet P I p∪simpleSet P true I p∪col p := by
    intro l hl
    by_cases a : l∈simpleSet P true I p
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ a)
    by_cases b : p∈simpleSet P false I l
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨by simp,b⟩)
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hl,a,b⟩))
  have each (p : Fin N) : q+1 ≤ (doubleSet P I p).card+(simpleSet P true I p).card+(col p).card := by
    rw [←(row_geometry I order hd hj true).1 p]
    have h := Finset.card_le_card (split p)
    have x := Finset.card_union_le (doubleSet P I p) (simpleSet P true I p)
    have y := Finset.card_union_le (doubleSet P I p∪simpleSet P true I p) (col p)
    omega
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => each p)
  have swap : ∑ p, (col p).card = ∑ l, (simpleSet P false I l).card := by
    simp only [col,Finset.card_filter]
    rw [Finset.sum_comm]; simp
  simp only [Finset.sum_add_distrib] at total
  rw [swap] at total
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at total
  rw [len] at pts lns
  simpa only [Nat.mul_add,mul_one] using (show N*q+N ≤ (∑ p, (doubleSet P I p).card)+10*C.size+2*N by
    simp only [Nat.mul_add,mul_one] at total; omega)

end GateElim.Plane
#print axioms GateElim.Plane.desk_double
#print axioms GateElim.Plane.desk_disjoint
