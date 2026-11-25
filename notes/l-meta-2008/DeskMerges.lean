import MergeRoles
import DeskExtraction

namespace GateElim.Plane
open Desk2008 Desk2008.Fanout Desk2008.Residual PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Reverse MergeTrace Rows Finset Classical
attribute [-simp] Fin.natAdd_eq_addNat
variable {q N : ℕ}

def profile (I : Fin N→Fin N→Prop) [DecidableRel I] (side : Bool) (U : Fin N→Finset (Fin N))
    (j : Fin N) (i : Vertex N) : Signal (Fin N) :=
  ⟨selected (baseline side) (pick side j) (onSet (U j)) i,
    (rowSet side I j).filter fun v => selected (baseline side) (pick side j) (onSet {v}) i=true⟩

private theorem atom (I : Fin N→Fin N→Prop) [DecidableRel I] (side : Bool) (U : Fin N→Finset (Fin N))
    (j : Fin N) (i : Vertex N) (off : (profile I side U j i).neg=false) :
    (profile I side U j i).acc.card≤1 := by
  apply card_le_one.mpr
  intro a ha b hb
  have va := (mem_filter.mp ha).2
  have vb := (mem_filter.mp hb).2
  cases side <;> induction i using Fin.addCases with
  | left p => simp_all [profile,selected,baseline,pick,onSet,var,const,left,right]
  | right l => simp_all [profile,selected,baseline,pick,onSet,var,const,left,right]

private theorem legal_profile (q : ℕ) (hq : 1≤q) (I : Fin N→Fin N→Prop) [DecidableRel I]
    (side : Bool) (j : Fin N) (U : Finset (Fin N)) (size : side=true → U.card≤q)
    (dis : Disjoint U (rowSet side I j)) :
    let x := selected (baseline side) (pick side j) (onSet U)
    Fintype.card {l : Fin N // x (right l)=true}≤q ∧
      ¬∃ p l,I p l ∧ x (left p)=true ∧ x (right l)=true := by
  cases side with
  | true => exact legal q hq I true j U (size rfl) dis
  | false =>
    dsimp only
    have mem (p : Fin N) : selected (baseline false) (pick false j) (onSet U) (left p)=decide (p∈U) := by
      simp [selected,baseline,pick,onSet,var,lr]
    have line (l : Fin N) : selected (baseline false) (pick false j) (onSet U) (right l)=decide (l=j) := by
      simp [selected,baseline,pick,const]
    constructor
    · simpa [Fintype.card_subtype,line] using hq
    · rintro ⟨p,l,pr,px,lx⟩
      rw [line] at lx; obtain rfl := of_decide_eq_true lx
      exact disjoint_left.mp dis (of_decide_eq_true ((mem p).symm.trans px)) (by simpa [rowSet] using pr)

/-- Every single legal negative test chosen for a row enforces q OR gates
that separate two positive inputs in opposite directions and stay false
on that negative. This is pointwise in the choice of the negative test. -/
theorem distinct_merges (q : ℕ) (hq : 1≤q) (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (P : Prog (N+N))
    (pos : ∀ p l,I p l → P.eval (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N→Bool,Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l,I p l ∧ x (left p)=true ∧ x (right l)=true) → P.eval x=false)
    (side : Bool) (U : Fin N→Finset (Fin N)) (size : side=true → ∀ j,(U j).card≤q)
    (dis : ∀ j,Disjoint (U j) (rowSet side I j)) (j : Fin N) :
    q≤count P (profile I side U j) := by
  let w := profile I side U j
  have ok := legal_profile q hq I side j (U j) (fun h => size h j) (dis j)
  have off : (run P w).neg=false := (truth P w).1.trans (neg _ ok.1 ok.2)
  have covered : rowSet side I j ⊆ (run P w).acc := by
    intro v hv
    apply ((truth P w).2 v).mpr
    have e : (fun i => decide (v∈(w i).acc))=selected (baseline side) (pick side j) (onSet {v}) := by
      funext i; simp [w,profile,hv]
    rw [e,singleton_selected]
    cases side <;> simp only [Bool.false_eq_true,↓reduceIte]
    · exact pos v j (by simpa [rowSet] using hv)
    · exact pos j v (by simpa [rowSet] using hv)
  have cost := budget P w off (atom I side U j)
  have entries := card_le_card covered
  rw [(row_geometry I ord hd hj side).1] at entries
  change q≤count P w
  omega

/-- The same gate can serve several rows, but every permitted family of
negative inputs must have Nq gate-row memberships. -/
theorem desk_merge_roles {q N : ℕ} (I : Fin N→Fin N→Prop) [DecidableRel I] (C : Circuit)
    (hq : 1≤q) (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l)
    (hm : Monotone2 C) (out : C.output<N+N+C.size) (norm : Normal (N+N) C)
    (pos : ∀ p l,I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N→Bool,Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l,I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false) :
    ∃ P,decode (N+N) C.gates C.output=some P ∧ P.size=C.size ∧
      ∀ (side : Bool) (U : Fin N→Finset (Fin N)), (side=true → ∀ j,(U j).card≤q) →
      (∀ j,Disjoint (U j) (rowSet side I j)) →
      let R := roles P (profile I side U)
      N*q≤(R.map Finset.card).sum ∧ ∀ c, N*q≤c*C.size+N*(R.filter (fun D => decide (c<D.card))).length := by
  obtain ⟨P,par,len,ev⟩ := parse_desk C norm hm out
  refine ⟨P,par,len,?_⟩
  intro side U sz dis
  have count := Finset.sum_le_sum (s:=univ) (fun j _ => distinct_merges q hq I ord hd hj P
    (fun p l hp => (ev _).trans (pos p l hp)) (fun x hs hn => (ev x).trans (neg x hs hn)) side U sz dis j)
  rw [←roles_total] at count
  simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at count
  exact ⟨count,fun c => count.trans (by simpa [len] using threshold (roles P (profile I side U)) c)⟩

end GateElim.Plane
#print axioms GateElim.Plane.desk_merge_roles
