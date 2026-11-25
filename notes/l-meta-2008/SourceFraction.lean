import FreshSources

namespace GateElim.Plane
open Desk2008 Desk2008.Fanout PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Reverse Block Cuts Products Rows Finset Classical
variable {q N : ℕ}

def emptyBackground (I : Fin N→Fin N→Prop) : Background I := ⟨∅,∅,by simp⟩

/-- The seven percent estimate uses the budget for t=q−1, leaving a spare
line for the same-edge replacement guaranteed by fresh_source. -/
private theorem percent (N q s m : ℕ) (large : 200≤q) (small : 100*s<N*q)
    (bound : q*m≤(q+1)*(6*s+2*N)) : 100*m<7*(N*(q+1)) := by
  have pos : 0<q+1 := by omega
  have cost : 100*(6*s+2*N)<7*(N*q) := by
    have room := Nat.mul_le_mul_left N large
    omega
  have mul := Nat.mul_lt_mul_of_pos_left cost pos
  have lo := Nat.mul_le_mul_left 100 bound
  have res : q*(100*m)<q*(7*(N*(q+1))) := by nlinarith only [mul,lo]
  exact Nat.lt_of_mul_lt_mul_left res

noncomputable def exposedPairs (P : Prog (N+N)) (I : Fin N→Fin N→Prop) [DecidableRel I] (q : ℕ) (p : Fin N) :=
  let B := emptyBackground I
  rowSet true I p \ endpointRows I (q-1) P B.px B.ly p

/-- More than 93 percent of all incident pairs in any undersized circuit
admit permanent exclusion of *each* possible physical first source. The
new background and the exclusions may differ between pairs and gates. -/
theorem desk_ninety_three {q N : ℕ} (I : Fin N→Fin N→Prop) [DecidableRel I] (C : Circuit)
    (large : 200≤q) (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l)
    (hm : Monotone2 C) (out : C.output<N+N+C.size) (norm : Normal (N+N) C)
    (pos : ∀ p l,I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N→Bool,Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l,I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false)
    (small : 100*C.size<N*q) :
    ∃ P, decode (N+N) C.gates C.output=some P ∧ 93*(N*(q+1))<100*(∑ p,(exposedPairs P I q p).card) ∧
      ∀ p l,l∈exposedPairs P I q p →
        let B := emptyBackground I
        (∃ g∈births P 0 B.px B.ly,g.fires (onSet {p}) (onSet {l})) ∧
        ∀ g∈births P 0 B.px B.ly,g.fires (onSet {p}) (onSet {l}) →
          ∃ D : Background I, p∈D.ptsOK ∧ l∈D.lnsOK ∧
            ((D.points=∅ ∧ D.lines.card≤q-1) ∨ (D.lines=∅ ∧ D.points.card≤q-1)) ∧
            (∃ k∈births P 0 D.px D.ly,k.fires (onSet {p}) (onSet {l})) ∧
            ∀ H : Background I,D.points⊆H.points → D.lines⊆H.lines → p∈H.ptsOK → l∈H.lnsOK →
              ∀ k∈births P 0 H.px H.ly,k.fires (onSet {p}) (onSet {l}) → g.index≠k.index := by
  classical
  obtain ⟨P,par,len,ev⟩ := parse_desk C norm hm out
  let B := emptyBackground I
  let t := q-1
  have t1 : 1≤t := by dsimp [t]; omega
  have succ : t+1=q := by dsimp [t]; omega
  have room : B.lines.card+t+1≤q := by simpa [B,emptyBackground] using succ.le
  have ok := desk_correct q I C hm pos neg
  have good := fun S h => (ev _).trans (ok.yes S (subset_univ _) h)
  have bad := fun S hs h => (ev _).trans (ok.no S (subset_univ _) hs h)
  have count := endpoint_cost q t t1 (by omega) I ord hd hj P B.px B.ly (fun i => (B.basic i).1) (fun i => (B.basic i).2)
  rw [succ,len] at count
  have few := percent N q C.size _ large small count
  have part (p : Fin N) : q+1≤(exposedPairs P I q p).card+(endpointRows I t P B.px B.ly p).card := by
    have eq := card_sdiff_add_card_inter (rowSet true I p) (endpointRows I t P B.px B.ly p)
    have sub := card_le_card (inter_subset_right (s₁:=rowSet true I p) (s₂:=endpointRows I t P B.px B.ly p))
    rw [(row_geometry I ord hd hj true).1] at eq
    change q+1≤((rowSet true I p)\(endpointRows I t P B.px B.ly p)).card+_
    omega
  have all := sum_le_sum (s:=univ) (fun p _ => part p)
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at all
  refine ⟨P,par,?_,?_⟩
  · simp only [Nat.mul_add,mul_one] at all few ⊢; omega
  intro p l member
  obtain ⟨inc,miss⟩ := mem_sdiff.mp member
  have hp : p∈B.ptsOK := by simp [Background.ptsOK,B,emptyBackground]
  have hl : l∈B.lnsOK := by simp [Background.lnsOK,B,emptyBackground]
  have e : I p l := by simpa [rowSet] using inc
  refine ⟨(residual_births q t t1 I B (by omega) P good bad p l hp hl e).1,?_⟩
  intro g mem fire
  obtain ⟨D,_,_,px,ly,cap,next,new⟩ := Background.fresh_source P B t q room good bad p l hp hl e miss g mem fire
  exact ⟨D,px,ly,by simpa [B,emptyBackground,t] using cap,next,new⟩

end GateElim.Plane
#print axioms GateElim.Plane.desk_ninety_three
