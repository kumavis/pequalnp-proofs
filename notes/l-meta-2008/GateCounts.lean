import ChoiceCNF
import MergeTrace
import Grid

namespace GateElim.Plane
open Desk2008 Desk2008.Fanout PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Reverse ChoiceCNF MergeTrace Finset Classical
attribute [-simp] Fin.natAdd_eq_addNat
variable {q N : ℕ}

theorem count_le_ors {n : ℕ} {A : Type*} [DecidableEq A] (P : Prog n) (w : Fin n→Signal A) :
    count P w≤orCount P := by
  induction P with
  | ret => rfl
  | gate op a b t ih =>
    have h := ih (snoc w (gate op (w a) (w b)))
    cases op with
    | false => simpa [count,orCount,MergeTrace.merge] using h
    | true =>
      change (if MergeTrace.merge true (w a) (w b) then 1 else 0)+_≤orCount t+1
      split <;> omega

theorem exposed (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (S : Finset (Fin N)) (small : S.card≤q)
    (i : Vertex N) (hi : i∈forcedClause I S) : EdgeIn (adj I) (insert i (maximumNegative I S)) := by
  cases i using Fin.addCases with
  | left p =>
    obtain ⟨l,hl,inc⟩ := (mem_filter.mp ((in_left ..).mp hi)).2
    exact (edge_iff I _).mpr ⟨p,mem_insert_self ..,l,mem_insert_of_mem ((in_right ..).mpr hl),inc⟩
  | right l =>
    have absent := (mem_sdiff.mp ((in_right ..).mp hi)).2
    obtain ⟨p,inc,no⟩ := private_point I ord hd hj S small l absent
    exact (edge_iff I _).mpr ⟨p,mem_insert_of_mem ((in_left ..).mpr (mem_sdiff.mpr ⟨mem_univ _,no⟩)),
      l,mem_insert_self ..,inc⟩

theorem clause_or_bound (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (S : Finset (Fin N)) (small : S.card≤q)
    (P : Prog (N+N)) (yes : ∀ X,EdgeIn (adj I) X → P.eval (bits X)=true)
    (no : P.eval (bits (maximumNegative I S))=false) : (forcedClause I S).card≤orCount P+1 := by
  let X := maximumNegative I S
  let F := forcedClause I S
  let w (i : Vertex N) : Signal (Vertex N) := ⟨bits X i,F.filter (fun t => i∈insert t X)⟩
  have off : (run P w).neg=false := (truth P w).1.trans no
  have atom (i : Vertex N) (v : (w i).neg=false) : (w i).acc.card≤1 := by
    have miss : i∉X := by simpa [w,bits] using v
    apply card_le_one.mpr
    intro a ha b hb; have a := (mem_filter.mp ha).2; have b := (mem_filter.mp hb).2; simp_all
  have sub : F⊆(run P w).acc := by
    intro i hi; apply ((truth P w).2 i).mpr
    have e : (fun z => decide (i∈(w z).acc))=bits (insert i X) := by funext z; simp [w,hi,bits]
    rw [e]; exact yes _ (exposed I ord hd hj S small i hi)
  exact (card_le_card sub).trans ((budget P w off atom).trans (Nat.add_le_add_right (count_le_ors P w) 1))

/-- q grid rows cover q² distinct points. A maximal negative therefore has
at least q²+N−q exposed single-bit changes, all charged to OR gates. -/
theorem desk_operator_counts {q N : ℕ} (I : Fin N→Fin N→Prop) [DecidableRel I] (C : Circuit)
    (hq : 2≤q) (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l)
    (hm : Monotone2 C) (out : C.output<N+N+C.size) (norm : Normal (N+N) C)
    (pos : ∀ p l,I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N→Bool,Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l,I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false) :
    ∃ P,decode (N+N) C.gates C.output=some P ∧ C.size=andCount P+orCount P ∧
      2*q^2≤orCount P ∧ (∑ i∈range (q+1),N.choose i)≤2^(andCount P) := by
  obtain ⟨P,par,len,_,capacity⟩ := forced_choices I C ord hd hj hm out norm pos neg
  obtain ⟨P',par',_,ev⟩ := parse_desk C norm hm out
  rw [par] at par'; cases par'
  obtain ⟨g⟩ := plane_grid I hq ord hd hj
  let S := univ.image g.row
  have sz : S.card=q := by simp [S,card_image_of_injective _ g.row_inj]
  have sub : univ.image g.cell ⊆ unionPoints I S := by
    intro p hp; obtain ⟨u,_,rfl⟩ := mem_image.mp hp
    exact mem_filter.mpr ⟨mem_univ _,g.row u.1,mem_image.mpr ⟨_,mem_univ _,rfl⟩,(g.incRow ..).mpr rfl⟩
  have pts := card_le_card sub
  simp only [card_image_of_injective _ g.injective,card_univ,Fintype.card_prod,Fintype.card_fin,←sq] at pts
  have good := desk_correct q I C hm pos neg
  have lower := clause_or_bound I ord hd hj S sz.le P (fun X edge => (ev _).trans (good.yes X (subset_univ _) edge))
    ((ev _).trans (good.no _ (subset_univ _) (by simp [maximumNegative,sz]) (max_negative_valid I S)))
  simp [forcedClause,sz] at lower
  have complement := card_sdiff_add_card_eq_card (subset_univ S)
  simp only [card_univ,Fintype.card_fin,sz] at complement
  exact ⟨P,par,len ▸ ChoiceCNF.split P,by omega,capacity⟩

end GateElim.Plane
#print axioms GateElim.Plane.desk_operator_counts
