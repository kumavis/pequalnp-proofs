import SoundProducts
import ProductSources

namespace GateElim.Plane
open Desk2008 Desk2008.Fanout PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Reverse Block Cuts Rows Products Finset Classical
attribute [-simp] Fin.natAdd_eq_addNat
variable {q N : ℕ}

def rawProducts (P : Prog (N+N)) := sources P (baseline false) (baseline true)
noncomputable def cleanProducts (I : Fin N→Fin N→Prop) (q : ℕ) (P : Prog (N+N)) :=
  (rawProducts P).toFinset.filter fun g => sound I q g.1 g.2
noncomputable def cleanEdges (I : Fin N→Fin N→Prop) (q : ℕ) (P : Prog (N+N)) (p : Fin N) :=
  edges (fun g : ↥(cleanProducts I q P) => g.val.1) (fun g => g.val.2) p

theorem clean_coverage (q : ℕ) (hq : 1≤q) (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (P : Prog (N+N)) :
    (∑ p,(cleanEdges I q P p).card)≤6*P.size+2*N := by
  classical
  let A := cleanProducts I q P
  obtain ⟨gs,hs,gl,hl,gb,hb,ready⟩ := banks P (baseline false) (baseline true) (base univ) (base univ)
    (base_legal false) (base_legal true)
  have mem (g : A) : g.val∈rawProducts P := List.mem_toFinset.mp (mem_filter.mp g.property).1
  have h := sound_product_bound q hq I ord hd hj (fun g : A => g.val.1) (fun g => g.val.2)
    (fun g => (mem_filter.mp g.property).2) gs hs gb hb (fun g => (ready g.val (mem g)).1)
    (fun g => (ready g.val (mem g)).2)
  have small : A.card≤(rawProducts P).length := (card_filter_le (rawProducts P).toFinset (fun r => sound I q r.1 r.2)).trans (List.toFinset_card_le (rawProducts P))
  have length := sources_len P (baseline false) (baseline true)
  change (rawProducts P).length≤2*P.size at length
  have cap : A.card≤2*P.size := (show A.card≤(rawProducts P).length from small).trans length
  change (∑ p,(cleanEdges I q P p).card)≤gs.length+hs.length+2*Fintype.card A+2*N at h
  simp only [Fintype.card_coe,gl,hl] at h; omega

private theorem pair_source (P : Prog (N+N)) (p l : Fin N)
    (pos : P.eval (fun i => decide (i=left p ∨ i=right l))=true)
    (noX : P.eval (fun i => baseline false i (onSet {p}))=false)
    (noY : P.eval (fun i => baseline true i (onSet {l}))=false) :
    ∃ r∈rawProducts P,r.1 (onSet {p})=true ∧ r.2 (onSet {l})=true := by
  by_contra! miss
  have start (i : Vertex N) (h : decide (i=left p ∨ i=right l)=true) :
      baseline false i (onSet {p})=true ∨ baseline true i (onSet {l})=true := by
    rcases of_decide_eq_true h with rfl|rfl <;> simp [baseline,onSet,var]
  have alt := first_source P (baseline false) (baseline true) (onSet {p}) (onSet {l}) _ start
    (fun r hr both => miss r hr both.1 both.2) pos
  simpa [Block.val,noX,noY] using alt

/-- Every source witnessing an edge outside the covered set fires on some
legal negative with at most q bits on either side and one singleton side. -/
theorem desk_sources {q N : ℕ} (I : Fin N→Fin N→Prop) [DecidableRel I] (C : Circuit)
    (hq : 1≤q) (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l)
    (hm : Monotone2 C) (out : C.output<N+N+C.size) (norm : Normal (N+N) C)
    (pos : ∀ p l,I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N→Bool,Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l,I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false) :
    ∃ P,decode (N+N) C.gates C.output=some P ∧ (∑ p,(cleanEdges I q P p).card)≤6*C.size+2*N ∧
      ∀ p l,I p l →
      (∃ r∈rawProducts P,r.1 (onSet {p})=true ∧ r.2 (onSet {l})=true) ∧
      (l∉cleanEdges I q P p → ∀ r∈rawProducts P,r.1 (onSet {p})=true → r.2 (onSet {l})=true →
        ∃ X Y : Finset (Fin N),X.card≤q ∧ Y.card≤q ∧ (X.card=1 ∨ Y.card=1) ∧
          r.1 (onSet X)=true ∧ r.2 (onSet Y)=true ∧ ¬∃ p∈X,∃ l∈Y,I p l) := by
  classical
  obtain ⟨P,par,len,ev⟩ := parse_desk C norm hm out
  refine ⟨P,par,by simpa [len] using clean_coverage q hq I ord hd hj P,?_⟩
  intro p l inc
  constructor
  · apply pair_source P p l ((ev _).trans (pos p l inc))
    all_goals rw [ev]; apply neg
    all_goals simp [Fintype.card_subtype,baseline,onSet,var,const,left,right,hq]
  · intro miss r hr xp yl
    have bad : ¬sound I q r.1 r.2 := by
      intro good
      have member : r∈cleanProducts I q P := mem_filter.mpr ⟨List.mem_toFinset.mpr hr,good⟩
      apply miss
      exact mem_filter.mpr ⟨mem_univ _,⟨r,member⟩,mem_filter.mpr ⟨mem_univ _,xp⟩,mem_filter.mpr ⟨mem_univ _,yl⟩⟩
    unfold sound at bad
    push Not at bad ⊢
    exact bad

end GateElim.Plane
#print axioms GateElim.Plane.desk_sources
