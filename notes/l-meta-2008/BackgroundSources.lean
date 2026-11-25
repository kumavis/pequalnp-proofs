import MixedSources
import PlaneOrdered

namespace GateElim.Plane
open Desk2008 Desk2008.Fanout PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Reverse Block Cuts Products Rows Finset Classical
attribute [-simp] Fin.natAdd_eq_addNat
variable {N q : ℕ}

structure Background (I : Fin N→Fin N→Prop) where
  points : Finset (Fin N)
  lines : Finset (Fin N)
  independent : ∀ p∈points,∀ l∈lines,¬I p l

namespace Background
variable {I : Fin N→Fin N→Prop} [DecidableRel I]

def ptsOK (B : Background I) := univ.filter fun p => ∀ l∈B.lines,¬I p l
def lnsOK (B : Background I) := univ.filter fun l => ∀ p∈B.points,¬I p l
noncomputable def extend (B : Background I) (X Y : Finset (Fin N)) :=
  box (B.points∪(X∩B.ptsOK)) (B.lines∪(Y∩B.lnsOK))

def active (fixed allowed : Finset (Fin N)) (i : Fin N) : Fn (Fin N) :=
  if i∈fixed then const true else if i∈allowed then var i else const false
def px (B : Background I) : SideFn N (N+N) :=
  Fin.addCases (active B.points B.ptsOK) (fun l => const (decide (l∈B.lines)))
def ly (B : Background I) : SideFn N (N+N) :=
  Fin.addCases (fun p => const (decide (p∈B.points))) (active B.lines B.lnsOK)

theorem basic (B : Background I) (i : Vertex N) : B.px i∈base univ ∧ B.ly i∈base univ := by
  have known (b : Bool) : const (V:=Fin N) b∈base univ := Or.inl ⟨b,rfl⟩
  have sel (s t : Finset (Fin N)) (i : Fin N) : active s t i∈base univ := by
    unfold active; split
    · exact known _
    · split
      · exact Or.inr ⟨i,mem_univ _,rfl⟩
      · exact known _
  cases i using Fin.addCases <;> simpa [px,ly,sel,known]

theorem pureX (B : Background I) (X : Finset (Fin N)) :
    (fun i => B.px i (onSet X))=bits (B.extend X ∅) := by
  funext i; cases i using Fin.addCases with
  | left p =>
    by_cases h : p∈B.points <;> by_cases a : p∈B.ptsOK <;> simp [px,active,extend,bits,onSet,var,const,h,a]
  | right l => simp [px,extend,bits,const]
theorem pureY (B : Background I) (Y : Finset (Fin N)) :
    (fun i => B.ly i (onSet Y))=bits (B.extend ∅ Y) := by
  funext i; cases i using Fin.addCases with
  | left p => simp [ly,extend,bits,const]
  | right l =>
    by_cases h : l∈B.lines <;> by_cases a : l∈B.lnsOK <;> simp [ly,active,extend,bits,onSet,var,const,h,a]

theorem legal (B : Background I) (X Y : Finset (Fin N)) (sz : B.lines.card+Y.card≤q)
    (off : ¬∃ p∈X,∃ l∈Y,I p l) :
    (lns (B.extend X Y)).card≤q ∧ ¬EdgeIn (adj I) (B.extend X Y) := by
  constructor
  · simp only [extend,lns_box]
    have small := card_le_card (inter_subset_left (s₁:=Y) (s₂:=B.lnsOK))
    exact (card_union_le ..).trans (by omega)
  · intro e; obtain ⟨p,hp,l,hl,inc⟩ := (edge_iff I _).mp e
    rcases mem_union.mp ((in_left ..).mp hp) with bg|new <;>
      rcases mem_union.mp ((in_right ..).mp hl) with old|added
    · exact B.independent p bg l old inc
    · exact (mem_filter.mp (mem_inter.mp added).2).2 p bg inc
    · exact (mem_filter.mp (mem_inter.mp new).2).2 l old inc
    · exact off ⟨p,(mem_inter.mp new).1,l,(mem_inter.mp added).1,inc⟩

theorem rises (B : Background I) (p l : Fin N) (hp : p∈B.ptsOK) (hl : l∈B.lnsOK) (inc : I p l) :
    EdgeIn (adj I) (B.extend {p} {l}) := (edge_iff I _).mpr
      ⟨p,(in_left ..).mpr (mem_union_right _ (mem_inter.mpr ⟨mem_singleton_self _,hp⟩)),
       l,(in_right ..).mpr (mem_union_right _ (mem_inter.mpr ⟨mem_singleton_self _,hl⟩)),inc⟩

theorem raw_cover (B : Background I) (p l : Fin N) (i : Vertex N) :
    bits (B.extend {p} {l}) i=true → B.px i (onSet {p})=true ∨ B.ly i (onSet {l})=true := by
  have a := congrFun (pureX B {p}) i; have b := congrFun (pureY B {l}) i
  change B.px i (onSet {p})=_ at a; change B.ly i (onSet {l})=_ at b
  rw [a,b]
  cases i using Fin.addCases <;> simp [extend,bits] <;> tauto

end Background

/-- The source obstruction works after any independent background choice
that leaves room for t more lines. Every spurious source has an actual
negative of the original desk circuit even after the background is added. -/
theorem desk_background_sources {q N : ℕ} (I : Fin N→Fin N→Prop) [DecidableRel I] (C : Circuit)
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l)
    (hm : Monotone2 C) (out : C.output<N+N+C.size) (norm : Normal (N+N) C)
    (pos : ∀ p l,I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N→Bool,Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l,I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false) :
    ∃ P,decode (N+N) C.gates C.output=some P ∧ ∀ (B : Background I) (t : ℕ),
      1≤t → B.lines.card+t≤q →
      (t+1)*(∑ p,(edgesAt I t P B.px B.ly p).card)≤(q+1)*(6*C.size+2*N) ∧
      ∀ p∈B.ptsOK,∀ l∈B.lnsOK,I p l →
        (∃ g∈sources P B.px B.ly,g.1 (onSet {p})=true ∧ g.2 (onSet {l})=true) ∧
        (l∉edgesAt I t P B.px B.ly p →
          ∀ g∈sources P B.px B.ly,g.1 (onSet {p})=true → g.2 (onSet {l})=true →
            ∃ X Y : Finset (Fin N),X.card≤t ∧ Y.card≤t ∧ (X.card=1 ∨ Y.card=1) ∧
              g.1 (onSet X)=true ∧ g.2 (onSet Y)=true ∧
              (lns (B.extend X Y)).card≤q ∧ ¬EdgeIn (adj I) (B.extend X Y) ∧
              circuitFun (N+N) C (bits (B.extend X Y))=false) := by
  classical
  obtain ⟨P,par,len,ev⟩ := parse_desk C norm hm out
  have correct := desk_correct q I C hm pos neg
  refine ⟨P,par,?_⟩
  intro B t ht left
  have cost := coverage_at q t ht (by omega) I ord hd hj P B.px B.ly (fun i => (B.basic i).1) (fun i => (B.basic i).2)
  refine ⟨by simpa [len] using cost,?_⟩
  intro p hp l hl inc
  constructor
  · by_contra! miss
    have okX := B.legal {p} ∅ (q:=q) (by simp; omega) (by simp)
    have okY := B.legal ∅ {l} (q:=q) (by simp; omega) (by simp)
    have nx : Block.val P B.px (onSet {p})=false := by
      unfold Block.val; rw [B.pureX,ev]; exact correct.no _ (subset_univ _) okX.1 okX.2
    have ny : Block.val P B.ly (onSet {l})=false := by
      unfold Block.val; rw [B.pureY,ev]; exact correct.no _ (subset_univ _) okY.1 okY.2
    have yes := (ev _).trans (correct.yes _ (subset_univ _) (B.rises p l hp hl inc))
    have alt := first_source P B.px B.ly (onSet {p}) (onSet {l}) _ (B.raw_cover p l)
      (fun g h both => miss g h both.1 both.2) yes
    simp [nx,ny] at alt
  · intro miss g member xp yl
    obtain ⟨X,Y,xs,ys,one,xg,yg,off⟩ := bad_at I t P B.px B.ly p l miss g member xp yl
    obtain ⟨small,free⟩ := B.legal X Y (q:=q) (by omega) off
    exact ⟨X,Y,xs,ys,one,xg,yg,small,free,correct.no _ (subset_univ _) small free⟩

end GateElim.Plane
#print axioms GateElim.Plane.desk_background_sources
