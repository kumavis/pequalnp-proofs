import SourceFraction

namespace GateElim.Plane
open Desk2008 Reverse Cuts Block Rows Products Finset Classical
variable {q N : ℕ}

/-- A single physical position can witness this edge on every admissible
one-sided background that leaves the endpoints available. -/
def persistent (I : Fin N→Fin N→Prop) [DecidableRel I] (q : ℕ) (P : Prog (N+N)) (p l : Fin N) :=
  ∃ i : ℕ, ∀ B : Background I,
    ((B.points=∅ ∧ B.lines.card≤q-1) ∨ (B.lines=∅ ∧ B.points.card≤q-1)) →
    p∈B.ptsOK → l∈B.lnsOK →
    ∃ g∈births P 0 B.px B.ly,g.index=i ∧ g.fires (onSet {p}) (onSet {l})

noncomputable def persistentEdges (I : Fin N→Fin N→Prop) [DecidableRel I] (q : ℕ) (P : Prog (N+N)) (p : Fin N) :=
  (rowSet true I p).filter (fun l => persistent I q P p l)

theorem persistent_budget (q : ℕ) (hq : 2≤q) (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (P : Prog (N+N)) :
    q*(∑ p,(persistentEdges I q P p).card)≤(q+1)*(6*P.size+2*N) := by
  classical
  let B := emptyBackground I
  have sub (p : Fin N) : persistentEdges I q P p⊆endpointRows I (q-1) P B.px B.ly p := by
    intro l member; obtain ⟨i,works⟩ := (mem_filter.mp member).2
    have px : p∈B.ptsOK := by simp [B,emptyBackground,Background.ptsOK]
    have ly : l∈B.lnsOK := by simp [B,emptyBackground,Background.lnsOK]
    obtain ⟨g,mem,index,fire⟩ := works B (by simp [B,emptyBackground]) px ly
    by_contra miss
    obtain ⟨C,_,_,hp,hl,cap,active⟩ := B.disable_source (q-1) P p l px ly miss g mem fire
    obtain ⟨k,km,ki,kf⟩ := works C (by simpa [B,emptyBackground] using cap) hp hl
    have off := separate_off P 0 C.px C.ly k km (onSet {p}) (onSet {l}) kf
    rw [index,←ki] at active
    rcases active with a|a <;> simp [a] at off
  have bound := endpoint_cost q (q-1) (by omega) (by omega) I ord hd hj P B.px B.ly (fun i => (B.basic i).1) (fun i => (B.basic i).2)
  rw [show q-1+1=q by omega] at bound
  exact (Nat.mul_le_mul_left q (sum_le_sum (s:=univ) (fun p _ => card_le_card (sub p)))).trans bound

theorem all_persistent (q : ℕ) (hq : 2≤q) (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (P : Prog (N+N))
    (all : ∀ p l,I p l → persistent I q P p l) : N*q≤6*P.size+2*N := by
  have eq (p : Fin N) : persistentEdges I q P p=rowSet true I p := by
    apply filter_true_of_mem; intro l h; exact all p l (by simpa [rowSet] using h)
  have b := persistent_budget q hq I ord hd hj P
  simp_rw [eq,(row_geometry I ord hd hj true).1] at b
  simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at b
  have start : (q+1)*(N*q)≤(q+1)*(6*P.size+2*N) := by convert b using 1 <;> ring
  exact Nat.le_of_mul_le_mul_left start (by omega)

end GateElim.Plane
#print axioms GateElim.Plane.persistent_budget
#print axioms GateElim.Plane.all_persistent
