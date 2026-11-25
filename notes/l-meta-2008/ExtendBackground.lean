import EndpointSources

namespace GateElim.Plane.Background
open Desk2008 Reverse Cuts Products Rows Block Finset Classical
attribute [-simp] Fin.natAdd_eq_addNat
variable {N : ℕ} {I : Fin N→Fin N→Prop} [DecidableRel I]

def addL (B : Background I) (Y : Finset (Fin N)) : Background I :=
  ⟨B.points,B.lines∪(Y∩B.lnsOK),by
    intro p hp l hl
    rcases mem_union.mp hl with old|new
    · exact B.independent p hp l old
    · exact (mem_filter.mp (mem_inter.mp new).2).2 p hp⟩
def addP (B : Background I) (X : Finset (Fin N)) : Background I :=
  ⟨B.points∪(X∩B.ptsOK),B.lines,by
    intro p hp l hl
    rcases mem_union.mp hp with old|new
    · exact B.independent p old l hl
    · exact (mem_filter.mp (mem_inter.mp new).2).2 l hl⟩

private theorem box_mono {A A' L L' : Finset (Fin N)} (a : A⊆A') (b : L⊆L') :
    box A L⊆box A' L' := by
  intro i h; cases i using Fin.addCases with
  | left p => exact (in_left ..).mpr (a ((in_left ..).mp h))
  | right l => exact (in_right ..).mpr (b ((in_right ..).mp h))

private theorem le_bits (A B : Finset (Vertex N)) (s : A⊆B) (i : Vertex N) :
    bits A i=true → bits B i=true := fun h => decide_eq_true (s (of_decide_eq_true h))

private theorem point_stays (B : Background I) (p : Fin N) {Y : Finset (Fin N)} (hp : p∈B.ptsOK)
    (avoid : Disjoint Y (rowSet true I p)) : p∈(B.addL Y).ptsOK := by
  apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩
  intro l hl inc; rcases mem_union.mp hl with old|new
  · exact (mem_filter.mp hp).2 l old inc
  · exact disjoint_left.mp avoid (mem_inter.mp new).1 (by simpa [rowSet] using inc)
private theorem line_stays (B : Background I) (l : Fin N) {X : Finset (Fin N)} (hl : l∈B.lnsOK)
    (avoid : Disjoint X (rowSet false I l)) : l∈(B.addP X).lnsOK := by
  apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩
  intro p hp inc; rcases mem_union.mp hp with old|new
  · exact (mem_filter.mp hl).2 p old inc
  · exact disjoint_left.mp avoid (mem_inter.mp new).1 (by simpa [rowSet] using inc)

/-- For an unprotected surviving edge and *each* genuine source for it, a
one-sided enlargement keeps the edge available and turns on this very gate
with only one endpoint added. A second genuine source must have a different
physical index on that background. -/
theorem disable_source (B : Background I) (t : ℕ) (P : Prog (N+N)) (p l : Fin N)
    (hp : p∈B.ptsOK) (hl : l∈B.lnsOK) (miss : l∉endpointRows I t P B.px B.ly p)
    (g : Birth (Fin N)) (mem : g∈births P 0 B.px B.ly) (fire : g.fires (onSet {p}) (onSet {l})) :
    ∃ C : Background I, B.points⊆C.points ∧ B.lines⊆C.lines ∧ p∈C.ptsOK ∧ l∈C.lnsOK ∧
      ((C.points=B.points ∧ C.lines.card≤B.lines.card+t) ∨ (C.lines=B.lines ∧ C.points.card≤B.points.card+t)) ∧
      (atGate P 0 (fun i => C.px i (onSet {p})) g.index=some true ∨
       atGate P 0 (fun i => C.ly i (onSet {l})) g.index=some true) := by
  obtain ⟨Y,avoid,small,win⟩|⟨X,avoid,small,win⟩ := one_sided_witness I t P B.px B.ly p l miss g mem fire
  · let C := B.addL Y
    have stay := point_stays B p hp avoid
    have fixed : C.extend {p} ∅=box (insert p B.points) (B.lines∪(Y∩B.lnsOK)) := by
      simp only [extend,singleton_inter_of_mem (show p∈C.ptsOK from stay),empty_inter,union_empty,union_singleton]; rfl
    have before : B.extend {p} ∅⊆C.extend {p} ∅ := by
      rw [fixed]; simp only [extend,empty_inter,union_empty,singleton_inter_of_mem hp,union_singleton]
      exact box_mono Subset.rfl subset_union_left
    have other : B.extend ∅ Y⊆C.extend {p} ∅ := by
      rw [fixed]; simp only [extend,empty_inter,union_empty]; exact box_mono (subset_insert ..) Subset.rfl
    refine ⟨C,Subset.rfl,subset_union_left,stay,hl,Or.inl ⟨rfl,?_⟩,Or.inl ?_⟩
    · exact (card_union_le ..).trans (Nat.add_le_add_left ((card_le_card inter_subset_left).trans small) _)
    · have h := activates P 0 B.px B.ly g mem (onSet {p}) (onSet Y) (bits (C.extend {p} ∅))
        (fun i h => le_bits _ _ before i (by rwa [←B.pureX])) (fun i h => le_bits _ _ other i (by rwa [←B.pureY])) fire.1 win
      simpa only [C.pureX] using h
  · let C := B.addP X
    have stay := line_stays B l hl avoid
    have fixed : C.extend ∅ {l}=box (B.points∪(X∩B.ptsOK)) (insert l B.lines) := by
      simp only [extend,singleton_inter_of_mem (show l∈C.lnsOK from stay),empty_inter,union_empty,union_singleton]; rfl
    have before : B.extend ∅ {l}⊆C.extend ∅ {l} := by
      rw [fixed]; simp only [extend,empty_inter,union_empty,singleton_inter_of_mem hl,union_singleton]
      exact box_mono subset_union_left Subset.rfl
    have other : B.extend X ∅⊆C.extend ∅ {l} := by
      rw [fixed]; simp only [extend,empty_inter,union_empty]; exact box_mono Subset.rfl (subset_insert ..)
    refine ⟨C,subset_union_left,Subset.rfl,hp,stay,Or.inr ⟨rfl,?_⟩,Or.inr ?_⟩
    · exact (card_union_le ..).trans (Nat.add_le_add_left ((card_le_card inter_subset_left).trans small) _)
    · have h := activates P 0 B.px B.ly g mem (onSet X) (onSet {l}) (bits (C.extend ∅ {l}))
        (fun i h => le_bits _ _ other i (by rwa [←B.pureX])) (fun i h => le_bits _ _ before i (by rwa [←B.pureY])) win fire.2.1
      simpa only [C.pureY] using h

end GateElim.Plane.Background
#print axioms GateElim.Plane.Background.disable_source
