import SourceFraction

namespace GateElim.Plane.Background
open Desk2008 Reverse Cuts Block Products Rows Finset Classical
variable {N q : ℕ} {I : Fin N→Fin N→Prop} [DecidableRel I]

noncomputable def availableEdges (B : Background I) (p : Fin N) :=
  if p∈B.ptsOK then rowSet true I p∩B.lnsOK else ∅

private theorem excluded (B : Background I) (ord : N=q^2+q+1)
    (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1) (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) :
    (univ\B.ptsOK).card≤B.lines.card*(q+1) ∧ (univ\B.lnsOK).card≤B.points.card*(q+1) := by
  have pd := (row_geometry I ord hd hj false).1
  have ld := (row_geometry I ord hd hj true).1
  have subP : univ\B.ptsOK⊆B.lines.biUnion (rowSet false I) := by
    intro p h; have no := (mem_sdiff.mp h).2
    simp [ptsOK] at no; obtain ⟨l,hl,inc⟩ := no
    exact mem_biUnion.mpr ⟨l,hl,by simpa [rowSet] using inc⟩
  have subL : univ\B.lnsOK⊆B.points.biUnion (rowSet true I) := by
    intro l h; have no := (mem_sdiff.mp h).2
    simp [lnsOK] at no; obtain ⟨p,hp,inc⟩ := no
    exact mem_biUnion.mpr ⟨p,hp,by simpa [rowSet] using inc⟩
  exact ⟨(card_le_card subP).trans (card_biUnion_le.trans (by simp [pd])),
    (card_le_card subL).trans (card_biUnion_le.trans (by simp [ld]))⟩

/-- Count incidences still present after a background is imposed. -/
theorem survives_count (B : Background I) (ord : N=q^2+q+1)
    (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1) (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) :
    N*(q+1)≤(∑ p,(B.availableEdges p).card)+(B.points.card+B.lines.card)*(q+1)^2 := by
  let dead (p : Fin N) := (rowSet true I p)\B.lnsOK
  let goneP := univ\B.ptsOK
  let goneL := univ\B.lnsOK
  have pd := (row_geometry I ord hd hj true).1
  have ld := (row_geometry I ord hd hj false).1
  have per (p : Fin N) : q+1≤(B.availableEdges p).card+(if p∈goneP then q+1 else 0)+(dead p).card := by
    by_cases live : p∈B.ptsOK
    · have h := card_sdiff_add_card_inter (rowSet true I p) B.lnsOK; rw [pd] at h
      simp [availableEdges,live,goneP,dead,pd] <;> omega
    · simp [availableEdges,live,goneP]
  have swap : ∑ p,(dead p).card=goneL.card*(q+1) := by
    have eq (p : Fin N) : dead p=goneL.filter fun l => p∈rowSet false I l := by ext l; simp [dead,goneL,rowSet]; tauto
    simp only [eq,card_filter]; rw [sum_comm]
    simp [←Finset.card_filter,ld]
  have h := sum_le_sum (s:=univ) (fun p _ => per p)
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,swap] at h
  have sumGone : (∑ p : Fin N,if p∈goneP then q+1 else 0)=goneP.card*(q+1) := by
    simp [←Finset.sum_filter]
  rw [sumGone] at h
  obtain ⟨lp,ll⟩ := excluded B ord hd hj
  have one := Nat.mul_le_mul_right (q+1) lp
  have two := Nat.mul_le_mul_right (q+1) ll
  change goneP.card*(q+1)≤_ at one; change goneL.card*(q+1)≤_ at two
  nlinarith only [h,one,two]

end GateElim.Plane.Background
#print axioms GateElim.Plane.Background.survives_count
