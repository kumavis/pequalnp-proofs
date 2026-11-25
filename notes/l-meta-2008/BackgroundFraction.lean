import ResidualPairs

namespace GateElim.Plane.Background
open Desk2008 Reverse Cuts Block Products Rows Finset Classical
variable {N q : ℕ} {I : Fin N→Fin N→Prop} [DecidableRel I]

/-- With a background using together at most q/10 points and lines, more
than 82 percent of *all original incidences* remain both available and
unprotected. The same bound holds for every such background. -/
theorem dense_exposed (B : Background I) (P : Prog (N+N)) (large : 200≤q)
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (small : 100*P.size<N*q)
    (used : 10*(B.points.card+B.lines.card)≤q) :
    let t := q-B.lines.card-1
    82*(N*(q+1))<100*(∑ p,(B.availableEdges p\endpointRows I t P B.px B.ly p).card) := by
  let t := q-B.lines.card-1
  let E := N*(q+1)
  let m := ∑ p,(endpointRows I t P B.px B.ly p).card
  let live := ∑ p,(B.availableEdges p).card
  let newE := ∑ p,(B.availableEdges p\endpointRows I t P B.px B.ly p).card
  have ht : 1≤t := by dsimp [t]; omega
  have eq : t+1+B.lines.card=q := by dsimp [t]; omega
  have bound := endpoint_cost q t ht (by omega) I ord hd hj P B.px B.ly (fun i => (B.basic i).1) (fun i => (B.basic i).2)
  change (t+1)*m≤_ at bound
  have balance : 100*(6*P.size+2*N)<8*(N*(t+1)) := by
    have enough : 6*q+200≤8*(t+1) := by omega
    have room := Nat.mul_le_mul_left N enough
    nlinarith only [room,small]
  have l := Nat.mul_le_mul_left 100 bound
  have r := Nat.mul_lt_mul_of_pos_left balance (show 0<q+1 by omega)
  have few : 100*m<8*E := by
    apply Nat.lt_of_mul_lt_mul_left (a:=t+1)
    dsimp [E]; nlinarith only [l,r]
  have keep := survives_count B ord hd hj
  change E≤live+(B.points.card+B.lines.card)*(q+1)^2 at keep
  have budgeted := Nat.mul_le_mul_right ((q+1)^2) used
  have geom : q*(q+1)^2≤E := by dsimp [E]; rw [ord]; nlinarith
  have missing : 10*((B.points.card+B.lines.card)*(q+1)^2)≤E := by
    rw [←Nat.mul_assoc]; exact budgeted.trans geom
  have per (p : Fin N) : (B.availableEdges p).card≤(B.availableEdges p\endpointRows I t P B.px B.ly p).card+
      (endpointRows I t P B.px B.ly p).card := by
    have h := card_sdiff_add_card_inter (B.availableEdges p) (endpointRows I t P B.px B.ly p)
    have k := card_le_card (inter_subset_right (s₁:=B.availableEdges p) (s₂:=endpointRows I t P B.px B.ly p))
    omega
  have split := sum_le_sum (s:=univ) (fun p _ => per p)
  rw [sum_add_distrib] at split
  change live≤newE+m at split
  change 82*E<100*newE
  omega

end GateElim.Plane.Background
#print axioms GateElim.Plane.Background.dense_exposed
