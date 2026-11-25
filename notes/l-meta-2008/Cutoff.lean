import PlaneCore

namespace GateElim.Plane
open Desk2008 Desk2008.Fanout PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private def n (q : ℕ) := q^2+q+1
private def t (q : ℕ) := (n q+9)/10
private def cap (q : ℕ) := (9*n q*q + (q-9)^2-1)/(q-9)^2
private def steps (q : ℕ) := n q-t q-cap q
private def valid (q : ℕ) : Prop :=
  n q≤10*t q ∧ steps q+t q+cap q≤n q ∧ cap q≤t q ∧ 2≤t q ∧
  9*n q*q≤cap q*(q+1-10)^2 ∧
  3*(n q*q)+100*(1+4*(cap q+q+3))≤100*(8*n q+2*steps q)
private instance (q : ℕ) : Decidable (valid q) := by unfold valid; infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem numeric : ∀ i : Fin 54, valid (267+i.val) := by decide +kernel

theorem through_320 (q : ℕ) (h : 100<q) (lim : q≤320) : TargetAt q := by
  intro N I inst C ord hd join hm out norm pos neg
  by_cases low : q≤266
  · exact through_266 q N I C h ord hd join hm out norm pos neg low
  have eq : 267+(q-267)=q := by omega
  have hs := numeric ⟨q-267,by omega⟩
  change valid (267+(q-267)) at hs
  rw [eq] at hs
  obtain ⟨d,r,res,tp,num,win⟩ := hs
  have ord' : N=n q := ord
  rw [←ord'] at d r num win
  have bound := core_bound I C ord hd join hm out norm (desk_fits I C hm q (by omega) pos neg)
    d r res tp (by decide) (by omega) (by omega) num
  omega

theorem residual_iff_320 : Desk2008.Posted ↔ ∀ q, 320<q → TargetAt q := by
  rw [Desk2008.Fanout.residual_iff]
  constructor
  · intro h q hq; exact h q (by omega)
  · intro h q hq
    by_cases low : q≤320
    · exact through_320 q (by omega) low
    · exact h q (by omega)

end GateElim.Plane
#print axioms GateElim.Plane.through_320
#print axioms GateElim.Plane.residual_iff_320
