import TriangularBound

namespace GateElim.Plane
open Desk2008 Desk2008.Fanout

theorem through_365 (q : ℕ) (hq : 100<q) (lim : q≤365) : TargetAt q := by
  intro N I inst C ord hd hj hm out norm pos neg
  have h := clean_bound I C (by omega) ord hd hj hm out norm pos neg
  by_cases large : 361≤q
  · have area := Nat.mul_le_mul_right q large
    have room : 1800*q+700≤5*N := by nlinarith
    have le := Nat.mul_le_mul_left N lim
    omega
  · have area := Nat.mul_le_mul_right q (show 101≤q by omega)
    have room : 1800*q+700≤20*N := by nlinarith
    have le := Nat.mul_le_mul_left N (show q≤360 by omega)
    omega

theorem residual_iff_365 : Desk2008.Posted ↔ ∀ q, 365<q → TargetAt q := by
  rw [Desk2008.Fanout.residual_iff]
  constructor
  · intro h q hq; exact h q (by omega)
  · intro h q hq
    by_cases low : q≤365
    · exact through_365 q (by omega) low
    · exact h q (by omega)

end GateElim.Plane
#print axioms GateElim.Plane.through_365
#print axioms GateElim.Plane.residual_iff_365
