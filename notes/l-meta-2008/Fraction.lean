import ResidualDual

namespace GateElim.Plane
open Desk2008.Residual Finset

/-- A bound for arbitrary surviving density, in a form with exact integer
parameters. It applies to adversarial choices of which lines survive. -/
theorem few_at_fraction {q N d K : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (order : N=q^2+q+1) (lineSize : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (join : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (L : Finset (Fin N))
    (density : N≤d*L.card) (dpos : 1≤d) (small : d≤q)
    (target : (d-1)*N*q ≤ K*(q+1-d)^2) :
    (Finset.univ.filter (fun p => degree I L p≤1)).card ≤ K := by
  classical
  let B := Finset.univ.filter (fun p => degree I L p≤1)
  let diff (p : Fin N) : ℤ := (N:ℤ)*degree I L p - (L.card:ℤ)*(q+1)
  have var := variance I order lineSize join L
  change (∑ p, (diff p)^2) ≤ (N:ℤ)*q*L.card*(N-L.card) at var
  have hN : 0<N := by omega
  have hL : 0<L.card := by by_contra! bad; simp [show L.card=0 by omega] at density; omega
  have den : (N:ℤ)≤(d:ℤ)*L.card := by exact_mod_cast density
  have dpos' : (1:ℤ)≤d := by exact_mod_cast dpos
  have small' : (d:ℤ)≤q := by exact_mod_cast small
  have hl : (0:ℤ)<L.card := by exact_mod_cast hL
  have per (p : Fin N) (hp : p∈B) : ((L.card:ℤ)*(q+1-d))^2 ≤ (diff p)^2 := by
    have low : degree I L p≤1 := (Finset.mem_filter.mp hp).2
    have low' : (degree I L p:ℤ)≤1 := by exact_mod_cast low
    have prod := mul_le_mul_of_nonneg_left low' (by positivity : (0:ℤ)≤N)
    have gap : (L.card:ℤ)*(q+1-d) ≤ -diff p := by dsimp [diff]; nlinarith only [den,prod]
    have sq := mul_self_le_mul_self (mul_nonneg hl.le (by omega : (0:ℤ)≤q+1-d)) gap
    nlinarith only [sq]
  have sum := Finset.sum_le_sum per
  have grow : (∑ p∈B, (diff p)^2) ≤ ∑ p, (diff p)^2 :=
    Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
  simp only [Finset.sum_const,nsmul_eq_mul] at sum
  have cap : (N:ℤ)-L.card ≤ ((d:ℤ)-1)*L.card := by nlinarith only [den]
  have grow2 := mul_le_mul_of_nonneg_left cap (by positivity : (0:ℤ)≤(N:ℤ)*q*L.card)
  have cmp : (B.card:ℤ)*(q+1-d)^2*(L.card:ℤ)^2 ≤ ((d:ℤ)-1)*N*q*(L.card:ℤ)^2 := by
    nlinarith only [sum.trans (grow.trans (var.trans grow2))]
  have cancel := le_of_mul_le_mul_right cmp (sq_pos_of_pos hl)
  have tgt : ((d:ℤ)-1)*N*q ≤ (K:ℤ)*(q+1-d)^2 := by
    have z : (((d-1:ℕ):ℤ)*N*q ≤ (K:ℤ)*((q+1-d:ℕ):ℤ)^2) := by exact_mod_cast target
    simpa [Nat.cast_sub dpos,Nat.cast_sub (by omega : d≤q+1)] using z
  have fin := le_of_mul_le_mul_right (cancel.trans tgt) (sq_pos_of_pos (by omega : (0:ℤ)<q+1-d))
  exact_mod_cast fin

end GateElim.Plane
#print axioms GateElim.Plane.few_at_fraction
