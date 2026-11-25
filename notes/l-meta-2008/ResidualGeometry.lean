import Mathlib

/-! A deletion estimate for the next gate-elimination step. It controls every
set of surviving lines simultaneously, including sets selected by a circuit.
The bound is a finite combinatorial fact, independent of the circuit model. -/
namespace Desk2008.Residual

def degree {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (L : Finset (Fin N)) (p : Fin N) := (L.filter (I p)).card

theorem moments {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (lineSize : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (join : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (L : Finset (Fin N)) :
    (∑ p, degree I L p) = L.card*(q+1) ∧
    (∑ p, (degree I L p)^2) ≤ L.card*(L.card+q) := by
  classical
  let bit (p l : Fin N) : ℕ := if I p l then 1 else 0
  have d (p : Fin N) : degree I L p = ∑ l ∈ L, bit p l := by simp [degree,bit,Finset.sum_boole]
  have col (l : Fin N) : (∑ p, bit p l) = q+1 := by
    simpa [bit,Finset.sum_boole,Fintype.card_subtype] using lineSize l
  have cross (l r : Fin N) : (∑ p, bit p l*bit p r) ≤ 1 + (if r=l then q else 0) := by
    by_cases eq : r=l
    · subst r
      have h (p : Fin N) : bit p l * bit p l = bit p l := by by_cases b : I p l <;> simp [bit,b]
      simp [h,col,Nat.add_comm]
    · have eqb (p : Fin N) : bit p l * bit p r = if I p l ∧ I p r then 1 else 0 := by
        by_cases a : I p l <;> by_cases b : I p r <;> simp [bit,a,b]
      simp only [eqb,Finset.sum_boole,ite_eq_right eq,Nat.add_zero]
      apply Finset.card_le_one_iff.mpr
      intro a b ha hb
      by_contra ab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      obtain ⟨t,_,unique⟩ := join a b ab
      exact eq ((unique r ⟨ha'.2,hb'.2⟩).trans (unique l ⟨ha'.1,hb'.1⟩).symm)
  constructor
  · simp only [d]; rw [Finset.sum_comm]; simp [col]
  · calc
      _ = ∑ p, ∑ l ∈ L, ∑ r ∈ L, bit p l*bit p r := by
        simp only [d,pow_two,Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl; intro p _
        apply Finset.sum_congr rfl; intro l _
        apply Finset.sum_congr rfl; intro r _
        exact Nat.mul_comm _ _
      _ = ∑ l ∈ L, ∑ p, ∑ r ∈ L, bit p l*bit p r := Finset.sum_comm
      _ = ∑ l ∈ L, ∑ r ∈ L, ∑ p, bit p l*bit p r := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ ≤ ∑ l ∈ L, ∑ r ∈ L, (1+ if r=l then q else 0) :=
        Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun r _ => cross l r))
      _ = _ := by
        apply Eq.trans (Finset.sum_congr rfl (g := fun _ => L.card+q) ?_)
        · simp
        · intro l hl; simp [Finset.sum_add_distrib,hl]

/-- A variance estimate, using only the two incidence axioms of the desk. -/
theorem variance {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (order : N=q^2+q+1) (lineSize : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (join : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (L : Finset (Fin N)) :
    (∑ p, ((N : ℤ)*degree I L p - (L.card : ℤ)*(q+1))^2)
       ≤ (N : ℤ)*q*L.card*(N-L.card) := by
  obtain ⟨one,two⟩ := moments I lineSize join L
  have a : (∑ p, (degree I L p : ℤ)) = (L.card : ℤ)*(q+1) := by exact_mod_cast one
  have b : (∑ p, (degree I L p : ℤ)^2) ≤ (L.card : ℤ)*(L.card+q) := by exact_mod_cast two
  have ord : (N : ℤ)=(q : ℤ)^2+q+1 := by exact_mod_cast order
  have form (p : Fin N) : ((N : ℤ)*degree I L p - (L.card : ℤ)*(q+1))^2 =
       (N : ℤ)^2*(degree I L p : ℤ)^2 -
       (2*N*L.card*(q+1):ℤ)*degree I L p + ((L.card : ℤ)*(q+1))^2 := by ring
  simp only [form,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,a]
  have bound := mul_le_mul_of_nonneg_left b (sq_nonneg (N : ℤ))
  calc
    _ ≤ (N : ℤ)^2*(L.card*(L.card+q)) - 2*N*L.card*(q+1)*(L.card*(q+1)) +
        N*((L.card : ℤ)*(q+1))^2 := by linarith
    _ = _ := by rw [ord]; ring

/-- If half the lines survive and q is at least eight, at most q+3 points
have zero or one remaining incident line. -/
theorem few_low {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 8≤q) (order : N=q^2+q+1) (lineSize : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (join : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (L : Finset (Fin N)) (half : N≤2*L.card) :
    (Finset.univ.filter (fun p => degree I L p≤1)).card ≤ q+3 := by
  classical
  let bad := Finset.univ.filter (fun p => degree I L p≤1)
  let diff (p : Fin N) : ℤ := (N : ℤ)*degree I L p - (L.card : ℤ)*(q+1)
  have var := variance I order lineSize join L
  change (∑ p, (diff p)^2) ≤ _ at var
  have hq' : (8:ℤ)≤q := by exact_mod_cast hq
  have hn' : (0:ℤ)<N := by exact_mod_cast (show 0<N by omega)
  have half' : (N:ℤ)≤2*L.card := by exact_mod_cast half
  have localBound (p : Fin N) (hp : p∈bad) :
      ((N : ℤ)*(q-1))^2 ≤ 4*(diff p)^2 := by
    have d : degree I L p≤1 := (Finset.mem_filter.mp hp).2
    have d' : (degree I L p : ℤ)≤1 := by exact_mod_cast d
    have prod := mul_le_mul_of_nonneg_right half' (show 0≤(q:ℤ)+1 by omega)
    have md := mul_le_mul_of_nonneg_left d' (le_of_lt hn')
    have lhs : 0≤(N : ℤ)*(q-1) := mul_nonneg (le_of_lt hn') (by omega)
    have dist : (N : ℤ)*(q-1) ≤ -2*diff p := by dsimp [diff]; nlinarith only [prod,md]
    have sq := mul_self_le_mul_self lhs dist
    nlinarith only [sq]
  have sumBound := Finset.sum_le_sum localBound
  have enlarge : (∑ p ∈ bad, (diff p)^2) ≤ ∑ p, (diff p)^2 :=
    Finset.sum_le_univ_sum_of_nonneg (fun p => sq_nonneg _)
  simp only [Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum] at sumBound
  have dev : (bad.card : ℤ)*((N : ℤ)*(q-1))^2 ≤ (N : ℤ)^3*q := calc
    _ ≤ 4*∑ p, (diff p)^2 := sumBound.trans (by linarith)
    _ ≤ 4*((N : ℤ)*q*L.card*(N-L.card)) := by linarith
    _ ≤ _ := by
      have h := mul_nonneg (mul_nonneg (le_of_lt hn') (show 0≤(q:ℤ) by omega))
        (sq_nonneg ((N:ℤ)-2*L.card))
      nlinarith only [h]
  have f : (N : ℤ)^2 * (bad.card*(q-1)^2 : ℤ) ≤ (N : ℤ)^2*(N*q) := by nlinarith only [dev]
  have bc := (le_of_mul_le_mul_left f (by positivity : (0:ℤ)<(N:ℤ)^2))
  have ord : (N : ℤ)=(q : ℤ)^2+q+1 := by exact_mod_cast order
  by_contra! huge
  change q+3<bad.card at huge
  have hh : (q : ℤ)+4≤bad.card := by exact_mod_cast (show q+4≤bad.card by omega)
  have ch := mul_le_mul_of_nonneg_right hh (sq_nonneg ((q:ℤ)-1))
  have gap := mul_nonneg (show 0≤(q:ℤ)-8 by omega) (show 0≤(q:ℤ) by omega)
  rw [ord] at bc
  nlinarith only [bc,ch,gap,hq']

end Desk2008.Residual
#print axioms Desk2008.Residual.few_low
