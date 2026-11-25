import Mathlib

/-! A finite probabilistic-method argument stated entirely as counts.
Lines receive independent bucket labels. A short list of directions then
avoids the nonzero residuals in every designated point/bucket/test triple. -/
namespace LineFamilies

open Finset Classical
variable {L B T H W : Type*} [Fintype L] [Fintype B] [Fintype T] [Fintype H] [Fintype W]
variable [DecidableEq L] [DecidableEq B]

/-- Weighted sum over all assignments, factored into independent coordinates. -/
private theorem factor {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (f : ι → α → ℕ) :
    (∑ g : ι → α, ∏ i, f i (g i)) = ∏ i, ∑ a, f i a := by
  classical
  exact (Fintype.prod_sum f).symm

private theorem bucket_moment (S : Finset L) (b : B) :
    (∑ g : L → B, 2^((S.filter (fun l => g l=b)).card)) =
    (Fintype.card B+1)^S.card * (Fintype.card B)^(Fintype.card L-S.card) := by
  classical
  let w (l : L) (a : B) : ℕ := if l ∈ S ∧ a=b then 2 else 1
  have left (g : L → B) : (∏ l, w l (g l))=2^((S.filter (fun l => g l=b)).card) := by
    let good := S.filter (fun l => g l=b)
    have eq (l : L) : w l (g l) = (if l∈good then 2 else 1) := by simp [w,good]
    simp only [eq,Finset.prod_ite_mem,Finset.univ_inter,Finset.prod_const]
    rfl
  have right (l : L) : (∑ a, w l a) = (if l∈S then Fintype.card B+1 else Fintype.card B) := by
    by_cases sl : l∈S
    · have eq (a : B) : w l a = 1 + (if a=b then 1 else 0) := by
        by_cases ab : a=b <;> simp [w,sl,ab]
      simp [eq,Finset.sum_add_distrib,sl]
    · simp [w,sl]
  rw [←Finset.sum_congr rfl (fun g _ => left g),factor]
  simp only [right,Finset.prod_ite,Finset.prod_const]
  have complement : (Finset.univ.filter (fun x => x∉S))=Sᶜ := by ext x; simp
  simp [complement,Finset.card_compl]

/-- A balanced coloring exists for every listed line selection simultaneously.
The moment assumption is explicit so the result can be used at finite orders. -/
theorem balanced [Nonempty B] (family : T → Finset L) (k : ℕ)
    (small : ∑ t, Fintype.card B * ((Fintype.card B+1)^(family t).card *
        (Fintype.card B)^(Fintype.card L-(family t).card)) <
      (Fintype.card B)^(Fintype.card L) * 2^k) :
    ∃ g : L → B, ∀ t b, ((family t).filter (fun l => g l=b)).card<k := by
  classical
  by_contra! bad
  let weight (g : L → B) (t : T) (b : B) := 2^(((family t).filter (fun l => g l=b)).card)
  have heavy (g : L → B) : 2^k ≤ ∑ t, ∑ b, weight g t b := by
    obtain ⟨t,b,hot⟩ := bad g
    calc
      2^k ≤ weight g t b := Nat.pow_le_pow_right (by decide) hot
      _ ≤ ∑ b', weight g t b' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      _ ≤ _ := Finset.single_le_sum (f:=fun t => ∑ b, weight g t b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  have upper (t : T) : (∑ g : L→B, ∑ b, weight g t b) =
      Fintype.card B * ((Fintype.card B+1)^(family t).card *
        (Fintype.card B)^(Fintype.card L-(family t).card)) := by
    rw [Finset.sum_comm]
    simp [weight,bucket_moment]
  have all := Finset.sum_le_sum (fun g (_ : g∈(Finset.univ : Finset (L→B))) => heavy g)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,nsmul_eq_mul] at all
  rw [Finset.sum_comm] at all
  simp only [upper] at all
  exact (Nat.not_le_of_lt small) all

/-- A common short list contains a good direction for every constraint when
the product-counting inequality holds. -/
theorem directions (bad : W → Finset H) (m : ℕ)
    (small : (∑ w, (bad w).card^m) < (Fintype.card H)^m) :
    ∃ list : Fin m → H, ∀ w, ∃ j, list j ∉ bad w := by
  classical
  by_contra! fail
  let E (w : W) : Finset (Fin m → H) := Fintype.piFinset (fun _ => bad w)
  have cover : (Finset.univ : Finset (Fin m → H)) ⊆ Finset.univ.biUnion E := by
    intro f _
    obtain ⟨w,hw⟩ := fail f
    exact Finset.mem_biUnion.mpr ⟨w,by simp,by simpa [E,Fintype.mem_piFinset] using hw⟩
  have bound := (Finset.card_le_card cover).trans Finset.card_biUnion_le
  simp [E,Fintype.card_piFinset] at bound
  omega

end LineFamilies
#print axioms LineFamilies.balanced
#print axioms LineFamilies.directions
