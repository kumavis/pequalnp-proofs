import FamilyCounting

namespace LineFamilies
open Finset Classical
variable {P L H B T : Type*} [Fintype P] [Fintype L] [Fintype H] [Fintype B] [Fintype T]
variable [DecidableEq L] [DecidableEq B] [DecidableEq H]

/-- None denotes a true incidence. Each nonincident line can masquerade as
incident under just one direction. Bucketed tests use only AND and OR. -/
def passes {m : ℕ} (res : P → L → Option H) (color : L → B) (dirs : Fin m → H)
    (p : P) (Y : Finset L) : Prop :=
  ∃ b : B, ∀ i, ∃ l∈Y, color l=b ∧ (res p l=none ∨ res p l=some (dirs i))

theorem positive {m : ℕ} (res : P → L → Option H) (color : L → B) (dirs : Fin m → H)
    (p : P) (Y : Finset L) (hit : ∃ l∈Y, res p l=none) : passes res color dirs p Y := by
  obtain ⟨l,inside,yes⟩ := hit
  exact ⟨color l,fun _ => ⟨l,inside,rfl,Or.inl yes⟩⟩

theorem template_schedule [Nonempty B] (res : P → L → Option H) (family : T → Finset L)
    (k m : ℕ)
    (balance : ∑ t, Fintype.card B * ((Fintype.card B+1)^(family t).card *
        (Fintype.card B)^(Fintype.card L-(family t).card)) <
      (Fintype.card B)^(Fintype.card L) * 2^k)
    (enough : Fintype.card T * Fintype.card P * Fintype.card B * (k-1)^m < (Fintype.card H)^m) :
    ∃ color : L → B, ∃ dirs : Fin m → H, ∀ t p, ∀ Y⊆family t,
      passes res color dirs p Y ↔ ∃ l∈Y, res p l=none := by
  classical
  obtain ⟨color,spread⟩ := balanced family k balance
  let cells (t : T) (b : B) := (family t).filter (fun l => color l=b)
  let bad (w : T × P × B) := (cells w.1 w.2.2).biUnion (fun l => (res w.2.1 l).toFinset)
  have small (w : T × P × B) : (bad w).card≤k-1 := by
    have atMost (l : L) (_ : l∈cells w.1 w.2.2) : (res w.2.1 l).toFinset.card≤1 := by
      cases res w.2.1 l <;> simp
    have n := Finset.card_biUnion_le (s:=cells w.1 w.2.2) (t:=fun l => (res w.2.1 l).toFinset)
    have wsum := Finset.sum_le_sum atMost
    simp only [Finset.sum_const,smul_eq_mul,mul_one] at wsum
    have sz : (cells w.1 w.2.2).card < k := spread _ _
    change ((cells w.1 w.2.2).biUnion _).card≤k-1
    omega
  have count : (∑ w, (bad w).card^m)<(Fintype.card H)^m := by
    have le := Finset.sum_le_sum (s:=Finset.univ) (fun w _ => Nat.pow_le_pow_left (small w) m)
    apply le.trans_lt
    simpa [Nat.mul_assoc] using enough
  obtain ⟨dirs,cover⟩ := directions bad m count
  refine ⟨color,dirs,?_⟩
  intro t p Y sub
  constructor
  · rintro ⟨b,all⟩
    obtain ⟨j,miss⟩ := cover (t,p,b)
    obtain ⟨l,inside,col,hit|err⟩ := all j
    · exact ⟨l,inside,hit⟩
    · exfalso; apply miss
      exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_filter.mpr ⟨sub inside,col⟩,by simp [err]⟩
  · exact positive res color dirs p Y

end LineFamilies
#print axioms LineFamilies.template_schedule
