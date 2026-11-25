import Mathlib
import Triangle

namespace GateElim.Plane.Grid
open Finset MvPolynomial
variable {K : Type*} [Field K]

private theorem dimension (d : ℕ) :
    2*Module.finrank K (restrictTotalDegree (Fin 2) K d)≤(d+1)*(d+2) := by
  classical
  let E := {a : Fin 2 →₀ ℕ | a.sum (fun _ k => k)≤d}
  have total (a : E) : a.val 0+a.val 1≤d := by
    have h := a.property
    change a.val.sum (fun _ k => k)≤d at h
    rw [Finsupp.sum_fintype a.val (fun (_ : Fin 2) (k : ℕ) => k) (fun _ => rfl),Fin.sum_univ_two] at h
    exact h
  let f (a : E) : ↥(triangle (d+1) (d+1)) :=
    ⟨(⟨a.val 0,by have := total a; omega⟩,⟨a.val 1,by have := total a; omega⟩),by
      have := total a; simpa [triangle,rank,Nat.lt_succ_iff] using this⟩
  have inj : Function.Injective f := by
    intro a b h
    have x := congrArg (fun v : ↥(triangle (d+1) (d+1)) => v.val.1.val) h
    have y := congrArg (fun v : ↥(triangle (d+1) (d+1)) => v.val.2.val) h
    apply Subtype.ext; ext j; fin_cases j <;> assumption
  have H := Nat.card_le_card_of_injective f inj
  simp only [Nat.card_eq_fintype_card,Fintype.card_coe] at H
  change 2*Module.finrank K (restrictSupport K E)≤_
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport K E)]
  have exactCard := triangle_card (q:=d+1) (d+1) le_rfl
  exact (Nat.mul_le_mul_left 2 H).trans (le_of_eq exactCard)

/-- Products of at most d affine line equations vanishing at earlier
points but nonzero at their own point are linearly independent. -/
theorem blanket_limit {m d : ℕ} (point : Fin m→Fin 2→K)
    (P : Fin m→MvPolynomial (Fin 2) K) (degree : ∀ i, (P i).totalDegree≤d)
    (vanish : ∀ i j, j < i → aeval (point j) (P i)=0)
    (pivot : ∀ i, aeval (point i) (P i)≠0) : 2*m≤(d+1)*(d+2) := by
  classical
  let W := restrictTotalDegree (Fin 2) K d
  let b (i : Fin m) : W := ⟨P i,(mem_restrictTotalDegree _ _ _).mpr (degree i)⟩
  have independent : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff]
    intro c sum i; by_contra h
    let S := univ.filter (fun j => c j≠0)
    obtain ⟨j,hj,first⟩ := S.exists_min_image id ⟨i,mem_filter.mpr ⟨mem_univ _,h⟩⟩
    have active := (mem_filter.mp hj).2
    let ev : W→ₗ[K]K := (aeval (point j)).toLinearMap.comp W.subtype
    have zero := congrArg ev sum
    rw [map_sum,map_zero] at zero
    rw [Finset.sum_eq_single j] at zero
    · rw [map_smul] at zero
      change c j*aeval (point j) (P j)=0 at zero
      exact (mul_ne_zero active (pivot j)) zero
    · intro k _ ne
      rw [map_smul]
      by_cases ck : c k=0
      · simp [ck]
      · have lt : j<k := lt_of_le_of_ne (first k (mem_filter.mpr ⟨mem_univ _,ck⟩)) (Ne.symm ne)
        change c k*aeval (point j) (P k)=0
        rw [vanish k j lt,mul_zero]
    · simp
  have h := independent.fintype_card_le_finrank
  simp only [Fintype.card_fin] at h
  exact (Nat.mul_le_mul_left 2 h).trans (dimension (K:=K) d)

private theorem degree_product {α : Type*} (L : α→MvPolynomial (Fin 2) K) (S : Finset α)
    (linear : ∀ l∈S, (L l).totalDegree≤1) : (∏ l∈S, L l).totalDegree≤S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert l S hl ih =>
    rw [prod_insert hl,card_insert_of_notMem hl]
    have a := linear l (mem_insert_self ..)
    have b := ih (fun r hr => linear r (mem_insert_of_mem hr))
    exact (totalDegree_mul ..).trans (by omega)

/-- For any affine coordinates over any field, the number of ordered points
having a cover of all predecessors by d lines avoiding the point is at most
(d+1)(d+2)/2. The lines may have arbitrary directions. -/
theorem line_blanket_limit {m d : ℕ} {L : Type*} (point : Fin m→Fin 2→K)
    (line : L→MvPolynomial (Fin 2) K) (linear : ∀ l, (line l).totalDegree≤1)
    (cover : Fin m→Finset L) (budget : ∀ i, (cover i).card≤d)
    (earlier : ∀ i j, j < i → ∃ l∈cover i, aeval (point j) (line l)=0)
    (avoid : ∀ i l, l∈cover i → aeval (point i) (line l)≠0) :
    2*m≤(d+1)*(d+2) := by
  apply blanket_limit point (fun i => ∏ l∈cover i, line l)
  · exact fun i => (degree_product line (cover i) (fun l _ => linear l)).trans (budget i)
  · intro i j lt; rw [map_prod]; obtain ⟨l,hl,e⟩ := earlier i j lt; exact prod_eq_zero hl e
  · intro i; rw [map_prod]; exact prod_ne_zero_iff.mpr (avoid i)

end GateElim.Plane.Grid
#print axioms GateElim.Plane.Grid.line_blanket_limit
