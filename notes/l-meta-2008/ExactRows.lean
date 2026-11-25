import BatchGates
import PlaneRows

namespace GateElim.Rows
open Cuts Reverse Finset Classical
variable {V J : Type*} [DecidableEq V] [Fintype V] [DecidableEq J] [Fintype J]

noncomputable def sumRow (U : Finset V) : Fn V := fun x => decide (∃ i∈U, x i=true)

private theorem makeRow (A : Finset V) (f : Fn V) (S : Set (Fn V)) (hf : f∈S)
    (inputs : ∀ i∈A, var i∈S) :
    ∃ gs : List (Node V), ∃ F : Fn V, gs.length=A.card ∧ Built S gs ∧ F∈pool S gs ∧
      ∀ y, F y=true ↔ f y=true ∨ ∃ i∈A, y i=true := by
  induction A using Finset.induction_on with
  | empty => exact ⟨[],f,rfl,True.intro,hf,by simp⟩
  | @insert j A fresh ih =>
    obtain ⟨gs,v,l,bu,av,ev⟩ := ih (fun i hi => inputs i (Finset.mem_insert_of_mem hi))
    let g := Node.mk true v (var j)
    refine ⟨gs++[g],g.value,by simp [fresh,l],build_append bu
      ⟨av,pool_grows _ _ (inputs _ (Finset.mem_insert_self ..)),True.intro⟩,?_,?_⟩
    · rw [pool_append]; exact Set.mem_insert _ _
    · intro y; simp [g,Node.value,ev,var]; grind

theorem family_upper (S : J → Finset V) (nonempty : ∀ j, (S j).Nonempty) :
    ∃ gs : List (Node V), gs.length=∑ j, ((S j).card-1) ∧ ∀ j, Ready (base univ) gs (sumRow (S j)) := by
  classical
  have aux (D : Finset J) (T : Set (Fn V)) (source : ∀ i, var i∈T) :
      ∃ gs : List (Node V), gs.length=∑ j∈D, ((S j).card-1) ∧ Built T gs ∧ ∀ j∈D, sumRow (S j)∈pool T gs := by
    induction D using Finset.induction_on generalizing T with
    | empty => exact ⟨[],by simp,True.intro,by simp⟩
    | @insert j D fresh ih =>
      obtain ⟨i,hi⟩ := nonempty j
      obtain ⟨gs,F,l,bu,av,ev⟩ := makeRow ((S j).erase i) (var i) T (source _) (fun _ _ => source _)
      have eq : F=sumRow (S j) := by
        funext y; apply Bool.eq_iff_iff.mpr
        simp only [ev,var,sumRow,decide_eq_true_eq,Finset.mem_erase]
        constructor
        · rintro (h|⟨v,⟨_,m⟩,hv⟩)
          · exact ⟨i,hi,h⟩
          · exact ⟨v,m,hv⟩
        · rintro ⟨v,m,hv⟩; by_cases e : v=i
          · exact Or.inl (e ▸ hv)
          · exact Or.inr ⟨v,⟨e,m⟩,hv⟩
      obtain ⟨hs,hl,hb,ha⟩ := ih (pool T gs) (fun i => pool_grows _ _ (source i))
      refine ⟨gs++hs,by simp [l,hl,fresh,hi],build_append bu hb,?_⟩
      intro u hu; rw [pool_append]; rcases Finset.mem_insert.mp hu with rfl|h
      · exact pool_grows _ _ (eq ▸ av)
      · exact ha u h
  obtain ⟨gs,l,bu,ready⟩ := aux univ (base univ) (fun i => Or.inr ⟨i,by simp,rfl⟩)
  exact ⟨gs,l,fun j => ready_of_built bu (ready j (by simp))⟩

end GateElim.Rows

namespace GateElim.Plane
open Finset Classical Rows
theorem exact_separate_outputs {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (side : Bool) :
    (∃ gs : List (Node (Fin N)), gs.length=N*q ∧ ∀ j, Ready (base univ) gs (sumRow (rowSet side I j))) ∧
    (∀ (gs : List (Node (Fin N))) (F : Fin N → Fn (Fin N)), (∀ j, Ready (base univ) gs (F j)) →
      (∀ j v, v∈rowSet side I j → F j (onSet {v})=true) →
      (∀ j U, Disjoint U (rowSet side I j) → U.card≤q → F j (onSet U)=false) → N*q≤gs.length) := by
  have ⟨deg,linear⟩ := row_geometry I ord hd hj side
  constructor
  · obtain ⟨gs,len,ready⟩ := family_upper (rowSet side I) (fun j => Finset.card_pos.mp (by rw [deg]; omega))
    simp_rw [deg] at len; exact ⟨gs,by simpa using len,ready⟩
  · intro gs F ready pos neg
    have h := circuit_bound (rowSet side I) (rowSet side I) F gs univ linear ready pos
      (fun j U dis count => neg j U dis (by rw [deg] at count; omega))
    simp_rw [deg] at h; simpa using h
end GateElim.Plane
#print axioms GateElim.Plane.exact_separate_outputs
