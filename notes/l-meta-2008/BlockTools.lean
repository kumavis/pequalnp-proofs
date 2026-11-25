import DeskCuts
import ExactRows

namespace GateElim.Block
open Reverse Cuts Finset Classical
variable {V J : Type*} {k n : ℕ}

theorem to_pool {S : Set (Fn V)} {gs : List (Node V)} {F : Fn V} (h : Ready S gs F) :
    Built S gs ∧ F∈pool S gs := by
  induction gs generalizing S with
  | nil => exact ⟨True.intro,h⟩
  | cons g gs ih =>
    obtain ⟨bu,av⟩ := ih h.2.2
    exact ⟨⟨h.1,h.2.1,bu⟩,av⟩

/-- Compile each requested family once and retain all its outputs. -/
theorem gather [DecidableEq J] (A : Finset J) (S : Set (Fn V))
    (out : J→Set (Fn V)) (cost : J→ℕ)
    (each : ∀ j∈A, ∀ T, S⊆T → ∃ gs, gs.length≤cost j ∧ Built T gs ∧ out j⊆pool T gs) :
    ∃ gs, gs.length≤∑ j∈A,cost j ∧ Built S gs ∧ ∀ j∈A, out j⊆pool S gs := by
  induction A using Finset.induction_on generalizing S with
  | empty => exact ⟨[],by simp,True.intro,by simp⟩
  | @insert j A fresh ih =>
    obtain ⟨gs,l,bu,has⟩ := each j (mem_insert_self ..) S Set.Subset.rfl
    obtain ⟨hs,len,built,other⟩ := ih (pool S gs) (fun i hi T incl =>
      each i (mem_insert_of_mem hi) T ((pool_grows ..).trans incl))
    refine ⟨gs++hs,by simp only [List.length_append,sum_insert fresh]; omega,build_append bu built,?_⟩
    intro i h; rw [pool_append]
    rcases mem_insert.mp h with rfl|old
    · exact has.trans (pool_grows ..)
    · exact other i old

def val (P : Prog n) (x : Fin n→Fn V) : Fn V := fun y => P.eval (fun i => x i y)

theorem compute (P : Prog n) (x : Fin n→Fn V) (S : Set (Fn V)) (av : ∀ i,x i∈S) :
    ∃ gs, gs.length=P.size ∧ Built S gs ∧ val P x∈pool S gs := by
  obtain ⟨G,i,_,ev⟩ := net_of_prog P (fun _ => (∅ : Finset Unit))
  obtain ⟨gs,len,bu,has⟩ := bases G x S av
  have eq : G.run comb x i=val P x := by funext y; rw [run_at,ev]; rfl
  exact ⟨gs,len,bu,eq ▸ has i⟩

theorem val_mono (P : Prog n) (x z : Fin n→Fn V) (le : ∀ i, bounds (x i) (z i)) :
    bounds (val P x) (val P z) := by
  obtain ⟨G,i,_,ev⟩ := net_of_prog P (fun _ => (∅ : Finset Unit))
  have a := lower_upper G (fun _ => false) x z le i
  intro y yes; have h := (a.2 y) (a.1 y (by simpa [run_at,ev,val] using yes))
  simpa [run_at,ev,val] using h

def ports {n : ℕ} : Prog n → Finset (Fin n)
  | .ret i => {i}
  | .gate _ a b t =>
    let u := ports t
    let old := Finset.univ.filter fun i => i.castSucc∈u
    if Fin.last _∈u then insert a (insert b old) else old

/-- At most s+1 distinct input ports can reach one output of s binary gates. -/
theorem support (P : Prog n) : (ports P).card≤P.size+1 ∧
    ∀ x z : Fin n→Bool, (∀ i∈ports P, x i=z i) → P.eval x=P.eval z := by
  classical
  induction P with
  | ret i => exact ⟨by simp [ports,Prog.size],fun _ _ agree => agree i (by simp [ports])⟩
  | @gate n op a b t ih =>
    let T := ports t
    obtain ⟨small,agree⟩ := ih
    change T.card≤_ at small
    let A := univ.filter fun i : Fin n => i.castSucc∈T
    have up : A.image Fin.castSucc=T.erase (Fin.last n) := by
      ext i; cases i using Fin.lastCases <;> simp [A,Fin.castSucc_ne_last,Ne.symm (Fin.castSucc_ne_last _)]
    have card : A.card=(T.erase (Fin.last n)).card := by rw [←up,card_image_of_injective _ (Fin.castSucc_injective _)]
    by_cases used : Fin.last n∈T
    · change (if Fin.last n∈T then insert a (insert b A) else A).card≤_ ∧ _
      simp only [ports,show Fin.last n∈ports t from used,if_true,used]
      refine ⟨?_,?_⟩
      · have h := card_erase_add_one used
        have u := card_insert_le a (insert b A); have v := card_insert_le b A
        simp only [Prog.size]; omega
      · intro x z eq; apply agree; intro i hi
        cases i using Fin.lastCases with
        | last => simp only [snoc_last]; rw [eq a (by simp),eq b (by simp)]
        | cast j => simpa only [snoc_old] using eq j (mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _,hi⟩)))
    · change (if Fin.last n∈T then insert a (insert b A) else A).card≤_ ∧ _
      simp only [ports,show Fin.last n∉ports t from used,if_false,used]
      refine ⟨by rw [card,erase_eq_of_notMem used]; simp only [Prog.size]; omega,?_⟩
      intro x z eq; apply agree; intro i hi
      cases i using Fin.lastCases with
      | last => contradiction
      | cast j => simpa only [snoc_old] using eq j (mem_filter.mpr ⟨mem_univ _,hi⟩)

end GateElim.Block
#print axioms GateElim.Block.support
