import Net

namespace GateElim.Cuts
open Reverse Finset Classical

private theorem build_batch {J V : Type*} [DecidableEq J] (A : Finset J)
    (g : J → Node V) (S : Set (Fn V)) (av : ∀ j∈A, (g j).a∈S ∧ (g j).b∈S) :
    ∃ gs : List (Node V), gs.length=A.card ∧ Built S gs ∧ ∀ j∈A, (g j).value∈pool S gs := by
  induction A using Finset.induction_on generalizing S with
  | empty => exact ⟨[],rfl,True.intro,by simp⟩
  | @insert i A fresh ih =>
    have a := av i (Finset.mem_insert_self ..)
    obtain ⟨gs,len,built,all⟩ := ih (insert (g i).value S) (fun j hj => by
      obtain ⟨a,b⟩ := av j (Finset.mem_insert_of_mem hj)
      exact ⟨Set.mem_insert_of_mem _ a,Set.mem_insert_of_mem _ b⟩)
    refine ⟨g i::gs,by simp [fresh,len],⟨a.1,a.2,built⟩,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl|hj
    · exact pool_grows (insert (g j).value S) gs (Set.mem_insert _ _)
    · exact all j hj

theorem batch {J V : Type*} [Fintype J] (op : Bool) (a b : J → Fn V) (S : Set (Fn V))
    (av : ∀ j, a j∈S ∧ b j∈S) :
    ∃ gs : List (Node V), gs.length=Fintype.card J ∧ Built S gs ∧ ∀ j, comb op (a j) (b j)∈pool S gs := by
  classical
  obtain ⟨gs,l,bu,av⟩ := build_batch Finset.univ (fun j => Node.mk op (a j) (b j)) S (fun j _ => av j)
  exact ⟨gs,by simpa using l,bu,fun j => av j (Finset.mem_univ _)⟩

theorem join_values {J V : Type*} [DecidableEq J] (A : Finset J) (f : J → Fn V) (S : Set (Fn V))
    (av : ∀ i∈A, f i∈S) (zero : const false∈S) :
    ∃ gs : List (Node V), ∃ v : Fn V, gs.length=A.card ∧ Built S gs ∧ v∈pool S gs ∧
      ∀ y, v y=true ↔ ∃ i∈A, f i y=true := by
  induction A using Finset.induction_on with
  | empty => exact ⟨[],const false,rfl,True.intro,zero,by simp [const]⟩
  | @insert j A fresh ih =>
    obtain ⟨gs,v,len,bu,has,eq⟩ := ih (fun i hi => av i (Finset.mem_insert_of_mem hi))
    let g := Node.mk true v (f j)
    refine ⟨gs++[g],g.value,by simp [fresh,len],build_append bu
      ⟨has,pool_grows _ _ (av _ (Finset.mem_insert_self ..)),True.intro⟩,?_,?_⟩
    · rw [pool_append]; exact Set.mem_insert _ _
    · intro y; simp [g,Node.value,eq,Finset.exists_mem_insert,or_comm]

end GateElim.Cuts
