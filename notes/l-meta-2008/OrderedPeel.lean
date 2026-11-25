import ChoicePeel
import Peeling

namespace GateElim.Port
open Finset Classical
variable {n : ℕ}
abbrev Vertex (n : ℕ) := Fin n

structure Correct (R : Fin n → Fin n → Prop) (allowed : Finset (Fin n) → Prop)
    (A : Finset (Fin n)) (F : Fn (Fin n)) : Prop where
  yes : ∀ S⊆A, EdgeIn R S → F (bits S)=true
  no : ∀ S⊆A, allowed S → ¬EdgeIn R S → F (bits S)=false

theorem correct_weaken {R : Fin n→Fin n→Prop} {A : Finset (Fin n)} {F : Fn (Fin n)}
    {a b : Finset (Fin n)→Prop} (good : Correct R a A F) (weaker : ∀ S⊆A, b S → a S) :
    Correct R b A F := ⟨good.yes, fun S h ok => good.no S h (weaker S h ok)⟩

theorem correct_fits {R : Fin n→Fin n→Prop} {A : Finset (Fin n)} {F : Fn (Fin n)}
    {a : Finset (Fin n)→Prop} (good : Correct R a A F) (small : ∀ S⊆A, S.card≤2 → a S) : Fits R A F :=
  fun S sub => ⟨fun card => good.no S sub (small S sub card),good.yes S sub⟩

private theorem put_bit (i : Fin n) (S : Finset (Fin n)) :
    Function.update (bits S) i true=bits (insert i S) := by
  funext u; by_cases eq : u=i <;> simp [eq,bits]

theorem step {R : Fin n → Fin n → Prop} (loop : ∀ u, ¬R u u)
    {A : Finset (Fin n)} (i : Fin n) (inside : i∈A) (family : Finset (Fin n)→Prop)
    (hasEdge : EdgeIn R (A.erase i)) (empty : family ∅) (small : family {i})
    (blanket : ∀ S⊆A.erase i, family S → ¬EdgeIn R S →
      ∃ T⊆A.erase i, S⊆T ∧ family T ∧ ¬EdgeIn R T ∧ EdgeIn R (insert i T))
    {gs : List (Node (Fin n))} {F : Fn (Fin n)}
    (ready : Ready (base A) gs F) (ok : Correct R family A F) :
    ∃ hs : List (Node (Fin n)), ∃ G, Ready (base (A.erase i)) hs G ∧
      Correct R family (A.erase i) G ∧ hs.length+2≤gs.length := by
  let B := A.erase i
  let pos (y : Fin n→Bool) := ∃ S⊆B, y=bits S ∧ EdgeIn R S
  let neg (y : Fin n→Bool) := ∃ S⊆B, y=bits S ∧ family S ∧ ¬EdgeIn R S
  have supp (S : Finset (Fin n)) (sub : S⊆B) : supported B (bits S) := by
    intro v on; exact sub (of_decide_eq_true on)
  have yes : ∃ y, pos y := ⟨bits B,B,by rfl,rfl,hasEdge⟩
  have no : ∃ y, neg y := ⟨bits ∅,∅,by simp,rfl,empty,by simp [EdgeIn]⟩
  have ans : Answers pos neg F := by
    constructor
    · rintro _ ⟨S,sub,rfl,on⟩; exact ok.yes S (sub.trans (Finset.erase_subset ..)) on
    · rintro _ ⟨S,sub,rfl,legal,indep⟩; exact ok.no S (sub.trans (Finset.erase_subset ..)) legal indep
  have silent : F (Function.update (fun _ => false) i true)=false := by
    have zero : (fun _ : Fin n => false)=bits ∅ := by funext u; simp [bits]
    rw [zero,put_bit]; exact ok.no {i} (by simpa using inside) small (by simp [EdgeIn,loop])
  obtain ⟨hs,G,run,correct,cost⟩ := choose_input A i gs F ready pos neg yes no
    (by rintro _ ⟨S,s,rfl,_⟩; exact supp S s) (by rintro _ ⟨S,s,rfl,_⟩; exact supp S s) ans (by
      rintro _ ⟨S,sub,rfl,legal,indep⟩
      obtain ⟨T,st,grow,legalT,free,edge⟩ := blanket S sub legal indep
      refine ⟨bits T,⟨T,st,rfl,legalT,free⟩,fun v h => decide_eq_true (grow (of_decide_eq_true h)),?_⟩
      rw [put_bit]; exact ok.yes _ (Finset.insert_subset inside (st.trans (Finset.erase_subset ..))) edge) silent
  exact ⟨hs,G,run,⟨fun S sub e => correct.1 _ ⟨S,sub,rfl,e⟩,
    fun S sub l f => correct.2 _ ⟨S,sub,rfl,l,f⟩⟩,cost⟩

/-- Delete any prescribed collection of inputs in a fixed domain of tests.
Each deletion saves two gates. -/
theorem ordered {R : Fin n → Fin n → Prop} (loop : ∀ u, ¬R u u)
    (A B : Finset (Fin n)) (sub : B⊆A) (family : Finset (Fin n) → Prop)
    (survive : EdgeIn R B) (empty : family ∅) (small : ∀ i∈A, family {i})
    (blanket : ∀ i∈A, i∉B → ∀ S⊆A, i∉S → family S → ¬EdgeIn R S →
      ∃ T⊆S∪B, S⊆T ∧ i∉T ∧ family T ∧ ¬EdgeIn R T ∧ EdgeIn R (insert i T))
    {gs : List (Node (Fin n))} {F : Fn (Fin n)}
    (ready : Ready (base A) gs F) (ok : Correct R family A F) :
    ∃ hs : List (Node (Fin n)), ∃ G, Ready (base B) hs G ∧ Correct R family B G ∧
      hs.length+2*(A.card-B.card)≤gs.length := by
  classical
  have go (D : Finset (Fin n)) (inA : D⊆A) (big : B⊆D) {gs : List (Node (Fin n))} {G : Fn (Fin n)}
      (ready : Ready (base D) gs G) (ok : Correct R family D G) :
      ∃ hs : List (Node (Fin n)), ∃ H, Ready (base B) hs H ∧ Correct R family B H ∧
        hs.length+2*(D.card-B.card)≤gs.length := by
    induction D using Finset.strongInduction generalizing gs G with
    | H D ih =>
      by_cases done : D=B
      · subst D; exact ⟨gs,G,ready,ok,by simp⟩
      obtain ⟨i,hi,notB⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨big,Ne.symm done⟩))
      have still : B⊆D.erase i := by
        intro u hu; exact Finset.mem_erase.mpr ⟨fun e => notB (e ▸ hu),big hu⟩
      have edge : EdgeIn R (D.erase i) := by
        obtain ⟨u,hu,v,hv,e⟩ := survive; exact ⟨u,still hu,v,still hv,e⟩
      obtain ⟨next,F,run,good,spent⟩ := step loop i hi family edge empty (small i (inA hi)) (by
        intro S s allowed free
        have sD := s.trans (Finset.erase_subset ..)
        obtain ⟨T,t,g,no,allow,ind,yes⟩ := blanket i (inA hi) notB S (sD.trans inA)
          (fun m => Finset.notMem_erase i D (s m)) allowed free
        exact ⟨T,t.trans (Finset.union_subset s still),g,allow,ind,yes⟩) ready ok
      obtain ⟨hs,H,run,good,len⟩ := ih _ (Finset.erase_ssubset hi) ((Finset.erase_subset ..).trans inA) still run good
      have c := Finset.card_erase_add_one hi
      have b := Finset.card_le_card still
      exact ⟨hs,H,run,good,by omega⟩
  exact go A (by rfl) sub ready ok

end GateElim.Port
#print axioms GateElim.Port.ordered
