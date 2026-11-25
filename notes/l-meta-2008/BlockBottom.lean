import BlockTools

namespace GateElim.Block
open Reverse Cuts Finset Classical
variable {V : Type} {J : Type*} [Fintype J] [DecidableEq J] {n k : ℕ}

def contact (sel : J→Fin n) (P : Prog n) := univ.filter fun j => sel j∈ports P

theorem contact_count (sel : J→Fin n) (inj : Function.Injective sel) (P : Prog n) :
    (contact sel P).card≤P.size+1 := by
  have sub : (contact sel P).image sel⊆ports P := by
    rintro _ h; obtain ⟨j,hj,rfl⟩ := mem_image.mp h; exact (mem_filter.mp hj).2
  have count := card_le_card sub
  rw [card_image_of_injective _ inj] at count
  exact count.trans (support P).1

theorem outside (P : Prog n) (x : Fin n→Fn V) (sel : J→Fin n) (j : J) (no : j∉contact sel P) :
    val P (inputs x sel j)=val P x := by
  funext y; apply (support P).2
  intro i hi; have e : i≠sel j := fun eq => no (mem_filter.mpr ⟨mem_univ _,eq ▸ hi⟩)
  simp [inputs,selected,e]

def localCost (s h d : ℕ) := s+min (d*s) (rowCost s h d)

private theorem direct (P : Prog n) (x : Fin n→Fn V) (sel : J→Fin n) (D : Finset J)
    (S : Set (Fn V)) (av : ∀ i,x i∈S) (cs : ∀ b, const b∈S) :
    ∃ gs, gs.length≤D.card*P.size ∧ Built S gs ∧ ∀ j∈D, val P (inputs x sel j)∈pool S gs := by
  obtain ⟨gs,len,bu,has⟩ := gather D S (fun j => {val P (inputs x sel j)}) (fun _ => P.size) (by
    intro j _ U incl
    obtain ⟨hs,l,b,r⟩ := compute P (inputs x sel j) U (fun i => by
      by_cases e : i=sel j
      · have eq : inputs x sel j i=const true := by funext y; simp [inputs,selected,const,e]
        rw [eq]; exact incl (cs _)
      · have eq : inputs x sel j i=x i := by funext y; simp [inputs,selected,e]
        rw [eq]; exact incl (av _))
    exact ⟨hs,l.le,b,Set.singleton_subset_iff.mpr r⟩)
  exact ⟨gs,by simpa using len,bu,fun j hj => has j hj (Set.mem_singleton _)⟩

private theorem marked (P : Prog n) (x : Fin n→Fn V) (sel : J→Fin n) (D : Finset J)
    (S : Set (Fn V)) (av : ∀ i,x i∈S) (cs : ∀ b, const b∈S) :
    ∃ gs, gs.length≤rowCost P.size (ProgCuts P (initScope sel)) D.card ∧ Built S gs ∧
      ∀ j∈D, val P (inputs x sel j)∈pool S gs := by
  classical
  by_cases empty : D=∅
  · subst D; exact ⟨[],Nat.zero_le _,True.intro,by simp⟩
  obtain ⟨M,count,yes⟩ := syntactic_marks P (initScope sel)
  obtain ⟨gs,len,known⟩ := extract_marked P M x (fun j : D => sel j.val) S av cs
  have cover := input_cover x sel
  have ready (j : D) : Ready S gs (val P (inputs x sel j.val)) := by
    have eq : (fun y => Cuts.Prog.model P M 0 (fun i => x i y) (selected x (sel j.val) y))=val P (inputs x sel j.val) := by
      funext y; apply yes j.val
      · exact fun i => (cover j.val i).1 y
      · exact fun i no => congrFun ((cover j.val i).2 no) y
    exact eq ▸ known j
  obtain ⟨j,hj⟩ := nonempty_iff_ne_empty.mpr empty
  exact ⟨gs,by simpa [count] using len,(to_pool (ready ⟨j,hj⟩)).1,
    fun i hi => (to_pool (ready ⟨i,hi⟩)).2⟩

/-- Baseline plus all active selector responses. Either a direct evaluation
per affected selector or one reverse extraction may be used for each block. -/
theorem local_build (P : Prog n) (x : Fin n→Fn V) (sel : J→Fin n) (D : Finset J)
    (S : Set (Fn V)) (av : ∀ i,x i∈S) (cs : ∀ b, const b∈S) :
    ∃ gs, gs.length≤localCost P.size (ProgCuts P (initScope sel)) D.card ∧ Built S gs ∧
      val P x∈pool S gs ∧ ∀ j∈D, val P (inputs x sel j)∈pool S gs := by
  obtain ⟨gs,len,bu,base⟩ := compute P x S av
  let U := pool S gs
  have lift : S⊆U := pool_grows ..
  have split : ∃ hs, hs.length ≤ min (D.card*P.size) (rowCost P.size (ProgCuts P (initScope sel)) D.card) ∧
      Built U hs ∧ ∀ j∈D, val P (inputs x sel j)∈pool U hs := by
    rcases le_total (D.card*P.size) (rowCost P.size (ProgCuts P (initScope sel)) D.card) with h|h
    · rw [min_eq_left h]; exact direct P x sel D U (fun i => lift (av i)) (fun b => lift (cs b))
    · rw [min_eq_right h]; exact marked P x sel D U (fun i => lift (av i)) (fun b => lift (cs b))
  obtain ⟨hs,hl,hb,has⟩ := split
  exact ⟨gs++hs,by simpa [localCost,len] using Nat.add_le_add_left hl P.size,
    build_append bu hb,by rw [pool_append]; exact pool_grows _ _ base,
    fun j hj => by rw [pool_append]; exact has j hj⟩

end GateElim.Block
#print axioms GateElim.Block.local_build
