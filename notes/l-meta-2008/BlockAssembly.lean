import BlockTop
import BlockBottom

namespace GateElim.Block
open Reverse Cuts Finset Classical
variable {V : Type} {J : Type*} [Fintype J] [DecidableEq J] {n k : ℕ}

noncomputable def localSum (B : Fin k→Prog n) (sel : J→Fin n) :=
  ∑ i, localCost (B i).size (ProgCuts (B i) (initScope sel)) (contact sel (B i)).card

/-- A two-stage circuit may share each block output arbitrarily in the
upper circuit. The individual bottom programs share original input bits. -/
theorem assemble (T : Prog k) (B : Fin k→Prog n) (x : Fin n→Fn V) (sel : J→Fin n)
    (S : Set (Fn V)) (av : ∀ i,x i∈S) (cs : ∀ b,const b∈S) :
    let X := fun i => val (B i) x
    let Z := fun (j : J) i => val (B i) (inputs x sel j)
    let D := fun i => contact sel (B i)
    ∃ gs, gs.length≤localSum B sel+5*T.size+2*(∑ i,(D i).card) ∧
      ∀ j, Ready S gs (result T X Z D j) := by
  let X := fun i => val (B i) x
  let Z := fun (j : J) i => val (B i) (inputs x sel j)
  let D := fun i => contact sel (B i)
  let O (i : Fin k) : Set (Fn V) := {f | f=X i ∨ ∃ j∈D i, f=Z j i}
  obtain ⟨gs,len,bu,has⟩ := gather (univ : Finset (Fin k)) S O
    (fun i => localCost (B i).size (ProgCuts (B i) (initScope sel)) (D i).card) (by
      intro i _ U incl
      obtain ⟨hs,l,b,bb,rr⟩ := local_build (B i) x sel (D i) U (fun j => incl (av j)) (fun b => incl (cs b))
      refine ⟨hs,l,b,?_⟩
      rintro f (rfl|⟨j,hj,rfl⟩)
      · exact bb
      · exact rr j hj)
  have ok (i : Fin k) := has i (mem_univ _)
  obtain ⟨hs,hl,hb,hav⟩ := finish T X Z D (pool S gs) (fun b => pool_grows _ _ (cs b))
    (fun i => ok i (Or.inl rfl)) (fun j i mem => ok i (Or.inr ⟨j,mem,rfl⟩))
  change gs.length≤localSum B sel at len
  refine ⟨gs++hs,by simp only [List.length_append]; dsimp [D] at hl; omega,?_⟩
  intro j; apply ready_of_built (build_append bu hb); rw [pool_append]; exact hav j

end GateElim.Block
#print axioms GateElim.Block.assemble
