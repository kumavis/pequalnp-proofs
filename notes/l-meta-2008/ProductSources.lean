import BlockTools

namespace GateElim.Products
open Reverse Cuts Block Finset Classical
variable {V : Type*} {n : ℕ}

def sources {n : ℕ} (P : Prog n) (x z : Fin n→Fn V) : List (Fn V ×Fn V) := match P with
  | .ret _ => []
  | .gate op a b t =>
    (if op then [] else [(x a,z b),(x b,z a)])++sources t (forward x op a b) (forward z op a b)

theorem sources_len (P : Prog n) (x z : Fin n→Fn V) : (sources P x z).length≤2*P.size := by
  induction P with
  | ret => simp [sources]
  | gate op a b t ih =>
    have h := ih (forward x op a b) (forward z op a b)
    cases op <;> simp [sources,Prog.size] <;> omega

theorem banks (P : Prog n) (x z : Fin n→Fn V) (S T : Set (Fn V)) (ax : ∀ i,x i∈S) (az : ∀ i,z i∈T) :
    ∃ gs hs : List (Node V), gs.length=P.size ∧ hs.length=P.size ∧ Built S gs ∧ Built T hs ∧
      ∀ v∈sources P x z, v.1∈pool S gs ∧ v.2∈pool T hs := by
  induction P generalizing S T with
  | ret => exact ⟨[],[],rfl,rfl,True.intro,True.intro,by simp [sources]⟩
  | @gate n op a b t ih =>
    let g : Node V := ⟨op,x a,x b⟩
    let h : Node V := ⟨op,z a,z b⟩
    let S' := insert g.value S
    let T' := insert h.value T
    have ax' (i : Fin (n+1)) : forward x op a b i∈S' := by
      cases i using Fin.lastCases <;> simp [forward,S',g,ax]
    have az' (i : Fin (n+1)) : forward z op a b i∈T' := by
      cases i using Fin.lastCases <;> simp [forward,T',h,az]
    obtain ⟨gs,hs,l,r,bu,bv,av⟩ := ih (forward x op a b) (forward z op a b) S' T' ax' az'
    refine ⟨g::gs,h::hs,by simp [l,Prog.size],by simp [r,Prog.size],⟨ax _,ax _,bu⟩,⟨az _,az _,bv⟩,?_⟩
    have old (i j : Fin n) : x i∈pool S' gs ∧ z j∈pool T' hs :=
      ⟨pool_grows _ _ (Set.mem_insert_of_mem _ (ax _)),pool_grows _ _ (Set.mem_insert_of_mem _ (az _))⟩
    intro v mv; rcases List.mem_append.mp mv with head|tail
    · cases op with
      | true => simp at head
      | false =>
        simp only [Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false] at head
        rcases head with rfl|rfl
        · exact old a b
        · exact old b a
    · exact av _ tail

/-- If neither pure setting accepts, some physical AND must have one operand
true at the first pure setting and its other operand true at the second. -/
theorem first_source (P : Prog n) (x z : Fin n→Fn V) (y v : V→Bool) (mix : Fin n→Bool)
    (raw : ∀ i,mix i=true → x i y=true ∨ z i v=true)
    (away : ∀ r∈sources P x z,¬(r.1 y=true ∧ r.2 v=true)) :
    P.eval mix=true → val P x y=true ∨ val P z v=true := by
  induction P with
  | ret i => exact raw i
  | @gate n op a b t ih =>
    let X := forward x op a b; let Z := forward z op a b
    have next : ∀ r∈sources t X Z, ¬(r.1 y=true ∧ r.2 v=true) := fun r h => away r (List.mem_append_right _ h)
    have step (i : Fin (n+1)) : snoc mix (applyOp op (mix a) (mix b)) i=true → X i y=true ∨ Z i v=true := by
      cases i using Fin.lastCases with
      | cast i => simpa [X,Z,forward] using raw i
      | last =>
        have ra := raw a; have rb := raw b
        cases op with
        | true => simp [X,Z,forward,Node.value,applyOp]; tauto
        | false =>
          have noAB := away (x a,z b) (by simp [sources])
          have noBA := away (x b,z a) (by simp [sources])
          simp [X,Z,forward,Node.value,applyOp]; tauto
    intro h
    have yes := ih X Z (snoc mix (applyOp op (mix a) (mix b))) step next h
    simpa only [X,Z,Block.val,forward_at,Prog.eval] using yes

end GateElim.Products
#print axioms GateElim.Products.first_source
