import CutReverse

namespace GateElim.Cuts
open Reverse Finset Classical
variable {J V : Type*} [Fintype J] [DecidableEq J] {n k : ℕ}

def inputs (x : Fin n → Fn V) (sel : J → Fin n) (j : J) (i : Fin n) : Fn V :=
  fun y => selected x (sel j) y i

theorem input_cover (x : Fin n → Fn V) (sel : J → Fin n) :
    Covered x (inputs x sel) (initScope sel) := by
  intro j i; constructor
  · intro y h; simp [inputs,selected,h]
  · intro outside; have ne : i≠sel j := by simpa [initScope,eq_comm] using outside
    funext y; simp [inputs,selected,ne]

/-- A reverse query computes every singleton row's value at one chosen wire. -/
theorem query (G : Net n k) (o : Fin (n+k)) (x : Fin n → Fn V) (sel : J → Fin n)
    (M : ℕ→Bool) (S : Set (Fn V)) (has : ∀ i, G.run comb x i∈S) (cs : ∀ b, const b∈S)
    (paid : Paid M x (inputs x sel) S G) :
    ∃ gs : List (Node V), gs.length≤4*k+(2*tally M k+1)*Fintype.card J ∧
      Built S gs ∧ ∀ j, G.row M x (inputs x sel j) o∈pool S gs := by
  let w0 (i : Fin (n+k)) := const (V:=V) (decide (i=o))
  let z := inputs x sel
  have cover := input_cover x sel
  obtain ⟨gs,u,c,l,bu,ua,ca,ev,scalar,inc⟩ := sweep G x z M S has paid
    w0 (fun _ => G.run comb x o) (fun _ => cs _) (fun _ => has o)
  have unit (z' : Fin (n+k) → Fn V) (y : V → Bool) :
      form w0 z' (const false) y ↔ z' o y=true := by simp [form,w0,const]
  obtain ⟨hs,hl,hb,stage⟩ := batch true c (fun j => u (sel j)) (pool S gs) (fun j => ⟨ca j,ua _⟩)
  refine ⟨gs++hs,?_,build_append bu hb,?_⟩
  · simp only [List.length_append,hl,Nat.add_mul,one_mul]; omega
  · intro j; rw [pool_append]
    have eq : G.row M x (z j) o = comb true (c j) (u (sel j)) := by
      funext y
      have lower := (lower_upper G M x (z j) (fun i => (cover j i).1) o).1 y
      have start : form w0 (G.row M x (z j)) (G.run comb x o) y ↔ G.row M x (z j) o y=true := by
        simp [form,w0,const]; tauto
      have applyEq := start.symm.trans (ev j y)
      have toBase (h : form u x (const false) y) := (unit _ y).mp (scalar y h)
      apply Bool.eq_iff_iff.mpr
      simp only [comb,Node.value,↓reduceIte,Bool.or_eq_true]
      constructor
      · intro yes
        rcases applyEq.mp yes with bias|⟨i,wi,zi⟩
        · exact Or.inl bias
        · have choice : i=sel j ∨ x i y=true := by simpa [z,inputs,selected] using zi
          rcases choice with rfl|base
          · exact Or.inr wi
          · exact Or.inl (inc j y (toBase (Or.inr ⟨i,wi,base⟩)))
      · rintro (bias|self)
        · exact applyEq.mpr (Or.inl bias)
        · exact applyEq.mpr (Or.inr ⟨sel j,self,by simp [z,inputs,selected]⟩)
    exact eq ▸ stage j

/-- All base wire functions are computed together in one forward pass. -/
theorem bases (G : Net n k) (x : Fin n → Fn V) (S : Set (Fn V)) (av : ∀ i, x i∈S) :
    ∃ gs : List (Node V), gs.length=k ∧ Built S gs ∧ ∀ i, G.run comb x i∈pool S gs := by
  induction G with
  | empty => exact ⟨[],rfl,True.intro,av⟩
  | add pre op a b ih =>
    obtain ⟨gs,l,bu,has⟩ := ih
    let g := Node.mk op (pre.run comb x a) (pre.run comb x b)
    refine ⟨gs++[g],by simp [l],build_append bu ⟨has _,has _,True.intro⟩,?_⟩
    intro i; rw [pool_append]
    cases i using Fin.lastCases with
    | last => simpa [Net.run,pool,comb,g] using (Set.mem_insert g.value (pool S gs))
    | cast i => simpa only [Net.run,snoc_old,pool] using Set.mem_insert_of_mem g.value (has i)

end GateElim.Cuts
#print axioms GateElim.Cuts.query
