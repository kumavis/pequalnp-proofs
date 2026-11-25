import BatchGates

namespace GateElim.Port
open Reverse Finset Classical
variable {V : Type*} {n : ℕ}

def uses {n : ℕ} (P : Prog n) (i : Fin n) : ℕ :=
  match P with
  | .ret _ => 0
  | .gate _ a b t => (if a=i ∨ b=i then 1 else 0)+uses t i.castSucc

def returns {n : ℕ} (P : Prog n) (i : Fin n) : Prop :=
  match P with
  | .ret o => o=i
  | .gate _ _ _ t => returns t i.castSucc

theorem returns_eval (P : Prog n) (i : Fin n) (h : returns P i) (y : Fin n → Bool) :
    P.eval y=y i := by
  induction P with
  | ret o => exact congrArg y h
  | gate op a b t ih =>
    exact (ih _ h _).trans (snoc_old ..)

theorem ignore (P : Prog n) (i : Fin n) (none : uses P i=0) (out : ¬returns P i)
    (x y : Fin n → Bool) (agree : ∀ j, j≠i → x j=y j) : P.eval x=P.eval y := by
  induction P with
  | ret o => exact agree o out
  | gate op a b t ih =>
    have miss : a≠i ∧ b≠i := by
      simp [uses] at none; exact none.1
    have rest : uses t i.castSucc=0 := by simpa [uses,miss] using none
    apply ih i.castSucc rest out
    intro j hj; cases j using Fin.lastCases with
    | last => simp [agree a miss.1,agree b miss.2]
    | cast j =>
      simp only [snoc_old]; apply agree j; intro e; exact hj (e ▸ rfl)

def fn (P : Prog n) (x : Fin n → Fn V) : Fn V := fun y => P.eval (fun i => x i y)

private theorem add_at (x : Fin n → Fn V) (g : Fn V) (y : V → Bool) :
    (fun j => snoc x g j y)=snoc (fun i => x i y) (g y) := by
  funext j; cases j using Fin.lastCases <;> simp

theorem fn_cons (op : Bool) (a b : Fin n) (t : Prog (n+1)) (x : Fin n → Fn V) :
    fn (.gate op a b t) x=fn t (snoc x (Cuts.comb op (x a) (x b))) := by
  funext y; simp only [fn,Prog.eval,add_at,Cuts.comb,Node.value,applyOp]

/-- Every gate reading a zero operand disappears under constant folding. -/
noncomputable def saved {n : ℕ} (P : Prog n) (x : Fin n → Fn V) : ℕ :=
  match P with
  | .ret _ => 0
  | .gate op a b t => (if x a=const false ∨ x b=const false then 1 else 0)+
    saved t (snoc x (Cuts.comb op (x a) (x b)))

theorem zeros (P : Prog n) (x : Fin n → Fn V) (i : Fin n) (zero : x i=const false) :
    uses P i ≤ saved P x := by
  induction P with
  | ret o => rfl
  | gate op a b t ih =>
    have h := ih (snoc x (Cuts.comb op (x a) (x b))) i.castSucc (by simpa)
    change (if _ then 1 else 0)+_ ≤ (if _ then 1 else 0)+_
    apply Nat.add_le_add _ h
    by_cases read : a=i ∨ b=i
    · have vanish : x a=const false ∨ x b=const false := by rcases read with rfl|rfl <;> simp [zero]
      simp [read,vanish]
    · simp [read]

theorem folding (P : Prog n) (x : Fin n → Fn V) (S : Set (Fn V)) (av : ∀ i, x i∈S) (zero : const false∈S) :
    ∃ gs : List (Node V), gs.length+saved P x≤P.size ∧ Built S gs ∧ fn P x∈pool S gs := by
  induction P generalizing S with
  | ret o => exact ⟨[],by simp [saved,Prog.size],True.intro,av o⟩
  | gate op a b t ih =>
    let g := Node.mk op (x a) (x b)
    let z := snoc x g.value
    by_cases vanish : x a=const false ∨ x b=const false
    · have existsWire : g.value∈S := by
        rcases vanish with ha|hb
        · cases op
          · have eq : g.value=const false := by funext y; simp [g,Node.value,ha,const]
            exact eq ▸ zero
          · have eq : g.value=x b := by funext y; simp [g,Node.value,ha,const]
            exact eq ▸ av b
        · cases op
          · have eq : g.value=const false := by funext y; simp [g,Node.value,hb,const]
            exact eq ▸ zero
          · have eq : g.value=x a := by funext y; simp [g,Node.value,hb,const]
            exact eq ▸ av a
      have existsZ (j) : z j∈S := by cases j using Fin.lastCases <;> simp [z,existsWire,av]
      obtain ⟨gs,cost,bu,terminal⟩ := ih z S existsZ zero
      exact ⟨gs,by simp only [saved,vanish,↓reduceIte,Prog.size]; change gs.length+(1+saved t z)≤_; omega,
        bu,by rwa [fn_cons]⟩
    · have existsZ (i) : z i∈insert g.value S := by
        cases i using Fin.lastCases <;> simp [z,av]
      obtain ⟨gs,cost,bu,terminal⟩ := ih z (insert g.value S) existsZ (Set.mem_insert_of_mem _ zero)
      refine ⟨g::gs,?_,⟨av _,av _,bu⟩,?_⟩
      · simp only [List.length_cons,saved,vanish,↓reduceIte,Nat.zero_add,Prog.size]
        change gs.length+1+saved t z≤_; omega
      · rwa [fn_cons]

end GateElim.Port
#print axioms GateElim.Port.folding
