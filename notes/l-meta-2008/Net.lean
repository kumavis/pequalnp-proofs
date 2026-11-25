import ExtractRows

namespace GateElim.Cuts
open Reverse Finset Classical

/-- A chronological gate list. At length k, the input ports followed by k
appended results may be used as the two operands of the next gate. -/
inductive Net (n : ℕ) : ℕ → Type
  | empty : Net n 0
  | add {k : ℕ} (pre : Net n k) (op : Bool) (a b : Fin (n+k)) : Net n (k+1)

def Net.run {α : Type*} {n k : ℕ} (comb : Bool → α → α → α) (x : Fin n → α) :
    Net n k → Fin (n+k) → α
  | .empty => x
  | .add pre op a b =>
    let z := pre.run comb x
    snoc z (comb op (z a) (z b))

def comb {V : Type*} (o : Bool) (a b : Fn V) : Fn V := (Node.mk o a b).value

def bounds {V : Type*} (f g : Fn V) := ∀ y, f y=true → g y=true

def unionOp {J : Type*} [DecidableEq J] (_ : Bool) (a b : Finset J) := a∪b

def clash {J : Type*} [DecidableEq J] (op : Bool) (a b : Finset J) : Prop :=
  op=false ∧ ¬Disjoint a b

noncomputable def Net.cuts {n k : ℕ} {J : Type*} [DecidableEq J] (sc : Fin n → Finset J) : Net n k → ℕ
  | .empty => 0
  | .add pre op a b =>
    pre.cuts sc + (if clash op (pre.run unionOp sc a) (pre.run unionOp sc b) then 1 else 0)

noncomputable def ProgCuts {J : Type*} [DecidableEq J] {n : ℕ} (P : Prog n) (sc : Fin n → Finset J) : ℕ :=
  match P with
  | .ret _ => 0
  | .gate op a b rest =>
    (if clash op (sc a) (sc b) then 1 else 0) + ProgCuts rest (snoc sc (sc a∪sc b))

theorem history {J : Type*} [DecidableEq J] {n k : ℕ} (pre : Net n k)
    (P : Prog (n+k)) (sc : Fin n → Finset J) :
    ∃ m, ∃ G : Net n m, ∃ o : Fin (n+m), m=k+P.size ∧
      G.cuts sc=pre.cuts sc+ProgCuts P (pre.run unionOp sc) ∧
      ∀ x : Fin n → Bool, G.run applyOp x o = P.eval (pre.run applyOp x) := by
  cases P with
  | ret j =>
    exact ⟨k,pre,j,by simp [Prog.size],by simp [ProgCuts],fun _ => rfl⟩
  | gate op a b t =>
    let next := Net.add pre op a b
    obtain ⟨m,G,o,len,cuts,ev⟩ := history next t sc
    refine ⟨m,G,o,?_,?_,fun x => ev x⟩
    · simp only [Prog.size]; omega
    · simpa only [next,Net.cuts,Net.run,unionOp,ProgCuts,Nat.add_assoc] using cuts
termination_by P.size
decreasing_by all_goals first | decreasing_tactic | omega | simp_all [Prog.size]

theorem net_of_prog {J : Type*} [DecidableEq J] {n : ℕ} (P : Prog n) (sc : Fin n → Finset J) :
    ∃ G : Net n P.size, ∃ o : Fin (n+P.size), G.cuts sc=ProgCuts P sc ∧
      ∀ x : Fin n → Bool, G.run applyOp x o=P.eval x := by
  obtain ⟨m,G,o,len,cuts,ev⟩ := history (Net.empty (n:=n)) P sc
  simp only [Nat.zero_add] at len; subst m
  exact ⟨G,o,by simpa [Net.cuts,Net.run] using cuts,ev⟩

theorem run_at {V : Type*} {n k : ℕ} (G : Net n k) (x : Fin n → Fn V) (y : V → Bool)
    (i : Fin (n+k)) : G.run comb x i y=G.run applyOp (fun j => x j y) i := by
  induction G with
  | empty => rfl
  | add pre op a b ih =>
    cases i using Fin.lastCases with
    | last => simp [Net.run,comb,Node.value,applyOp,ih]
    | cast i => simpa [Net.run] using ih i

def Covered {J V : Type*} [DecidableEq J] {n : ℕ} (x : Fin n → Fn V)
    (z : J → Fin n → Fn V) (sc : Fin n → Finset J) :=
  ∀ j i, bounds (x i) (z j i) ∧ (j∉sc i → z j i=x i)

private theorem comb_bound {V : Type*} {f g h i : Fn V} (o : Bool)
    (a : bounds f h) (b : bounds g i) : bounds (comb o f g) (comb o h i) := by
  intro y; have h := a y; have k := b y
  cases o <;> simp [comb,Node.value] <;> tauto

theorem net_covered {J V : Type*} [DecidableEq J] {n k : ℕ} (G : Net n k)
    {x : Fin n → Fn V} {z : J → Fin n → Fn V} {sc : Fin n → Finset J}
    (h : Covered x z sc) :
    Covered (G.run comb x) (fun j => G.run comb (z j)) (G.run unionOp sc) := by
  induction G with
  | empty => exact h
  | add pre op a b ih =>
    intro j i
    cases i using Fin.lastCases with
    | cast i => simpa [Net.run] using ih j i
    | last =>
      simp only [Net.run,snoc_last,unionOp,Finset.mem_union,not_or]
      refine ⟨comb_bound op (ih j a).1 (ih j b).1,?_⟩
      rintro ⟨na,nb⟩; exact congrArg₂ (comb op) ((ih j a).2 na) ((ih j b).2 nb)

end GateElim.Cuts
#print axioms GateElim.Cuts.net_of_prog
