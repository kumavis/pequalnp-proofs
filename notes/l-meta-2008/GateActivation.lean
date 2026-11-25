import StrictSources

namespace GateElim.Products
open Reverse Block Finset Classical
variable {V : Type*} {n : ℕ}

def atGate {n : ℕ} (P : Prog n) (off : ℕ) (u : Fin n→Bool) (index : ℕ) : Option Bool :=
  match P with
  | .ret _ => none
  | .gate op a b t =>
    let g := applyOp op (u a) (u b)
    if index=off then some g else atGate t (off+1) (snoc u g) index

private theorem forward_bound (x : Fin n→Fn V) (y : V→Bool) (u : Fin n→Bool)
    (le : ∀ i,x i y=true → u i=true) (op : Bool) (a b : Fin n) (i : Fin (n+1)) :
    forward x op a b i y=true → snoc u (applyOp op (u a) (u b)) i=true := by
  cases i using Fin.lastCases with
  | cast i => simpa [forward] using le i
  | last =>
    have ha := le a; have hb := le b; cases op <;> simp [forward,Node.value,applyOp] <;> tauto

/-- The physical AND is true on any single input dominating the two
separate operand witnesses. Both orientations use the same gate index. -/
theorem activates (P : Prog n) (off : ℕ) (x z : Fin n→Fn V) (g : Birth V)
    (mem : g∈births P off x z) (y v : V→Bool) (u : Fin n→Bool)
    (left : ∀ i,x i y=true → u i=true) (right : ∀ i,z i v=true → u i=true)
    (onA : g.point y=true) (onB : g.line v=true) : atGate P off u g.index=some true := by
  induction P generalizing off with
  | ret => simp [births] at mem
  | @gate n op a b t ih =>
    rcases List.mem_append.mp mem with head|tail
    · cases op with
      | true => simp at head
      | false =>
        simp only [Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false] at head
        rcases head with rfl|rfl
        · simp [atGate,applyOp,left _ onA,right _ onB]
        · simp [atGate,applyOp,left _ onA,right _ onB]
    · have ne : g.index≠off := by have h := (birth_mem t (off+1) _ _ g tail).2.1; omega
      simp only [atGate,ne,↓reduceIte]
      exact ih (off+1) _ _ tail _ (forward_bound x y u left op a b) (forward_bound z v u right op a b)

/-- A genuine source is off on both pure settings. -/
theorem separate_off (P : Prog n) (off : ℕ) (x z : Fin n→Fn V) (g : Birth V)
    (mem : g∈births P off x z) (y v : V→Bool) (yes : g.fires y v) :
    atGate P off (fun i => x i y) g.index=some false ∧ atGate P off (fun i => z i v) g.index=some false := by
  induction P generalizing off with
  | ret => simp [births] at mem
  | @gate n op a b t ih =>
    rcases List.mem_append.mp mem with head|tail
    · cases op with
      | true => simp at head
      | false =>
        simp only [Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false] at head
        rcases head with rfl|rfl <;> obtain ⟨a,b,c,d⟩ := yes <;> simp_all [atGate,applyOp]
    · have ne : g.index≠off := by have h := (birth_mem t (off+1) _ _ g tail).2.1; omega
      simpa only [atGate,ne,↓reduceIte,forward_at] using ih (off+1) _ _ tail

end GateElim.Products
#print axioms GateElim.Products.activates
#print axioms GateElim.Products.separate_off
