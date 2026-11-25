import SparseRows

namespace GateElim
namespace Reverse
open Classical

/-- Input wire numbers are preserved when a new gate is appended. -/
inductive Prog : ℕ → Type
  | ret {n : ℕ} (out : Fin n) : Prog n
  | gate {n : ℕ} (op : Bool) (a b : Fin n) (tail : Prog (n+1)) : Prog n

def Prog.size {n : ℕ} : Prog n → ℕ
  | .ret _ => 0
  | .gate _ _ _ rest => rest.size+1

def snoc {α : Type*} {n : ℕ} (v : Fin n → α) (last : α) : Fin (n+1) → α :=
  Fin.lastCases last v

@[simp] theorem snoc_last {α : Type*} {n : ℕ} (v : Fin n → α) (x : α) :
    snoc v x (Fin.last n)=x := Fin.lastCases_last ..
@[simp] theorem snoc_old {α : Type*} {n : ℕ} (v : Fin n → α) (x : α) (i : Fin n) :
    snoc v x i.castSucc=v i := Fin.lastCases_castSucc ..

def applyOp (op a b : Bool) := if op then a || b else a && b

def Prog.eval {n : ℕ} : Prog n → (Fin n → Bool) → Bool
  | .ret i, x => x i
  | .gate op a b t, x => t.eval (snoc x (applyOp op (x a) (x b)))

def forward {V : Type*} {n : ℕ} (x : Fin n → Fn V) (op : Bool) (a b : Fin n) :=
  snoc x (Node.value ⟨op,x a,x b⟩)

def product {V : Type*} (op : Bool) (w sibling : Fn V) : Fn V :=
  if op then w else (Node.mk false w sibling).value

def merge {V : Type*} (f g : Fn V) := (Node.mk true f g).value

def update {V : Type*} {n : ℕ} (op : Bool) (a b : Fin n) (x : Fin n → Fn V)
    (w : Fin (n+1) → Fn V) (i : Fin n) : Fn V :=
  if i=a then merge (w i.castSucc) (product op (w (Fin.last n)) (x b))
  else if i=b then merge (w i.castSucc) (product op (w (Fin.last n)) (x a))
  else w i.castSucc

/-- Each output is true if a path from that input reaches the designated root
with all AND-siblings true on the chosen base assignment. -/
def Prog.weights {V : Type*} {n : ℕ} : Prog n → (Fin n → Fn V) → Fin n → Fn V
  | .ret j, _, i => const (decide (i=j))
  | .gate op a b t, x, i => update op a b x (t.weights (forward x op a b)) i

def pool {V : Type*} (S : Set (Fn V)) : List (Node V) → Set (Fn V)
  | [] => S
  | g::gs => pool (insert g.value S) gs

def Built {V : Type*} (S : Set (Fn V)) : List (Node V) → Prop
  | [] => True
  | g::gs => g.a∈S ∧ g.b∈S ∧ Built (insert g.value S) gs

theorem pool_grows {V : Type*} (S : Set (Fn V)) (gs : List (Node V)) :
    S ⊆ pool S gs := by
  induction gs generalizing S with
  | nil => rfl
  | cons g gs ih => exact Set.Subset.trans (Set.subset_insert ..) (ih _)

theorem ready_of_built {V : Type*} {S : Set (Fn V)} {gs : List (Node V)} {f : Fn V}
    (h : Built S gs) (avail : f∈pool S gs) : Ready S gs f := by
  induction gs generalizing S with
  | nil => exact avail
  | cons g gs ih => exact ⟨h.1,h.2.1,ih h.2.2 avail⟩

theorem pool_append {V : Type*} (S : Set (Fn V)) (gs hs : List (Node V)) :
    pool S (gs++hs)=pool (pool S gs) hs := by
  induction gs generalizing S with
  | nil => rfl
  | cons g gs ih => exact ih _

theorem build_append {V : Type*} {S : Set (Fn V)} {gs hs : List (Node V)}
    (h : Built S gs) (r : Built (pool S gs) hs) : Built S (gs++hs) := by
  induction gs generalizing S with
  | nil => exact r
  | cons g gs ih => exact ⟨h.1,h.2.1,ih h.2.2 r⟩

/-- A gate needs at most two products and two ORs in the reverse pass. -/
theorem backward {V : Type*} {n : ℕ} (S : Set (Fn V)) (op : Bool) (a b : Fin n)
    (x : Fin n → Fn V) (w : Fin (n+1) → Fn V) (xb : ∀ i, x i∈S) (wb : ∀ i, w i∈S) :
    ∃ gs : List (Node V), gs.length≤4 ∧ Built S gs ∧ ∀ i, update op a b x w i ∈ pool S gs := by
  let gateA := Node.mk false (w (Fin.last n)) (x b)
  let gateB := Node.mk false (w (Fin.last n)) (x a)
  let useA := Node.mk true (w a.castSucc) (product op (w (Fin.last n)) (x b))
  let useB := Node.mk true (w b.castSucc) (product op (w (Fin.last n)) (x a))
  let gs := [gateA,gateB,useA,useB]
  refine ⟨gs,by simp [gs],?_,?_⟩
  · simp only [gs,Built,Set.mem_insert_iff,gateA,gateB,useA,useB]
    cases op <;> simp [product,xb,wb]
  · intro i
    by_cases ia : i=a
    · subst i; simp [update,gs,pool,merge,useA]
    by_cases ib : i=b
    · subst i; simp [update,ia,gs,pool,merge,useB]
    · simp [update,ia,ib,gs,pool,wb]

/-- The base values need one forward gate per original gate, and the same
reverse circuit simultaneously supplies all input weights. -/
theorem compile_weights {V : Type*} {n : ℕ} (p : Prog n) (x : Fin n → Fn V)
    (S : Set (Fn V)) (available : ∀ i, x i∈S) (cs : ∀ b, const b∈S) :
    ∃ gs : List (Node V), gs.length≤5*p.size ∧ Built S gs ∧ ∀ i, p.weights x i ∈ pool S gs := by
  induction p generalizing S with
  | ret j =>
    exact ⟨[],by simp [Prog.size],True.intro,fun i => cs _⟩
  | @gate n op a b tail ih =>
    let g : Node V := ⟨op,x a,x b⟩
    let T := insert g.value S
    have av (i : Fin (n+1)) : forward x op a b i∈T := by
      cases i using Fin.lastCases with
      | last => simp [forward,T,g]
      | cast i => simp [forward,T,available]
    obtain ⟨gs,len,built,w⟩ := ih (forward x op a b) T av (fun z => Set.mem_insert_of_mem _ (cs z))
    obtain ⟨hs,hlen,hbuilt,done⟩ := backward (pool T gs) op a b x _ (fun i =>
      pool_grows T gs (Set.mem_insert_of_mem _ (available i))) w
    refine ⟨g::(gs++hs),?_,⟨available _,available _,build_append built hbuilt⟩,?_⟩
    · simp [Prog.size]; omega
    · intro i; change update op a b x (tail.weights (forward x op a b)) i ∈ pool T (gs++hs)
      rw [pool_append]; exact done i

theorem common_outputs {V : Type*} {n : ℕ} (p : Prog n) (x : Fin n → Fn V)
    (S : Set (Fn V)) (available : ∀ i, x i∈S) (cs : ∀ b, const b∈S) :
    ∃ gs : List (Node V), gs.length≤5*p.size ∧ ∀ i, Ready S gs (p.weights x i) := by
  obtain ⟨gs,cost,built,w⟩ := compile_weights p x S available cs
  exact ⟨gs,cost,fun i => ready_of_built built (w i)⟩

end Reverse
end GateElim
#print axioms GateElim.Reverse.common_outputs
