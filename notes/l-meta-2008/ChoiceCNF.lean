import PrimeClauses
import BlockTools

namespace GateElim.ChoiceCNF
open Reverse Finset Classical
variable {V : Type*} [DecidableEq V] {n : ℕ}

def andCount {n : ℕ} : Prog n→ℕ
  | .ret _ => 0
  | .gate op _ _ t => andCount t + (if op then 0 else 1)

def orCount {n : ℕ} : Prog n→ℕ
  | .ret _ => 0
  | .gate op _ _ t => orCount t + (if op then 1 else 0)

theorem split (P : Prog n) : P.size=andCount P+orCount P := by
  induction P with
  | ret => rfl
  | gate op a b t ih => cases op <;> simp only [Prog.size,andCount,orCount,Bool.false_eq_true,↓reduceIte] <;> omega

/-- Each AND chooses a single operand across *all* uses of its output.
The resulting network consists only of unions, so its output is one clause. -/
def leaves {n : ℕ} (P : Prog n) (v : Fin n→Finset V) : List (Finset V) := match P with
  | .ret i => [v i]
  | .gate true a b t => leaves t (snoc v (v a∪v b))
  | .gate false a b t => leaves t (snoc v (v a))++leaves t (snoc v (v b))

theorem leaves_length (P : Prog n) (v : Fin n→Finset V) : (leaves P v).length=2^(andCount P) := by
  induction P with
  | ret => simp [leaves,andCount]
  | gate op a b t ih => cases op <;> simp [leaves,andCount,ih,pow_succ,Nat.mul_two]

def bit (X D : Finset V) := decide (¬Disjoint D X)

private theorem bit_union (X a b : Finset V) : bit X (a∪b)=(bit X a || bit X b) := by
  apply Bool.eq_iff_iff.mpr; simp [bit]

private theorem tail_mono (t : Prog (n+1)) (x : Fin n→Bool) (a b : Bool) (ab : a=true → b=true) :
    t.eval (snoc x a)=true → t.eval (snoc x b)=true := by
  let X (i : Fin (n+1)) : Fn Unit := const (snoc x a i)
  let Z (i : Fin (n+1)) : Fn Unit := const (snoc x b i)
  have inc := Block.val_mono t X Z (fun i => by
    intro _; cases i using Fin.lastCases <;> simp [X,Z,const] <;> exact ab)
  exact inc (fun _ => false)

theorem represents (P : Prog n) (v : Fin n→Finset V) (X : Finset V) :
    P.eval (fun i => bit X (v i))=true ↔ ∀ D∈leaves P v, ¬Disjoint D X := by
  induction P with
  | ret => simp [Prog.eval,leaves,bit]
  | @gate n op a b t ih =>
    let x (i : Fin n) := bit X (v i)
    have extend (D : Finset V) : (fun i => bit X (snoc v D i))=snoc x (bit X D) := by
      funext i; cases i using Fin.lastCases <;> simp [x]
    cases op with
    | true =>
      rw [leaves,←ih,extend,bit_union]; rfl
    | false =>
      simp only [leaves,List.mem_append,or_imp,forall_and,←ih,extend]
      change t.eval (snoc x (x a && x b))=true ↔ t.eval (snoc x (x a))=true ∧ t.eval (snoc x (x b))=true
      constructor
      · intro h; exact ⟨tail_mono t x _ _ (by simp; tauto) h,tail_mono t x _ _ (by simp <;> tauto) h⟩
      · rintro ⟨ha,hb⟩; cases aa : x a <;> cases bb : x b <;> simp_all

end GateElim.ChoiceCNF

namespace GateElim.Plane
open Desk2008 Desk2008.Fanout PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Reverse ChoiceCNF Finset Classical
attribute [-simp] Fin.natAdd_eq_addNat
variable {q N : ℕ}

theorem forced_choices (I : Fin N→Fin N→Prop) [DecidableRel I] (C : Circuit)
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l)
    (hm : Monotone2 C) (out : C.output<N+N+C.size) (norm : Normal (N+N) C)
    (pos : ∀ p l,I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N→Bool,Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l,I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false) :
    ∃ P, decode (N+N) C.gates C.output=some P ∧ P.size=C.size ∧
      clauses I q ⊆ (leaves P (fun i => {i})).toFinset ∧ (∑ i∈range (q+1),N.choose i)≤2^(andCount P) := by
  obtain ⟨P,par,len,ev⟩ := parse_desk C norm hm out
  let F := (leaves P (fun i => {i})).toFinset
  have eq (X : Finset (Vertex N)) : CNF F X ↔ P.eval (bits X)=true := by
    have single : (fun i => bit X {i})=bits X := by funext i; simp [bit,bits]
    simpa [single,F,CNF] using (represents P (fun i => {i}) X).symm
  have sub : clauses I q⊆F := all_clauses_necessary I ord hd hj F (by
    intro p l inc; apply (eq _).mpr
    have one : bits {left p,right l}=(fun i => decide (i=left p ∨ i=right l)) := by funext i; simp [bits]
    rw [one,ev]; exact pos p l inc) (by
    intro X small free good
    have yes := (eq X).mp good
    have off := (desk_correct q I C hm pos neg).no X (subset_univ _) small free
    rw [ev,off] at yes; contradiction)
  have card := card_le_card sub
  rw [clauses,card_image_of_injective _ (clause_inj I),clause_count] at card
  have cap := List.toFinset_card_le (leaves P (fun i => {i}))
  rw [leaves_length] at cap
  exact ⟨P,par,len,sub,card.trans cap⟩

end GateElim.Plane
#print axioms GateElim.Plane.forced_choices
