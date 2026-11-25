import BlockTools

namespace GateElim.MergeTrace
open Reverse Finset Classical
variable {A : Type*} [DecidableEq A] {n : ℕ}

/-- One negative evaluation and a set of positive tests on which a wire fires. -/
structure Signal (A : Type*) where
  neg : Bool
  acc : Finset A

def gate (op : Bool) (a b : Signal A) : Signal A :=
  ⟨applyOp op a.neg b.neg,if op then a.acc∪b.acc else a.acc∩b.acc⟩

def merge (op : Bool) (a b : Signal A) : Prop :=
  op=true ∧ a.neg=false ∧ b.neg=false ∧ ¬a.acc⊆b.acc ∧ ¬b.acc⊆a.acc
instance (op : Bool) (a b : Signal A) : Decidable (merge op a b) := by unfold merge; infer_instance

def run {n : ℕ} (P : Prog n) (w : Fin n→Signal A) : Signal A := match P with
  | .ret i => w i
  | .gate op a b t => run t (snoc w (gate op (w a) (w b)))

def count {n : ℕ} (P : Prog n) (w : Fin n→Signal A) : ℕ := match P with
  | .ret _ => 0
  | .gate op a b t => (if merge op (w a) (w b) then 1 else 0)+count t (snoc w (gate op (w a) (w b)))

theorem truth (P : Prog n) (w : Fin n→Signal A) :
    (run P w).neg=P.eval (fun i => (w i).neg) ∧
    ∀ v, v∈(run P w).acc ↔ P.eval (fun i => decide (v∈(w i).acc))=true := by
  induction P with
  | ret i => simp [run,Prog.eval]
  | @gate n op a b t ih =>
    let W := snoc w (gate op (w a) (w b))
    have e : (fun i => (W i).neg)=snoc (fun i => (w i).neg) (applyOp op (w a).neg (w b).neg) := by
      funext i; cases i using Fin.lastCases <;> simp [W,gate]
    constructor
    · exact (ih W).1.trans (congrArg t.eval e)
    · intro v
      have eq : (fun i => decide (v∈(W i).acc)) = snoc (fun i => decide (v∈(w i).acc))
          (applyOp op (decide (v∈(w a).acc)) (decide (v∈(w b).acc))) := by
        funext i; cases i using Fin.lastCases <;> cases op <;> simp [W,gate,applyOp]
      change v∈(run t W).acc ↔ t.eval _=true
      rw [(ih W).2,eq]

private theorem one (op : Bool) (a b : Signal A) (off : (gate op a b).neg=false)
    (cheap : ¬merge op a b) :
    (a.neg=false ∧ (gate op a b).acc⊆a.acc) ∨ (b.neg=false ∧ (gate op a b).acc⊆b.acc) := by
  cases op with
  | false =>
    have z : a.neg=false ∨ b.neg=false := by cases h : a.neg <;> simp_all [gate,applyOp]
    exact z.elim (fun h => Or.inl ⟨h,inter_subset_left⟩) (fun h => Or.inr ⟨h,inter_subset_right⟩)
  | true =>
    obtain ⟨ha,hb⟩ : a.neg=false ∧ b.neg=false := by simpa [gate,applyOp] using off
    by_cases le : a.acc⊆b.acc
    · exact Or.inr ⟨hb,union_subset le Subset.rfl⟩
    · have rev : b.acc⊆a.acc := by by_contra h; exact cheap ⟨rfl,ha,hb,le,h⟩
      exact Or.inl ⟨ha,union_subset Subset.rfl rev⟩

/-- Tracing back through a stable AND needs one child even if both children
use the same inputs. An OR needs both only when their positive sets differ
in both directions. Every counted gate is a distinct physical occurrence. -/
theorem frontier (P : Prog n) (w : Fin n→Signal A) (off : (run P w).neg=false) :
    ∃ D : Finset (Fin n), D.card≤count P w+1 ∧ (∀ i∈D,(w i).neg=false) ∧
      ∀ v∈(run P w).acc, ∃ i∈D, v∈(w i).acc := by
  induction P with
  | ret i => exact ⟨{i},by simp [count],fun j hj => (mem_singleton.mp hj) ▸ off,fun v hv => ⟨i,by simp,hv⟩⟩
  | @gate n op a b t ih =>
    let W := snoc w (gate op (w a) (w b))
    obtain ⟨D,small,stable,cover⟩ := ih W off
    let U := univ.filter fun i : Fin n => i.castSucc∈D
    have up : U.image Fin.castSucc=D.erase (Fin.last n) := by
      ext i; cases i using Fin.lastCases <;> simp [U,Fin.castSucc_ne_last]
    have card : U.card=(D.erase (Fin.last n)).card := by rw [←up,card_image_of_injective _ (Fin.castSucc_injective _)]
    have old (i : Fin n) (hi : i∈U) : (w i).neg=false := by
      simpa [W] using stable i.castSucc (mem_filter.mp hi).2
    have trace (v : A) (hv : v∈(run t W).acc) :
        (∃ i∈U, v∈(w i).acc) ∨ (Fin.last n∈D ∧ v∈(gate op (w a) (w b)).acc) := by
      obtain ⟨i,hi,on⟩ := cover v hv
      cases i using Fin.lastCases with
      | last => exact Or.inr ⟨hi,by simpa [W] using on⟩
      | cast i => exact Or.inl ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩,by simpa [W] using on⟩
    change ∃ E : Finset (Fin n), E.card≤(if merge op (w a) (w b) then 1 else 0)+count t W+1 ∧ _
    by_cases use : Fin.last n∈D
    · have spent := card_erase_add_one use
      have on : (gate op (w a) (w b)).neg=false := by simpa [W] using stable _ use
      by_cases paid : merge op (w a) (w b)
      · have opOn := paid.1; subst op
        have ha := paid.2.1; have hb := paid.2.2.1
        refine ⟨insert a (insert b U),?_,?_,?_⟩
        · rw [if_pos (by assumption : merge true (w a) (w b))]
          have x := card_insert_le a (insert b U); have y := card_insert_le b U; omega
        · intro i hi; rcases mem_insert.mp hi with rfl|hi; exact ha
          rcases mem_insert.mp hi with rfl|hi; exact hb; exact old _ hi
        · intro v hv; rcases trace v hv with ⟨i,hi,h⟩|⟨_,h⟩
          · exact ⟨i,mem_insert_of_mem (mem_insert_of_mem hi),h⟩
          · rcases mem_union.mp h with h|h
            · exact ⟨a,by simp,h⟩
            · exact ⟨b,by simp,h⟩
      · obtain ⟨i,st,sub⟩ : ∃ i,(w i).neg=false ∧ (gate op (w a) (w b)).acc⊆(w i).acc := by
          rcases one op (w a) (w b) on paid with h|h
          · exact ⟨a,h⟩
          · exact ⟨b,h⟩
        refine ⟨insert i U,?_,?_,?_⟩
        · rw [if_neg paid]; have h := card_insert_le i U; omega
        · intro j hj; rcases mem_insert.mp hj with rfl|h; exact st; exact old _ h
        · intro v hv; rcases trace v hv with ⟨j,hj,h⟩|⟨_,h⟩
          · exact ⟨j,mem_insert_of_mem hj,h⟩
          · exact ⟨i,by simp,sub h⟩
    · refine ⟨U,?_,old,?_⟩
      · rw [card,erase_eq_of_notMem use]; omega
      · intro v hv; exact (trace v hv).resolve_right (fun h => use h.1)

theorem budget (P : Prog n) (w : Fin n→Signal A) (off : (run P w).neg=false)
    (atom : ∀ i,(w i).neg=false → (w i).acc.card≤1) :
    (run P w).acc.card≤count P w+1 := by
  obtain ⟨D,l,st,cover⟩ := frontier P w off
  have sub : (run P w).acc⊆D.biUnion (fun i => (w i).acc) := fun _ h => mem_biUnion.mpr (cover _ h)
  have sum := Finset.sum_le_sum (s:=D) (fun i hi => atom i (st i hi))
  have card := Finset.card_biUnion_le (s:=D) (t:=fun i => (w i).acc)
  have incl := card_le_card sub
  simp only [sum_const,smul_eq_mul,mul_one] at sum
  omega

end GateElim.MergeTrace
#print axioms GateElim.MergeTrace.budget
