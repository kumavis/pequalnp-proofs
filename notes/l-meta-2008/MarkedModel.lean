import Net

namespace GateElim.Cuts
open Reverse Finset Classical
variable {n k : ℕ} {V J : Type*}

def linearEval (op za zb ba bb : Bool) := (za && (op || bb)) || (zb && (op || ba))
def linFn (op : Bool) (za zb ba bb : Fn V) : Fn V := fun y => linearEval op (za y) (zb y) (ba y) (bb y)

/-- A marked gate may use the selected side in both children. Else one branch
of an AND must have a proof with the selected side entirely absent. -/
def Net.row (M : ℕ → Bool) (x z : Fin n → Fn V) : {k : ℕ} → Net n k → Fin (n+k) → Fn V
  | _, .empty => z
  | k+1, .add pre op a b =>
    let r := pre.row M x z
    let base := pre.run comb x
    snoc r (if M k then comb op (r a) (r b) else linFn op (r a) (r b) (base a) (base b))

def tally (M : ℕ→Bool) : ℕ → ℕ
  | 0 => 0
  | k+1 => tally M k+(if M k then 1 else 0)

theorem linear_true (op za zb ba bb : Bool) :
    linearEval op za zb ba bb=true ↔ (za=true ∧ (op=true ∨ bb=true)) ∨ (zb=true ∧ (op=true ∨ ba=true)) := by
  simp [linearEval]

theorem lower_upper (G : Net n k) (M : ℕ→Bool) (x z : Fin n→Fn V) (baseOK : ∀ i, bounds (x i) (z i))
    (i : Fin (n+k)) : bounds (G.run comb x i) (G.row M x z i) ∧ bounds (G.row M x z i) (G.run comb z i) := by
  induction G with
  | empty => exact ⟨baseOK i,fun _ => id⟩
  | @add k pre op a b ih =>
    cases i using Fin.lastCases with
    | cast i => simpa [Net.row,Net.run] using ih i
    | last =>
      simp only [Net.run,Net.row,snoc_last]
      obtain ⟨la,ua⟩ := ih a; obtain ⟨lb,ub⟩ := ih b
      constructor <;> intro y
      all_goals
        have al := la y; have au := ua y; have bl := lb y; have bu := ub y
        cases cut : M k <;> cases op <;> simp [cut,comb,Node.value,linFn,linearEval] <;> tauto

def Prog.model {n : ℕ} (P : Prog n) (M : ℕ→Bool) (start : ℕ) (b z : Fin n→Bool) : Bool :=
  match P with
  | .ret i => z i
  | .gate op a c t => Prog.model t M (start+1) (snoc b (applyOp op (b a) (b c)))
      (snoc z (if M start then applyOp op (z a) (z c) else linearEval op (z a) (z c) (b a) (b c)))

/-- The chronological net preserves the marked evaluation at exactly the
same physical gate positions as the program. -/
theorem mark_history {n k : ℕ} (pre : Net n k) (P : Reverse.Prog (n+k)) :
    ∃ m, ∃ G : Net n m, ∃ i : Fin (n+m), m=k+P.size ∧
      ∀ (V : Type) (M : ℕ→Bool) (x z : Fin n→Fn V) y,
      G.row M x z i y=Prog.model P M k (fun i => pre.run comb x i y) (fun i => pre.row M x z i y) := by
  cases P with
  | ret j => exact ⟨k,pre,j,by simp [Reverse.Prog.size],fun _ _ _ _ _ => rfl⟩
  | gate op a b t =>
    obtain ⟨m,G,i,sz,ev⟩ := mark_history (Net.add pre op a b) t
    refine ⟨m,G,i,by simp only [Reverse.Prog.size]; omega,?_⟩
    intro V M x z y; rw [ev]
    apply congrArg₂ (Prog.model t M (k+1))
    · funext u; cases u using Fin.lastCases <;> simp [Net.run,comb,Node.value,applyOp]
    · funext u; cases u using Fin.lastCases <;> cases e : M k <;> simp [Net.row,comb,Node.value,applyOp,linFn,e]
termination_by P.size
decreasing_by all_goals first | decreasing_tactic | omega | simp_all [Reverse.Prog.size]

end GateElim.Cuts
#print axioms GateElim.Cuts.mark_history
