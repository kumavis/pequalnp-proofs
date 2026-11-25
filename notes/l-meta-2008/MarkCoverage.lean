import MarkedModel

namespace GateElim.Cuts
open Reverse Finset Classical
variable {n : ℕ} {J : Type*} [DecidableEq J]

theorem model_sound (P : Reverse.Prog n) (M : ℕ→Bool) (start : ℕ) (b z u : Fin n→Bool)
    (lower : ∀ i, b i=true → u i=true) (upper : ∀ i, z i=true → u i=true) :
    Prog.model P M start b z=true → P.eval u=true := by
  induction P generalizing start with
  | ret i => exact upper i
  | @gate n op a c t ih =>
    apply ih (start+1)
    · intro i; cases i using Fin.lastCases with
      | cast i => simpa using lower i
      | last =>
        have h := lower a; have k := lower c; cases op <;> simp [applyOp] <;> tauto
    · intro i; cases i using Fin.lastCases with
      | cast i => simpa using upper i
      | last =>
        have ba := lower a; have bb := lower c; have za := upper a; have zz := upper c
        cases cut : M start <;> cases op <;> simp [linearEval,applyOp,cut] <;> tauto

private theorem shift_count (M : ℕ→Bool) (k : ℕ) :
    tally M (k+1)=(if M 0 then 1 else 0)+tally (fun i => M (i+1)) k := by
  induction k with
  | zero => simp [tally]
  | succ k ih => rw [tally,ih]; simp only [tally]; omega

private theorem offset (P : Reverse.Prog n) (M H : ℕ→Bool) (s k : ℕ)
    (same : ∀ j, M (s+j)=H (k+j)) (b z : Fin n→Bool) : Prog.model P M s b z=Prog.model P H k b z := by
  induction P generalizing s k with
  | ret _ => rfl
  | gate op a c t ih =>
    have now : M s=H k := by simpa using same 0
    simp only [Prog.model,now]; apply ih
    intro j; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using same (j+1)

/-- Mark exactly the AND gates whose two input scopes meet. This is sufficient
to preserve the output at every legal or illegal singleton-selector setting. -/
theorem syntactic_marks (P : Reverse.Prog n) (sc : Fin n→Finset J) :
    ∃ M : ℕ→Bool, tally M P.size=ProgCuts P sc ∧
      ∀ (j : J) (b z : Fin n→Bool), (∀ i, b i=true → z i=true) →
      (∀ i, j∉sc i → z i=b i) → Prog.model P M 0 b z=P.eval z := by
  classical
  induction P with
  | ret o => exact ⟨fun _ => false,rfl,fun _ _ _ _ _ => rfl⟩
  | @gate n op a c t ih =>
    obtain ⟨tail,count,exactly⟩ := ih (snoc sc (sc a∪sc c))
    let flag := decide (clash op (sc a) (sc c))
    let M : ℕ→Bool := fun k => match k with | 0 => flag | j+1 => tail j
    refine ⟨M,?_,?_⟩
    · change tally M (t.size+1)=_
      rw [shift_count]
      change (if flag then 1 else 0)+tally tail t.size=_
      simp [ProgCuts,flag,count]
    · intro j b z le agree
      let B := snoc b (applyOp op (b a) (b c))
      let Z := snoc z (applyOp op (z a) (z c))
      have edge : (if M 0 then applyOp op (z a) (z c) else linearEval op (z a) (z c) (b a) (b c)) =
          applyOp op (z a) (z c) := by
        by_cases bad : clash op (sc a) (sc c)
        · simp [M,flag,bad]
        · simp only [M,flag,bad,decide_false,Bool.false_eq_true,↓reduceIte]
          have da := le a; have dc := le c
          cases op with
          | true => simp [linearEval,applyOp]
          | false =>
            have dis : Disjoint (sc a) (sc c) := by simpa [clash] using bad
            have one : z a=b a ∨ z c=b c := by
              by_cases ha : j∈sc a
              · exact Or.inr (agree c (fun hc => Finset.disjoint_left.mp dis ha hc))
              · exact Or.inl (agree a ha)
            rcases one with e|e <;> cases aa : z a <;> cases cc : z c <;> simp_all [linearEval,applyOp] <;> grind
      change Prog.model t M 1 B (snoc z _) = t.eval Z
      rw [edge,offset t M tail 1 0 (by intro i; rw [Nat.zero_add,Nat.add_comm])]
      apply exactly j B Z
      · intro i; cases i using Fin.lastCases with
        | cast i => simpa [B,Z] using le i
        | last => have da := le a; have dc := le c; cases op <;> simp [B,Z,applyOp] <;> tauto
      · intro i; cases i using Fin.lastCases with
        | cast i => simpa [B,Z] using agree i
        | last => simp only [snoc_last,Finset.mem_union,not_or,B,Z]; rintro ⟨ha,hc⟩; rw [agree a ha,agree c hc]

end GateElim.Cuts
#print axioms GateElim.Cuts.syntactic_marks
