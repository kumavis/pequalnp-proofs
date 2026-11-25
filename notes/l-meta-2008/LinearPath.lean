import Reverse

namespace GateElim.Reverse
open Classical
variable {V J : Type*} {n : ℕ}

/-- The unique marked input occurrence traverses one child of an AND. Its
sibling must have a derivation with no marked inputs at all. -/
def pass (op a b : Bool) (da db : Prop) : Prop :=
  (da ∧ (op=true ∨ b=true)) ∨ (db ∧ (op=true ∨ a=true))

def Prog.path : {n : ℕ} → Prog n → (Fin n → Fn V) → (V → Bool) → (Fin n → Prop) → Prop
  | _, .ret j, _, _, d => d j
  | _, .gate op a b t, x, y, d =>
    t.path (forward x op a b) y (snoc d (pass op (x a y) (x b y) (d a) (d b)))

theorem updated {n : ℕ} (x : Fin n → Fn V) (w : Fin (n+1) → Fn V) (op : Bool)
    (a b i : Fin n) (y : V → Bool) :
    update op a b x w i y=true ↔ w i.castSucc y=true ∨
      (i=a ∧ w (Fin.last n) y=true ∧ (op=true ∨ x b y=true)) ∨
      (i=b ∧ w (Fin.last n) y=true ∧ (op=true ∨ x a y=true)) := by
  by_cases ia : i=a <;> by_cases ib : i=b <;> cases op <;>
    simp_all [update,merge,product,Node.value] <;> tauto

theorem path_iff (p : Prog n) (x : Fin n → Fn V) (y : V → Bool) (d : Fin n → Prop) :
    p.path x y d ↔ ∃ i, d i ∧ p.weights x i y=true := by
  induction p with
  | ret j => simp [Prog.path,Prog.weights,const]
  | @gate n op a b t ih =>
    let w := t.weights (forward x op a b)
    rw [Prog.path,ih]
    change (∃ j, snoc d _ j ∧ w j y=true) ↔ ∃ i, d i ∧ update op a b x w i y=true
    constructor
    · rintro ⟨j,dj,on⟩
      cases j using Fin.lastCases with
      | last =>
        rw [snoc_last] at dj
        rcases dj with ⟨da,p⟩|⟨db,p⟩
        · exact ⟨a,da,(updated ..).mpr (Or.inr (Or.inl ⟨rfl,on,p⟩))⟩
        · exact ⟨b,db,(updated ..).mpr (Or.inr (Or.inr ⟨rfl,on,p⟩))⟩
      | cast i => exact ⟨i,by simpa using dj,(updated ..).mpr (Or.inl on)⟩
    · rintro ⟨i,di,wins⟩
      rcases (updated ..).mp wins with old|⟨rfl,has,edge⟩|⟨rfl,has,edge⟩
      · exact ⟨i.castSucc,by simpa using di,old⟩
      · exact ⟨Fin.last n,by rw [snoc_last]; exact Or.inl ⟨di,edge⟩,has⟩
      · exact ⟨Fin.last n,by rw [snoc_last]; exact Or.inr ⟨di,edge⟩,has⟩

private theorem both_sound (op A B a b : Bool) (da db : Prop)
    (sa : A=true → a=true) (sb : B=true → b=true)
    (va : da → a=true) (vb : db → b=true) :
    (applyOp op A B=true → applyOp op a b=true) ∧
    (pass op A B da db → applyOp op a b=true) := by
  cases op <;> simp_all [applyOp,pass] <;> tauto

theorem path_sound (p : Prog n) (x : Fin n → Fn V) (y : V → Bool)
    (d : Fin n → Prop) (z : Fin n → Bool)
    (baseOK : ∀ i, x i y=true → z i=true) (tagOK : ∀ i, d i → z i=true) :
    p.path x y d → p.eval z=true := by
  induction p with
  | ret i => exact tagOK i
  | @gate n op a b t ih =>
    let both := both_sound op (x a y) (x b y) (z a) (z b) (d a) (d b)
      (baseOK a) (baseOK b) (tagOK a) (tagOK b)
    apply ih (forward x op a b) _ (snoc z (applyOp op (z a) (z b)))
    · intro i; cases i using Fin.lastCases with
      | last => simpa [forward,applyOp,Node.value] using both.1
      | cast i => simpa [forward] using baseOK i
    · intro i; cases i using Fin.lastCases with
      | last => simpa using both.2
      | cast i => simpa using tagOK i

def Prog.disjoint [DecidableEq J] : {n : ℕ} → Prog n → (Fin n → Finset J) → Prop
  | _, .ret _, _ => True
  | _, .gate op a b t, sc =>
    (op=false → Disjoint (sc a) (sc b)) ∧ t.disjoint (snoc sc (sc a ∪ sc b))

private theorem both_complete (op A B a b : Bool) (da db : Prop)
    (sa : a=true → A=true ∨ da) (sb : b=true → B=true ∨ db)
    (separate : op=false → da → db → False) :
    applyOp op a b=true → applyOp op A B=true ∨ pass op A B da db := by
  cases op <;> simp_all [applyOp,pass] <;> tauto

theorem forward_at (x : Fin n → Fn V) (op : Bool) (a b : Fin n) (y : V → Bool) :
    (fun j => forward x op a b j y) = snoc (fun i => x i y) (applyOp op (x a y) (x b y)) := by
  funext i; cases i using Fin.lastCases <;> simp [forward,Node.value,applyOp]

theorem path_complete [DecidableEq J] (mark : J) (p : Prog n) (x : Fin n → Fn V) (y : V → Bool)
    (d : Fin n → Prop) (z : Fin n → Bool) (sc : Fin n → Finset J)
    (sep : p.disjoint sc) (cover : ∀ i, z i=true → x i y=true ∨ d i)
    (marked : ∀ i, d i → mark∈sc i) :
    p.eval z=true → p.eval (fun i => x i y)=true ∨ p.path x y d := by
  induction p with
  | ret i => exact cover i
  | @gate n op a b t ih =>
    let step := pass op (x a y) (x b y) (d a) (d b)
    have both := both_complete op (x a y) (x b y) (z a) (z b) (d a) (d b)
      (cover a) (cover b) (fun isAnd da db => Finset.disjoint_left.mp (sep.1 isAnd) (marked a da) (marked b db))
    have hs (i : Fin (n+1)) : snoc z (applyOp op (z a) (z b)) i=true →
        forward x op a b i y=true ∨ snoc d step i := by
      cases i using Fin.lastCases with
      | last => simpa [forward,Node.value,applyOp,step] using both
      | cast i => simpa [forward] using cover i
    have hm (i : Fin (n+1)) : snoc d step i → mark∈snoc sc (sc a ∪ sc b) i := by
      cases i using Fin.lastCases with
      | last =>
        simp only [snoc_last,Finset.mem_union]; rintro (⟨ha,_⟩|⟨hb,_⟩)
        · exact Or.inl (marked a ha)
        · exact Or.inr (marked b hb)
      | cast i => simpa using marked i
    have r := ih (forward x op a b) (snoc d step) (snoc z (applyOp op (z a) (z b)))
      (snoc sc (sc a ∪ sc b)) sep.2 hs hm
    simpa only [Prog.eval,Prog.path,forward_at,step] using r

end GateElim.Reverse
#print axioms GateElim.Reverse.path_complete
#print axioms GateElim.Reverse.path_iff
