import BatchGates
import MarkedModel

namespace GateElim.Cuts
open Reverse Finset Classical
variable {J V : Type*} [Fintype J] [DecidableEq J] {n k : ℕ}

/-- All base values and an exceptional gate's row values are available when
the reverse pass needs them. -/
def Paid (M : ℕ→Bool) (x : Fin n → Fn V) (z : J → Fin n → Fn V) (S : Set (Fn V)) :
    {k : ℕ} → Net n k → Prop
  | _, .empty => True
  | k+1, .add pre op a b =>
    Paid M x z S pre ∧ (M k=true →
      ∀ j, comb op (pre.row M x (z j) a) (pre.row M x (z j) b) ∈ S)

theorem paid_lift (G : Net n k) {S T : Set (Fn V)} {z : J → Fin n → Fn V} {x : Fin n→Fn V} {M : ℕ→Bool}
    (h : Paid M x z S G) (sub : S⊆T) : Paid M x z T G := by
  induction G with
  | empty => trivial
  | add _ _ _ _ ih => exact ⟨ih h.1,fun clash j => sub (h.2 clash j)⟩

def form {m : ℕ} (w z : Fin m → Fn V) (bias : Fn V) (y : V → Bool) : Prop :=
  bias y=true ∨ ∃ i, w i y=true ∧ z i y=true

private theorem split_form {m : ℕ} (w : Fin (m+1) → Fn V) (z : Fin m → Fn V)
    (v bias : Fn V) (y : V → Bool) :
    form w (snoc z v) bias y ↔ form (fun i => w i.castSucc) z bias y ∨
      (w (Fin.last m) y=true ∧ v y=true) := by
  simp only [form,Fin.exists_fin_succ',snoc_last,snoc_old]
  exact or_assoc.symm

private theorem combine_valid (op : Bool) (a b A B : Bool)
    (ha : A=true → a=true) (hb : B=true → b=true)
    (ordinary : op=false → a=A ∨ b=B) :
    applyOp op a b=true ↔ (a=true ∧ (op=true ∨ B=true)) ∨ (b=true ∧ (op=true ∨ A=true)) := by
  cases op <;> simp_all [applyOp] <;> grind

private theorem reverse_form {m : ℕ} (x z : Fin m → Fn V) (op : Bool) (a b : Fin m)
    (w : Fin (m+1) → Fn V) (bias : Fn V) (y : V → Bool)
    (v : Fn V)
    (step : v y=true ↔ (z a y=true ∧ (op=true ∨ x b y=true)) ∨ (z b y=true ∧ (op=true ∨ x a y=true))) :
    form w (snoc z v) bias y ↔ form (update op a b x w) z bias y := by
  rw [split_form]
  rw [step]
  constructor
  · rintro (orig|⟨vw,⟨ha,pa⟩|⟨hb,pb⟩⟩)
    · rcases orig with bias|⟨i,wi,zi⟩
      · exact Or.inl bias
      · exact Or.inr ⟨i,(updated ..).mpr (Or.inl wi),zi⟩
    · exact Or.inr ⟨a,(updated ..).mpr (Or.inr (Or.inl ⟨rfl,vw,pa⟩)),ha⟩
    · exact Or.inr ⟨b,(updated ..).mpr (Or.inr (Or.inr ⟨rfl,vw,pb⟩)),hb⟩
  · rintro (bias|⟨i,wi,zi⟩)
    · exact Or.inl (Or.inl bias)
    rcases (updated ..).mp wi with old|⟨rfl,h,ok⟩|⟨rfl,h,ok⟩
    · exact Or.inl (Or.inr ⟨_,old,zi⟩)
    · exact Or.inr ⟨h,Or.inl ⟨zi,ok⟩⟩
    · exact Or.inr ⟨h,Or.inr ⟨zi,ok⟩⟩

/-- Reversing an ordinary gate costs at most four scalar gates. Reversing a
cut gate costs two gates per requested row. -/
theorem sweep (G : Net n k) (x : Fin n → Fn V) (z : J → Fin n → Fn V) (M : ℕ→Bool)
    (S : Set (Fn V)) (has : ∀ i, G.run comb x i∈S)
    (paid : Paid M x z S G)
    (w : Fin (n+k) → Fn V) (bias : J → Fn V) (wa : ∀ i, w i∈S) (ba : ∀ j, bias j∈S) :
    ∃ gs : List (Node V), ∃ u : Fin n → Fn V, ∃ c : J → Fn V,
      gs.length≤4*k+2*(tally M k)*Fintype.card J ∧ Built S gs ∧
      (∀ i, u i∈pool S gs) ∧ (∀ j, c j∈pool S gs) ∧
      (∀ j y, form w (G.row M x (z j)) (bias j) y ↔ form u (z j) (c j) y) ∧
      (∀ y, form u x (const false) y → form w (G.run comb x) (const false) y) ∧
      ∀ j, bounds (bias j) (c j) := by
  classical
  induction G generalizing S bias with
  | empty => exact ⟨[],w,bias,by simp [tally],True.intro,wa,ba,(fun _ _ => Iff.rfl),(fun _ h => h),fun _ _ h => h⟩
  | @add k pre op a b ih =>
    have prev (i : Fin (n+k)) : pre.run comb x i∈S := by simpa [Net.run] using has i.castSucc
    let last := Fin.last (n+k)
    let val (j : J) := comb op (pre.row M x (z j) a) (pre.row M x (z j) b)
    by_cases bad : M k=true
    · obtain ⟨gs,gl,gb,prod⟩ := batch false (fun _ : J => w last) val S (fun j => ⟨wa _,paid.2 bad j⟩)
      let term (j : J) := comb false (w last) (val j)
      obtain ⟨hs,hl,hb,add⟩ := batch true bias term (pool S gs) (fun j => ⟨pool_grows _ _ (ba j),prod j⟩)
      let T := pool (pool S gs) hs
      have lift : S⊆T := Set.Subset.trans (pool_grows _ _) (pool_grows _ _)
      obtain ⟨ks,u,c,kl,kb,ua,ca,eq,scalar,inc⟩ := ih T (fun i => lift (prev i)) (paid_lift pre paid.1 lift)
        (fun i => w i.castSucc) (fun j => comb true (bias j) (term j)) (fun i => lift (wa _)) add
      refine ⟨gs++hs++ks,u,c,?_,?_,?_,?_,?_,?_,?_⟩
      · simp only [List.length_append,tally,bad,↓reduceIte,Nat.mul_add,Nat.add_mul,mul_one,one_mul]; omega
      · apply build_append (build_append gb hb); rwa [pool_append]
      · simpa only [pool_append,T] using ua
      · simpa only [pool_append,T] using ca
      · intro j y; apply Iff.trans _ (eq j y)
        rw [Net.row,split_form]
        simp only [bad,↓reduceIte,form,term,val,last,comb,Node.value,↓reduceIte,Bool.or_eq_true,Bool.and_eq_true]
        grind
      · intro y h; rw [Net.run,split_form]; exact Or.inl (scalar y h)
      · intro j y on; apply inc j y; simp [comb,Node.value,on]
    · obtain ⟨gs,gl,gb,add⟩ := backward S op a b (pre.run comb x) w prev wa
      let T := pool S gs
      have lift : S⊆T := pool_grows _ _
      obtain ⟨ks,u,c,kl,kb,ua,ca,eq,scalar,inc⟩ := ih T (fun i => lift (prev i)) (paid_lift pre paid.1 lift)
        (update op a b (pre.run comb x) w) bias add (fun j => lift (ba j))
      refine ⟨gs++ks,u,c,?_,build_append gb kb,?_,?_,?_,?_,inc⟩
      · simp [List.length_append,tally,bad]; omega
      · simpa only [pool_append,T] using ua
      · simpa only [pool_append,T] using ca
      · intro j y; apply Iff.trans _ (eq j y)
        simp only [Net.row,bad,↓reduceIte]
        apply reverse_form
        exact linear_true ..
      · intro y h
        apply (reverse_form (pre.run comb x) (pre.run comb x) op a b w (const false) y
          (comb op (pre.run comb x a) (pre.run comb x b)) ?_).mpr (scalar y h)
        exact combine_valid op _ _ _ _ id id (fun _ => Or.inl rfl)

end GateElim.Cuts
#print axioms GateElim.Cuts.sweep
