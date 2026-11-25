import Port

namespace GateElim.Port
open Reverse Finset Classical
variable {V : Type*} {n : ℕ}
def below (x y : V → Bool) := ∀ v, x v=true → y v=true
def inc (f : Fn V) := ∀ x y, below x y → f x=true → f y=true
def guard (h : Option (Fn V)) : Fn V := h.getD (const false)
def fee {α : Type*} (h : Option α) : ℕ := if h.isSome then 1 else 0

def tag (P : Prog n) (z : Fin n → Fn V) (i : Fin n) (h : Fn V) : Fn V :=
  fun y => P.eval (Function.update (fun j => z j y) i (h y))

structure Sample (pos neg : (V → Bool) → Prop) (off on : Fn V) : Prop where
  yes : ∀ y, pos y → off y=true
  no : ∀ y, neg y → off y=false
  witness : ∀ y, neg y → ∃ z, neg z ∧ below y z ∧ on z=true
  silent : ∃ y, on y=false

theorem inc_comb {f g : Fn V} (o : Bool) (a : inc f) (b : inc g) : inc (Cuts.comb o f g) := by
  intro x y le
  have ha := a _ _ le; have hb := b _ _ le
  cases o <;> simp [Cuts.comb,Node.value] <;> tauto

theorem masked {P : Prog n} {z : Fin n → Fn V} {i : Fin n} {h : Fn V} {pos neg}
    (sample : Sample pos neg (tag P z i h) (tag P z i (const true))) (mono : inc h) :
    ∀ y, neg y → h y=false := by
  intro y hy; apply Bool.eq_false_iff.mpr; intro yes
  obtain ⟨t,nt,le,on⟩ := sample.witness _ hy
  have ht := mono _ _ le yes
  have off := sample.no _ nt
  simp_all [tag,const]

theorem dependence {P : Prog n} {z : Fin n → Fn V} {i : Fin n} {h : Fn V} {pos neg}
    (sample : Sample pos neg (tag P z i h) (tag P z i (const true))) (someNeg : ∃ x, neg x) :
    ∃ t, tag P z i h t≠tag P z i (const true) t := by
  obtain ⟨v,hv⟩ := someNeg; obtain ⟨t,nt,_,on⟩ := sample.witness _ hv
  exact ⟨t,by rw [sample.no _ nt,on]; decide⟩

theorem not_return {P : Prog n} {z : Fin n → Fn V} {i : Fin n} {h : Fn V} {pos neg}
    (sample : Sample pos neg (tag P z i h) (tag P z i (const true))) : ¬returns P i := by
  intro out; obtain ⟨y,silent⟩ := sample.silent
  simp [tag,returns_eval P i out,const] at silent

theorem tag_zero (P : Prog n) (z : Fin n → Fn V) (i : Fin n) (zero : z i=const false)
    (h : Fn V) (y : V→Bool) (hy : h y=false) : tag P z i h y=fn P z y := by
  unfold tag fn; congr 1; funext j
  by_cases eq : j=i <;> simp [eq,hy,zero,const]

theorem normal_step (op : Bool) (a b i : Fin n) (t : Prog (n+1)) (z : Fin n → Fn V)
    (h : Fn V) (na : a≠i) (nb : b≠i) :
    tag (.gate op a b t) z i h =
      tag t (snoc z (Cuts.comb op (z a) (z b))) i.castSucc h := by
  funext y; unfold tag; simp only [Prog.eval,Function.update_of_ne na,Function.update_of_ne nb]
  congr 1; funext j
  cases j using Fin.lastCases with
  | last => rw [Function.update_of_ne (Fin.ne_of_gt (Fin.castSucc_lt_last i))]; simp [Cuts.comb,Node.value,applyOp]
  | cast j => by_cases eq : j=i <;> simp [eq]

def sibling (z : Fin n → Fn V) (a b i : Fin n) := if a=i then z b else z a
def nextValue (op : Bool) (z : Fin n → Fn V) (a b i : Fin n) (h : Fn V) : Fn V :=
  fun y => applyOp op (Function.update (fun j => z j y) i (h y) a)
    (Function.update (fun j => z j y) i (h y) b)

/-- Once an OR/AND result becomes the designated port, the old port has no
subsequent reader. Its stored bit can therefore be reset to zero. -/
theorem move (op : Bool) (a b i : Fin n) (t : Prog (n+1)) (z : Fin n → Fn V) (h : Fn V)
    (old : uses t i.castSucc=0) (notOut : ¬returns t i.castSucc) :
    tag (.gate op a b t) z i h = tag t (snoc z (const false)) (Fin.last n) (nextValue op z a b i h) := by
  funext y; apply ignore t i.castSucc old notOut
  intro j ne
  cases j using Fin.lastCases with
  | last => simp [nextValue]
  | cast j => have nj : j≠i := fun e => ne (e ▸ rfl); simp [nj]

theorem or_guard (z : Fin n → Fn V) (a b i : Fin n) (h : Fn V) (zero : z i=const false)
    (reads : a=i ∨ b=i) : nextValue true z a b i h = Cuts.comb true h (sibling z a b i) := by
  funext y
  by_cases ea : a=i <;> by_cases eb : b=i <;>
    simp_all [nextValue,sibling,applyOp,zero,const,Cuts.comb,Node.value,Bool.or_comm]

theorem or_on (z : Fin n → Fn V) (a b i : Fin n) (reads : a=i ∨ b=i) :
    nextValue true z a b i (const true)=const true := by
  funext y; rcases reads with rfl|rfl <;> simp [nextValue,applyOp,const]

theorem and_zero (z : Fin n → Fn V) (a b i : Fin n) (reads : a=i ∨ b=i) (h : Fn V)
    (y : V → Bool) (hy : h y=false) : nextValue false z a b i h y=false := by
  rcases reads with rfl|rfl <;> simp [nextValue,applyOp,hy]

end GateElim.Port
