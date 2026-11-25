import BackgroundSources

namespace GateElim.Products
open Reverse Cuts Block Finset Classical
variable {V : Type*} {n : ℕ}

/-- The two oriented views of a physical AND remember the same gate position.
The opposite operands certify that neither pure input already activates it. -/
structure Birth (V : Type*) where
  index : ℕ
  point : Fn V
  line : Fn V
  otherPoint : Fn V
  otherLine : Fn V

def Birth.fires (g : Birth V) (y z : V→Bool) :=
  g.point y=true ∧ g.line z=true ∧ g.otherPoint y=false ∧ g.otherLine z=false

def births {n : ℕ} (P : Prog n) (off : ℕ) (x z : Fin n→Fn V) : List (Birth V) := match P with
  | .ret _ => []
  | .gate op a b t =>
    (if op then [] else [⟨off,x a,z b,x b,z a⟩,⟨off,x b,z a,x a,z b⟩])++
      births t (off+1) (forward x op a b) (forward z op a b)

theorem birth_mem (P : Prog n) (off : ℕ) (x z : Fin n→Fn V) (g : Birth V) (h : g∈births P off x z) :
    (g.point,g.line)∈sources P x z ∧ off≤g.index ∧ g.index<off+P.size := by
  induction P generalizing off with
  | ret => simp [births] at h
  | @gate n op a b t ih =>
    rcases List.mem_append.mp h with head|tail
    · cases op with
      | true => simp at head
      | false =>
        simp only [Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false] at head
        rcases head with rfl|rfl <;> simp [sources,Prog.size] <;> omega
    · obtain ⟨mem,lo,hi⟩ := ih (off+1) _ _ tail
      exact ⟨List.mem_append_right _ mem,by omega,by simp only [Prog.size]; omega⟩

/-- If the joint input accepts and both separate inputs reject, there is an
AND that is active jointly and inactive separately for this same pair. -/
theorem strict_first (P : Prog n) (off : ℕ) (x z : Fin n→Fn V) (y v : V→Bool) (mix : Fin n→Bool)
    (raw : ∀ i,mix i=true → x i y=true ∨ z i v=true)
    (away : ∀ g∈births P off x z,¬g.fires y v) :
    P.eval mix=true → Block.val P x y=true ∨ Block.val P z v=true := by
  induction P generalizing off with
  | ret i => exact raw i
  | @gate n op a b t ih =>
    let X := forward x op a b; let Z := forward z op a b
    have next : ∀ g∈births t (off+1) X Z, ¬g.fires y v := fun g h => away g (List.mem_append_right _ h)
    have step (i : Fin (n+1)) : snoc mix (applyOp op (mix a) (mix b)) i=true → X i y=true ∨ Z i v=true := by
      cases i using Fin.lastCases with
      | cast i => simpa [X,Z,forward] using raw i
      | last =>
        have ra := raw a; have rb := raw b
        cases op with
        | true => simp [X,Z,forward,Node.value,applyOp]; tauto
        | false =>
          have h := away ⟨off,x a,z b,x b,z a⟩ (by simp [births])
          have k := away ⟨off,x b,z a,x a,z b⟩ (by simp [births])
          simp only [Birth.fires] at h k
          simp [X,Z,forward,Node.value,applyOp]
          grind
    intro h
    have yes := ih (off+1) X Z (snoc mix (applyOp op (mix a) (mix b))) step next h
    simpa only [X,Z,Block.val,forward_at,Prog.eval] using yes

end GateElim.Products

namespace GateElim.Plane
open Desk2008 Desk2008.Fanout PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Reverse Cuts Block Products Rows Finset Classical
variable {q N : ℕ}

/-- The false positive is guaranteed even for a source that genuinely
switches on for that surviving pair, after the chosen background is fixed. -/
theorem residual_births (q t : ℕ) (ht : 1≤t) (I : Fin N→Fin N→Prop) [DecidableRel I]
    (B : Background I) (room : B.lines.card+t≤q) (P : Prog (N+N))
    (yes : ∀ S,EdgeIn (adj I) S → P.eval (bits S)=true)
    (no : ∀ S,(lns S).card≤q → ¬EdgeIn (adj I) S → P.eval (bits S)=false)
    (p l : Fin N) (hp : p∈B.ptsOK) (hl : l∈B.lnsOK) (inc : I p l) :
    (∃ g∈births P 0 B.px B.ly,g.fires (onSet {p}) (onSet {l})) ∧
    (l∉edgesAt I t P B.px B.ly p →
      ∀ g∈births P 0 B.px B.ly,g.fires (onSet {p}) (onSet {l}) →
        ∃ X Y : Finset (Fin N), X.card≤t ∧ Y.card≤t ∧ (X.card=1 ∨ Y.card=1) ∧
          g.point (onSet X)=true ∧ g.line (onSet Y)=true ∧
          (lns (B.extend X Y)).card≤q ∧ ¬EdgeIn (adj I) (B.extend X Y) ∧ P.eval (bits (B.extend X Y))=false) := by
  constructor
  · by_contra! miss
    have okX := B.legal {p} ∅ (q:=q) (by simp; omega) (by simp)
    have okY := B.legal ∅ {l} (q:=q) (by simp; omega) (by simp)
    have nx : Block.val P B.px (onSet {p})=false := by
      unfold Block.val; rw [B.pureX]; exact no _ okX.1 okX.2
    have ny : Block.val P B.ly (onSet {l})=false := by
      unfold Block.val; rw [B.pureY]; exact no _ okY.1 okY.2
    have alt := strict_first P 0 B.px B.ly (onSet {p}) (onSet {l}) _ (B.raw_cover p l) miss
      (yes _ (B.rises p l hp hl inc))
    simp [nx,ny] at alt
  · intro miss g member fires
    obtain ⟨X,Y,xs,ys,one,xg,yg,off⟩ := bad_at I t P B.px B.ly p l miss _ (birth_mem P 0 _ _ g member).1 fires.1 fires.2.1
    obtain ⟨small,free⟩ := B.legal X Y (q:=q) (by omega) off
    exact ⟨X,Y,xs,ys,one,xg,yg,small,free,no _ small free⟩

end GateElim.Plane
#print axioms GateElim.Plane.residual_births
