import ExtractRows
import PlaneModel
import ParseDesk

namespace GateElim.Plane
open Desk2008 Desk2008.Residual Desk2008.Fanout PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Reverse Rows Finset Classical
attribute [-simp] Fin.natAdd_eq_addNat
variable {N q : ℕ}

/-- The Boolean selects which side is the marked input variable. -/
def pick (pointSide : Bool) (j : Fin N) : Vertex N := if pointSide then left j else right j
def baseline (pointSide : Bool) : Vertex N → Fn (Fin N) :=
  if pointSide then Fin.addCases (fun _ => const false) var else Fin.addCases var (fun _ => const false)
def rowSet (pointSide : Bool) (I : Fin N → Fin N → Prop) [DecidableRel I] (j : Fin N) :=
  Finset.univ.filter fun v => if pointSide then I j v else I v j

private theorem left_right_bits (u v : Fin N) : decide (left u=right v)=false :=
  decide_eq_false (lr _ _)
private theorem right_left_bits (u v : Fin N) : decide (right u=left v)=false :=
  decide_eq_false (Ne.symm (lr _ _))

private theorem eval_left (j p : Fin N) (U : Finset (Fin N)) :
    selected (baseline true) (pick true j) (onSet U) (left p)=decide (p=j) ∧
    selected (baseline false) (pick false j) (onSet U) (left p)=decide (p∈U) := by
  simp [selected,baseline,pick,const,var,onSet,lr]
private theorem eval_right (j l : Fin N) (U : Finset (Fin N)) :
    selected (baseline true) (pick true j) (onSet U) (right l)=decide (l∈U) ∧
    selected (baseline false) (pick false j) (onSet U) (right l)=decide (l=j) := by
  simp [selected,baseline,pick,const,var,onSet,fun l p => Ne.symm (lr p l)]

theorem legal (q : ℕ) (hq : 1≤q) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (side : Bool) (j : Fin N) (U : Finset (Fin N)) (size : U.card≤q) (dis : Disjoint U (rowSet side I j)) :
    let x := selected (baseline side) (pick side j) (onSet U)
    Fintype.card {l : Fin N // x (right l)=true}≤q ∧
      ¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true := by
  dsimp only
  cases side with
  | true =>
    have rd := fun l => (eval_right j l U).1
    have ld := fun p => (eval_left j p U).1
    constructor
    · simpa [Fintype.card_subtype,rd] using size
    · rintro ⟨p,l,hl,hp,hy⟩
      rw [ld] at hp; rw [rd] at hy
      obtain rfl := of_decide_eq_true hp
      exact Finset.disjoint_left.mp dis (of_decide_eq_true hy) (by simpa [rowSet] using hl)
  | false =>
    have rd := fun l => (eval_right j l U).2
    have ld := fun p => (eval_left j p U).2
    constructor
    · simpa [Fintype.card_subtype,rd] using hq
    · rintro ⟨p,l,hl,hp,hy⟩
      rw [ld] at hp; rw [rd] at hy
      obtain rfl := of_decide_eq_true hy
      exact Finset.disjoint_left.mp dis (of_decide_eq_true hp) (by simpa [rowSet] using hl)

private theorem row_linear (I : Fin N → Fin N → Prop) [DecidableRel I]
    (join : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (i j : Fin N) (ne : i≠j) :
    ((Finset.univ.filter (I i))∩(Finset.univ.filter (I j))).card≤1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have := join i j ne
  simp only [Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and] at ha hb
  exact this.unique ha hb

theorem row_geometry (I : Fin N → Fin N → Prop) [DecidableRel I] (order : N=q^2+q+1)
    (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (side : Bool) :
    (∀ j, (rowSet side I j).card=q+1) ∧
    (∀ i j, i≠j → ((rowSet side I i)∩(rowSet side I j)).card≤1) := by
  obtain ⟨pd,meet⟩ := dual_axioms I order hd hj
  cases side <;> simp only [rowSet,Bool.false_eq_true,↓reduceIte]
  · exact ⟨fun j => by simpa [Fintype.card_subtype] using hd j,row_linear (fun a b => I b a) meet⟩
  · exact ⟨fun j => by simpa [Fintype.card_subtype] using pd j,row_linear I hj⟩

noncomputable def simpleSet (P : Prog (N+N)) (side : Bool) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (j : Fin N) := (rowSet side I j).filter fun v =>
  singlePath P (baseline side) (pick side j) v

theorem base_legal (side : Bool) (i : Vertex N) : baseline side i∈base univ := by
  cases side <;> induction i using Fin.addCases with
  | left p => simp [baseline]; first | exact Or.inl ⟨_,rfl⟩ | exact Or.inr ⟨_,by simp,rfl⟩
  | right l => simp [baseline]; first | exact Or.inl ⟨_,rfl⟩ | exact Or.inr ⟨_,by simp,rfl⟩

theorem simple_gate_bound (q : ℕ) (hq : 1≤q) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (order : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (P : Prog (N+N))
    (neg : ∀ x : Vertex N → Bool, Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → P.eval x=false)
    (side : Bool) :
    ∑ j, (simpleSet P side I j).card ≤ 5*P.size+N := by
  classical
  obtain ⟨deg,linear⟩ := row_geometry I order hd hj side
  have h := simple_bound P (baseline side) (pick side) (rowSet side I) (simpleSet P side I)
    (base_legal side) linear (fun _ _ h => (Finset.mem_filter.mp h).2) (by
      intro j U dis few
      have sub : (simpleSet P side I j).card≤(rowSet side I j).card := Finset.card_filter_le ..
      have count : (simpleSet P side I j).card ≤ q+1 := sub.trans (deg j).le
      have ok := legal q hq I side j U (by omega) dis
      exact neg _ ok.1 ok.2)
  have each (j : Fin N) : (simpleSet P side I j).card ≤ ((simpleSet P side I j).card-1)+1 := by omega
  have s := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => each j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at s
  omega

end GateElim.Plane
#print axioms GateElim.Plane.simple_gate_bound
