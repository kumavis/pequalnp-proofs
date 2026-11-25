import BlockAssembly
import Through365

namespace GateElim.Plane
open Desk2008 Desk2008.Fanout Reverse Cuts Rows Block Finset Classical
attribute [-simp] Fin.natAdd_eq_addNat
variable {q N k : ℕ}

def composed (T : Prog k) (B : Fin k→Prog (N+N)) (v : Vertex N→Bool) :=
  T.eval (fun i => (B i).eval v)

def blockSize (T : Prog k) (B : Fin k→Prog (N+N)) := (∑ i,(B i).size)+T.size

private theorem pick_inj (side : Bool) : Function.Injective (pick (N:=N) side) := by
  cases side
  · exact Fin.natAdd_injective _ _
  · exact Fin.castAdd_injective _ _

/-- All orders. The top part can have arbitrary fanout, depth, and arbitrary
OR overlap. The lower programs may overlap on their original inputs. -/
theorem block_tradeoff (q : ℕ) (hq : 1≤q) (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (T : Prog k) (B : Fin k→Prog (N+N)) (side : Bool)
    (sep : T.disjoint (fun i => contact (pick side) (B i)))
    (pos : ∀ p l,I p l → composed T B (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N→Bool,Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l,I p l ∧ x (left p)=true ∧ x (right l)=true) → composed T B x=false) :
    N*q≤localSum B (pick side)+5*T.size+2*(∑ i,(contact (pick side) (B i)).card) := by
  let x := baseline (N:=N) side
  let sel := pick (N:=N) side
  let X := fun i => val (B i) x
  let Z := fun (j : Fin N) i => val (B i) (inputs x sel j)
  let D := fun i => contact sel (B i)
  obtain ⟨gs,len,ready⟩ := assemble T B x sel (base univ) (base_legal side) (fun b => Or.inl ⟨b,rfl⟩)
  have lo := (exact_separate_outputs I ord hd hj side).2 gs (result T X Z D) ready (by
    intro j v incident
    apply result_complete T X Z D j _ sep
    · change composed T B (fun i => baseline side i (onSet {v}))=false
      apply neg
      · cases side <;> simp [Fintype.card_subtype,baseline,const,var,onSet,right,hq]
      · cases side <;> simp [baseline,left,right,const]
    · exact fun i no => congrFun (outside (B i) x sel j no) _
    · change composed T B (selected (baseline side) (pick side j) (onSet {v}))=true
      rw [singleton_selected]
      cases side <;> simp only [Bool.false_eq_true,↓reduceIte]
      · exact pos v j (by simpa [rowSet] using incident)
      · exact pos j v (by simpa [rowSet] using incident)) (by
    intro j U dis small
    have legal' := legal q hq I side j U small dis
    apply Bool.eq_false_iff.mpr
    intro h
    have on := result_sound T X Z D j (onSet U)
      (fun i => val_mono (B i) x (inputs x sel j) (fun i => (input_cover x sel j i).1) _) h
    exact Bool.noConfusion (on.symm.trans (neg _ legal'.1 legal'.2)))
  exact lo.trans len

private theorem affordable (s h d : ℕ) (support : d ≤ s+1) (cheap : h≤4 ∨ d≤96) :
    localCost s h d+2*d≤99*s+47 := by
  rcases cheap with cuts|bits
  · have coeff : (8*h+5)*s ≤37*s := Nat.mul_le_mul_right s (by omega)
    have square : h^2≤16 := by simpa using Nat.pow_le_pow_left cuts 2
    have term : (2*h^2+3*h+1)*d≤45*d := Nat.mul_le_mul_right d (by omega)
    have cut := Nat.min_le_right (d*s) (rowCost s h d)
    unfold localCost rowCost at *; omega
  · have many := Nat.mul_le_mul_right s bits
    have direct := Nat.min_le_left (d*s) (rowCost s h d)
    unfold localCost; omega

/-- The number of bottom blocks and their global number of overlapping ANDs
are unlimited. Each bottom block can independently use either local bound. -/
theorem desk_blocks {q N k : ℕ} (I : Fin N→Fin N→Prop) [DecidableRel I]
    (hq : 100<q) (ord : N=q^2+q+1) (hd : ∀ l,Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r,p≠r → ∃! l,I p l ∧ I r l) (T : Prog k) (B : Fin k→Prog (N+N)) (side : Bool)
    (live : ports T=univ) (sep : T.disjoint (fun i => contact (pick side) (B i)))
    (cheap : ∀ i,ProgCuts (B i) (initScope (pick (N:=N) side))≤4 ∨ (contact (pick side) (B i)).card≤96)
    (pos : ∀ p l,I p l → composed T B (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N→Bool,Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l,I p l ∧ x (left p)=true ∧ x (right l)=true) → composed T B x=false) :
    N*q≤100*blockSize T B := by
  have bound := block_tradeoff q (by omega) I ord hd hj T B side sep pos neg
  have per := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    affordable _ _ _ (contact_count (pick side) (pick_inj side) (B i)) (cheap i))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at per
  have count := (support T).1; rw [live] at count; simp only [Finset.card_univ,Fintype.card_fin] at count
  have large : 4700≤N*q := by nlinarith
  unfold localSum at bound; unfold blockSize; omega

end GateElim.Plane
#print axioms GateElim.Plane.block_tradeoff
#print axioms GateElim.Plane.desk_blocks
