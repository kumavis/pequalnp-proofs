import LinearPath

namespace GateElim.Reverse
open Finset Classical Rows
variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {n : ℕ}

def selected (x : Fin n → Fn V) (sel : Fin n) (y : V → Bool) (i : Fin n) : Bool :=
  decide (i=sel) || x i y

def singlePath (p : Prog n) (x : Fin n → Fn V) (sel : Fin n) (v : V) :=
  p.path x (onSet {v}) (fun i => i=sel)

theorem weights_sound (p : Prog n) (x : Fin n → Fn V) (sel : Fin n) (y : V → Bool) :
    p.weights x sel y=true → p.eval (selected x sel y)=true := by
  intro yes
  apply path_sound p x y (fun i => i=sel) _
    (fun i hi => by simp [selected,hi]) (fun i eq => by simp [selected,eq])
  exact (path_iff ..).mpr ⟨sel,rfl,yes⟩

/-- On a negative selection the reverse output is also negative. Distinct
pencils therefore have to pay separately for the singleton paths they cover. -/
theorem simple_bound (p : Prog n) (x : Fin n → Fn V) (sel : J → Fin n) (S P : J → Finset V)
    (av : ∀ i, x i∈base Finset.univ)
    (linear : ∀ i j, i≠j → ((S i)∩(S j)).card≤1)
    (simple : ∀ j v, v∈P j → singlePath p x (sel j) v)
    (neg : ∀ j U, Disjoint U (S j) → U.card<(P j).card →
      p.eval (selected x (sel j) (onSet U))=false) :
    ∑ j, ((P j).card-1) ≤ 5*p.size := by
  obtain ⟨gs,cost,all⟩ := common_outputs p x (base univ) av (fun b => Or.inl ⟨b,rfl⟩)
  apply le_trans _ cost
  apply Rows.circuit_bound S P (fun j => p.weights x (sel j)) gs univ linear (fun j => all _)
  · intro j v hv
    obtain ⟨i,rfl,h⟩ := (path_iff ..).mp (simple j v hv)
    exact h
  · intro j U dis small
    apply Bool.eq_false_iff.mpr
    intro yes
    have wrong := weights_sound p x (sel j) (onSet U) yes
    simp [neg j U dis small] at wrong

def initScope (sel : J → Fin n) (i : Fin n) : Finset J :=
  univ.filter fun j => sel j=i

theorem disjoint_simple (p : Prog n) (x : Fin n → Fn V) (sel : J → Fin n)
    (sep : p.disjoint (initScope sel)) (j : J) (v : V)
    (zero : p.eval (fun i => x i (onSet {v}))=false)
    (on : p.eval (selected x (sel j) (onSet {v}))=true) :
    singlePath p x (sel j) v := by
  have h := path_complete j p x (onSet {v}) (fun i => i=sel j) _ (initScope sel) sep
    (fun i => by simp [selected]; tauto)
    (fun i e => by simp [initScope,e]) on
  simpa [zero,singlePath] using h

end GateElim.Reverse
#print axioms GateElim.Reverse.simple_bound
