import Elimination

namespace GateElim
open Finset Classical
variable {V : Type*} [DecidableEq V]

/-- Tracing the output backwards through one binary gate adds at most one wire
to a sufficient collection of earlier values. -/
theorem frontier {S : Set (Fn V)} {gs : List (Node V)} {F : Fn V} (h : Ready S gs F) :
    ∃ D : Finset (Fn V), (∀ f∈D, f∈S) ∧ D.card≤gs.length+1 ∧
    ∀ x y, (∀ d∈D, d x=d y) → F x=F y := by
  classical
  induction gs generalizing S with
  | nil => exact ⟨{F},by simpa [Ready] using h,by simp,by intro x y a; exact a F (by simp)⟩
  | cons g gs ih =>
    obtain ⟨D,inside,cost,dep⟩ := ih h.2.2
    by_cases used : g.value ∈ D
    · let E := insert g.a (insert g.b (D.erase g.value))
      have domain : ∀ f∈E, f∈S := by
        intro f hf
        rcases Finset.mem_insert.mp hf with rfl|hf
        · exact h.1
        rcases Finset.mem_insert.mp hf with rfl|hf
        · exact h.2.1
        obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hf
        exact (inside f mem).resolve_left ne
      have bound : E.card≤(g::gs).length+1 := by
        have e := Finset.card_erase_add_one used
        have i := Finset.card_insert_le g.b (D.erase g.value)
        have j := Finset.card_insert_le g.a (insert g.b (D.erase g.value))
        change (insert g.a (insert g.b (D.erase g.value))).card ≤ gs.length+1+1; omega
      refine ⟨E,domain,bound,?_⟩
      intro x y same
      apply dep x y
      intro d hd
      by_cases eq : d=g.value
      · have a := same g.a (by simp [E])
        have b := same g.b (by simp [E])
        simp [eq,Node.value,a,b]
      · exact same d (by simp [E,eq,hd])
    · refine ⟨D,?_,by simp; omega,dep⟩
      intro d hd
      exact (inside d hd).resolve_left (fun eq => used (eq ▸ hd))

theorem support_size (A E : Finset V) (gs : List (Node V)) (F : Fn V)
    (ready : Ready (base A) gs F) (ess : ∀ i∈E, Essential F i) : E.card ≤ gs.length+1 := by
  classical
  obtain ⟨D,inside,cost,dep⟩ := frontier ready
  have inj : Function.Injective (@var V) := by
    intro i j eq
    by_contra ne
    have e := congrFun eq (fun u : V => decide (u=i))
    exact ne (show j=i by simpa [var] using e).symm
  have subset : E.image var ⊆ D := by
    intro f hf
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hf
    by_contra miss
    obtain ⟨x,y,agree,diff⟩ := ess i hi
    apply diff
    apply dep x y
    intro d hd
    rcases inside d hd with ⟨b,rfl⟩|⟨j,_,rfl⟩
    · rfl
    · exact agree j (fun e => miss (e ▸ hd))
  simpa [Finset.card_image_of_injective E inj] using (Finset.card_le_card subset).trans cost

end GateElim
#print axioms GateElim.support_size
