import Elimination
import RobustFanout

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Desk2008.Fanout
namespace GateElim
open Classical

/-- A list of indexed operations becomes a semantic straight-line program when
each operand is available initially or produced by an earlier index. -/
private theorem from_index {V : Type*} (S : Set (Fn V)) (m : ℕ) (node : Fin m → Node V)
    (F : Fn V)
    (available : ∀ j, ∀ f, f=(node j).a ∨ f=(node j).b →
      f∈S ∨ ∃ h, h.val<j.val ∧ f=(node h).value)
    (result : F∈S ∨ ∃ h, F=(node h).value) : Ready S (List.ofFn node) F := by
  induction m generalizing S with
  | zero => simpa [Ready] using result
  | succ m ih =>
    have first (f : Fn V) (hf : f=(node 0).a ∨ f=(node 0).b) : f∈S := by
      rcases available 0 f hf with h|⟨j,lt,_⟩
      · exact h
      · simp at lt
    rw [List.ofFn_succ]
    refine ⟨first _ (Or.inl rfl),first _ (Or.inr rfl),?_⟩
    apply ih
    · intro j f h
      rcases available j.succ f h with orig|⟨i,lt,e⟩
      · exact Or.inl (Set.mem_insert_of_mem _ orig)
      · cases i using Fin.cases with
        | zero => exact Or.inl (Or.inl e)
        | succ i => exact Or.inr ⟨i,by simpa using lt,e⟩
    · rcases result with orig|⟨i,e⟩
      · exact Or.inl (Set.mem_insert_of_mem _ orig)
      · cases i using Fin.cases with
        | zero => exact Or.inl (Or.inl e)
        | succ i => exact Or.inr ⟨i,e⟩

theorem from_desk {n : ℕ} (C : Circuit) (normal : Normal n C) (hm : Monotone2 C)
    (out : C.output<n+C.size) :
    ∃ gs : List (Node (Fin n)), gs.length=C.size ∧
      Ready (base Finset.univ) gs (circuitFun n C) := by
  classical
  let w (i : ℕ) : Fn (Fin n) := fun x => Desk2008.WireMono.val C.gates x i
  have get (j : Fin C.size) := spec normal (v:=n+j.val) ⟨by omega,by omega⟩
  choose g a b hg ins ab before _ using get
  let node (j : Fin C.size) : Node (Fin n) :=
    ⟨decide ((g j).op=.or),w (a j),w (b j)⟩
  have value (j : Fin C.size) : w (n+j.val)=(node j).value := by
    funext x
    have ev := eval_gate (by omega : n≤n+j.val ∧ n+j.val<n+C.size) (hg j) (ins j)
      (by have := ab j; have := before j; omega) (before j) x
    have ops : (g j).op=.and ∨ (g j).op=.or := by
      simpa [Set.mem_insert_iff,Set.mem_singleton_iff] using (hm _ (List.mem_of_getElem? (hg j))).1
    rcases ops with op|op <;> simpa [node,w,Node.value,op,GateOp.eval] using ev
  have source (i : ℕ) (hi : i<n) : w i∈base Finset.univ :=
    Or.inr ⟨⟨i,hi⟩,by simp,by funext x; exact Desk2008.WireMono.val_lt _ _ _ hi⟩
  have getWire (i k : ℕ) (ik : i<n+k) (ks : k≤C.size) :
      w i∈base Finset.univ ∨ ∃ h : Fin C.size, h.val<k ∧ w i=(node h).value := by
    by_cases hi : i<n
    · exact Or.inl (source i hi)
    · let h : Fin C.size := ⟨i-n,by omega⟩
      have eq : n+h.val=i := by dsimp [h]; omega
      exact Or.inr ⟨h,by dsimp [h]; omega,eq ▸ value h⟩
  refine ⟨List.ofFn node,by simp,?_⟩
  apply from_index
  · intro j f h
    have aa := ab j
    have bb := before j
    rcases h with e|e <;> subst f
    · exact getWire _ j.val (by omega) (by omega)
    · exact getWire _ j.val bb (by omega)
  · have eq : circuitFun n C = w C.output := by rfl
    rw [eq]
    rcases getWire _ _ out (le_refl _) with h|⟨i,_,e⟩
    · exact Or.inl h
    · exact Or.inr ⟨i,e⟩

end GateElim
#print axioms GateElim.from_desk
