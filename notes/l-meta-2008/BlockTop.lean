import BlockTools

namespace GateElim.Block
open Reverse Cuts Finset Classical
variable {V J : Type*} [Fintype J] [DecidableEq J] {k : ℕ}

/-- A selected row can enter the final circuit from any affected block along
a path whose AND siblings are true with all selectors switched off. -/
noncomputable def result (T : Prog k) (x : Fin k→Fn V) (z : J→Fin k→Fn V)
    (D : Fin k→Finset J) (j : J) : Fn V :=
  fun y => decide (∃ i, j∈D i ∧ T.weights x i y=true ∧ z j i y=true)

theorem result_sound (T : Prog k) (x : Fin k→Fn V) (z : J→Fin k→Fn V)
    (D : Fin k→Finset J) (j : J) (y : V→Bool) (le : ∀ i, x i y=true → z j i y=true) :
    result T x z D j y=true → T.eval (fun i => z j i y)=true := by
  intro h
  obtain ⟨i,mem,weight,on⟩ := of_decide_eq_true h
  apply path_sound T x y (fun b => j∈D b ∧ z j b y=true) _ le (fun _ => And.right)
  exact (path_iff ..).mpr ⟨i,⟨mem,on⟩,weight⟩

theorem result_complete (T : Prog k) (x : Fin k→Fn V) (z : J→Fin k→Fn V)
    (D : Fin k→Finset J) (j : J) (y : V→Bool) (sep : T.disjoint D)
    (silent : T.eval (fun i => x i y)=false) (outside : ∀ i,j∉D i → z j i y=x i y)
    (yes : T.eval (fun i => z j i y)=true) : result T x z D j y=true := by
  let tag (i : Fin k) := j∈D i ∧ z j i y=true
  have cover (i : Fin k) (on : z j i y=true) : x i y=true ∨ tag i := by
    by_cases h : j∈D i
    · exact Or.inr ⟨h,on⟩
    · exact Or.inl ((outside i h).symm.trans on)
  have alt := path_complete j T x y tag _ D sep cover (fun _ h => h.1) yes
  obtain ⟨i,⟨inside,active⟩,weight⟩ := (path_iff ..).mp (alt.resolve_left (by simp [silent]))
  exact decide_eq_true ⟨i,inside,weight,active⟩

private theorem one_row (T : Prog k) (x : Fin k→Fn V) (z : J→Fin k→Fn V)
    (D : Fin k→Finset J) (j : J) (S : Set (Fn V)) (zero : const false∈S)
    (w : ∀ i, T.weights x i∈S) (haveZ : ∀ i,j∈D i → z j i∈S) :
    ∃ gs, gs.length=2*(univ.filter (fun i => j∈D i)).card ∧ Built S gs ∧ result T x z D j∈pool S gs := by
  let A := univ.filter (fun i => j∈D i)
  obtain ⟨gs,len,bu,has⟩ := batch false (fun i : A => T.weights x i.val) (fun i : A => z j i.val) S
    (fun i => ⟨w _,haveZ _ (mem_filter.mp i.property).2⟩)
  obtain ⟨hs,f,hl,hb,av,eq⟩ := join_values A (fun i => comb false (T.weights x i) (z j i)) (pool S gs)
    (fun i hi => has ⟨i,hi⟩) (pool_grows _ _ zero)
  have equal : f=result T x z D j := by
    funext y; apply Bool.eq_iff_iff.mpr
    simp [eq,result,A,comb,Node.value,and_assoc]
  refine ⟨gs++hs,?_,build_append bu hb,by rw [pool_append,←equal]; exact av⟩
  simp only [List.length_append,len,hl,Fintype.card_coe,A]; omega

/-- Outputting all row responses pays once for the common reverse sweep
and twice per (block, selector) membership. -/
theorem finish (T : Prog k) (x : Fin k→Fn V) (z : J→Fin k→Fn V) (D : Fin k→Finset J)
    (S : Set (Fn V)) (cs : ∀ b, const b∈S) (base : ∀ i,x i∈S) (rows : ∀ j i,j∈D i → z j i∈S) :
    ∃ gs, gs.length≤5*T.size+2*(∑ i,(D i).card) ∧ Built S gs ∧ ∀ j,result T x z D j∈pool S gs := by
  obtain ⟨gs,len,bu,weights⟩ := compile_weights T x S base cs
  let A (j : J) := univ.filter (fun i => j∈D i)
  have swap : ∑ j, (A j).card=∑ i,(D i).card := by
    simp only [A,card_filter]; rw [sum_comm]; simp
  obtain ⟨hs,hl,hb,hav⟩ := gather (V:=V) (univ : Finset J) (pool S gs)
    (fun j => {result T x z D j}) (fun j => 2*(A j).card) (by
      intro j _ U sub
      obtain ⟨h,l,b,r⟩ := one_row T x z D j U (sub (pool_grows _ _ (cs false))) (fun i => sub (weights i))
        (fun i hi => sub (pool_grows _ _ (rows j i hi)))
      exact ⟨h,l.le,b,Set.singleton_subset_iff.mpr r⟩)
  rw [←Finset.mul_sum,swap] at hl
  exact ⟨gs++hs,by simp only [List.length_append]; omega,build_append bu hb,fun j => by
    rw [pool_append]; exact hav j (mem_univ _) (Set.mem_singleton _)⟩

end GateElim.Block
#print axioms GateElim.Block.finish
