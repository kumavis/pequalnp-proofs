import PortTests

namespace GateElim.Port
open Reverse Cuts Finset Classical
variable {V : Type*} {n : ℕ}

def Answers (pos neg : (V→Bool) → Prop) (f : Fn V) :=
  (∀ y, pos y → f y=true) ∧ ∀ y, neg y → f y=false

private theorem recover (P : Prog n) (z : Fin n → Fn V) (i : Fin n) (h : Option (Fn V))
    (S : Set (Fn V)) (pos neg : (V→Bool) → Prop)
    (av : ∀ j, z j∈S) (hg : guard h∈S) (mono : inc (guard h)) (off : z i=const false)
    (sample : Sample pos neg (tag P z i (guard h)) (tag P z i (const true))) (enough : 2 ≤ saved P z) :
    ∃ gs : List (Node V), ∃ f, Built S gs ∧ f∈pool S gs ∧ Answers pos neg f ∧ gs.length+2≤P.size+fee h := by
  have zero : const false∈S := off ▸ av i
  obtain ⟨gs,cost,built,known⟩ := folding P z S av zero
  have safe := masked sample mono
  cases h with
  | none =>
    refine ⟨gs,fn P z,built,known,⟨?_,?_⟩,by simpa [fee] using (by omega : gs.length+2≤P.size)⟩
    · intro y hy; rw [←tag_zero P z i off (guard none) y rfl]; exact sample.yes _ hy
    · intro y hy; rw [←tag_zero P z i off (guard none) y rfl]; exact sample.no _ hy
  | some h =>
    let g := Node.mk true h (fn P z)
    refine ⟨gs++[g],g.value,build_append built ⟨pool_grows _ _ hg,known,True.intro⟩,?_,⟨?_,?_⟩,?_⟩
    · rw [pool_append]; exact Set.mem_insert _ _
    · intro y hy
      by_cases yes : h y=true
      · simp [g,Node.value,yes]
      · have r := sample.yes _ hy
        rw [tag_zero P z i off (guard (some h)) y (Bool.eq_false_iff.mpr yes)] at r
        simp [g,Node.value,r]
    · intro y hy; have no := safe _ hy
      have r := sample.no _ hy
      rw [tag_zero P z i off _ y no] at r
      simpa [g,Node.value,r,guard] using no
    · simp [fee]; omega

/-- A variable may be chosen in advance. On every negative input there must
be a larger legal negative where setting that variable to one changes the
answer. Eliminating such an input costs two fewer gates. -/
theorem remove_aux (P : Prog n) (z : Fin n → Fn V) (i : Fin n) (h : Option (Fn V))
    (S : Set (Fn V)) (pos neg : (V→Bool)→Prop) (somePos : ∃y, pos y) (someNeg : ∃y, neg y)
    (av : ∀ j, z j∈S) (incr : ∀ j, inc (z j)) (hg : guard h∈S) (mono : inc (guard h))
    (off : z i=const false) (sample : Sample pos neg (tag P z i (guard h)) (tag P z i (const true))) :
    ∃ gs : List (Node V), ∃ f, Built S gs ∧ f∈pool S gs ∧ Answers pos neg f ∧ gs.length+2≤P.size+fee h := by
  classical
  induction P generalizing S h with
  | ret o =>
    have ne : o≠i := not_return sample
    obtain ⟨t,dep⟩ := dependence sample someNeg
    exact (dep (by simp [tag,Prog.eval,ne])).elim
  | @gate n op a b t ih =>
    let P := Prog.gate op a b t
    by_cases reads : a=i ∨ b=i
    · have hit : z a=const false ∨ z b=const false := by rcases reads with rfl|rfl <;> simp [off]
      have oldOut : ¬returns t i.castSucc := not_return (P:=Prog.gate op a b t) sample
      by_cases elsewhere : uses t i.castSucc≠0
      · apply recover P z i h S pos neg av hg mono off sample
        have two : 2≤uses P i := by simp only [P,uses,reads,↓reduceIte]; omega
        exact two.trans (zeros P z i off)
      have old := not_not.mp elsewhere
      let z' := snoc z (const false)
      have av' (j : Fin (n+1)) : z' j∈S := by
        cases j using Fin.lastCases <;> simp [z',av,show const false∈S from off ▸ av i]
      have inc' (j : Fin (n+1)) : inc (z' j) := by
        cases j using Fin.lastCases with
        | last => simp only [z',snoc_last]; intro _ _ _ h; exact h
        | cast j => simpa [z'] using incr j
      cases op with
      | false =>
        let next := snoc z (comb false (z a) (z b))
        have newZero : next (Fin.last n)=const false := by
          simp only [next,snoc_last]; funext y; rcases hit with h|h <;> simp [h,const,comb,Node.value]
        by_cases second : uses t (Fin.last n) ≠ 0
        · apply recover P z i h S pos neg av hg mono off sample
          have c := zeros t next (Fin.last n) newZero
          change 2≤(if _ then 1 else 0)+saved t next
          simp only [hit,↓reduceIte]; omega
        have m0 := move false a b i t z (guard h) old oldOut
        have m1 := move false a b i t z (const true) old oldOut
        by_cases terminal : returns t (Fin.last n)
        · have safe := masked sample mono
          have must (y : V→Bool) (yes : pos y) : guard h y=true := by
            have r := sample.yes _ yes; rw [m0] at r
            simp only [tag,returns_eval t (Fin.last n) terminal,Function.update_self] at r
            cases e : guard h y
            · have no := and_zero z a b i reads (guard h) y e; simp_all
            · rfl
          cases h with
          | none =>
            obtain ⟨y,hy⟩ := somePos; have f := must y hy; simp [guard,const] at f
          | some f => exact ⟨[],f,True.intro,hg,⟨must,safe⟩,by simp [fee,Prog.size]⟩
        · obtain ⟨y,dep⟩ := dependence sample someNeg
          apply False.elim; apply dep
          rw [m0,m1]
          apply ignore t (Fin.last n) (not_not.mp second) terminal
          intro j ne; simp [ne]
      | true =>
        let sib := sibling z a b i
        have sibA : sib∈S := by by_cases e : a=i <;> simp [sib,sibling,e,av]
        have sibI : inc sib := by by_cases e : a=i <;> simp [sib,sibling,e,incr]
        have zero := move true a b i t z (guard h) old oldOut
        have one := (move true a b i t z (const true) old oldOut).trans (by rw [or_on z a b i reads])
        rw [or_guard z a b i _ off reads] at zero
        cases h with
        | none =>
          have merge0 : comb true (guard (none : Option (Fn V))) sib=sib := by
            funext y; simp [comb,Node.value,const,guard]
          change tag _ _ _ _ = tag t z' (Fin.last n) (comb true _ sib) at zero
          rw [merge0] at zero
          have sam : Sample pos neg (tag t z' (Fin.last n) (guard (some sib))) (tag t z' (Fin.last n) (const true)) := by
            rw [zero,one] at sample
            exact sample
          obtain ⟨gs,F,bu,haveF,cert,cost⟩ := ih z' (Fin.last n) (some sib) S av' inc' sibA sibI
            (by simp [z']) sam
          exact ⟨gs,F,bu,haveF,cert,by simpa [Prog.size,fee] using cost⟩
        | some f =>
          let g := Node.mk true f sib
          let T := insert g.value S
          have sam : Sample pos neg (tag t z' (Fin.last n) (guard (some g.value))) (tag t z' (Fin.last n) (const true)) := by
            rw [zero,one] at sample
            exact sample
          obtain ⟨gs,F,bu,haveF,cert,cost⟩ := ih z' (Fin.last n) (some g.value) T
            (fun i => Set.mem_insert_of_mem _ (av' i)) inc' (Set.mem_insert _ _) (inc_comb true mono sibI)
            (by simp [z']) sam
          refine ⟨g::gs,F,⟨hg,sibA,bu⟩,haveF,cert,?_⟩
          simp [fee,Prog.size] at cost ⊢; omega
    · have na : a≠i := fun h => reads (Or.inl h)
      have nb : b≠i := fun h => reads (Or.inr h)
      let g := Node.mk op (z a) (z b)
      let T := insert g.value S
      let next := snoc z g.value
      have av' (j : Fin (n+1)) : next j∈T := by cases j using Fin.lastCases <;> simp [next,T,av]
      have incr' (j : Fin (n+1)) : inc (next j) := by
        cases j using Fin.lastCases with
        | last => rw [show next (Fin.last _) = comb op (z a) (z b) by simp [next,g,comb]]; exact inc_comb op (incr a) (incr b)
        | cast j => simpa [next] using incr j
      have sam : Sample pos neg (tag t next i.castSucc (guard h)) (tag t next i.castSucc (const true)) := by
        change Sample pos neg (tag t (snoc z (comb op (z a) (z b))) i.castSucc _) (tag t (snoc z (comb op (z a) (z b))) i.castSucc _)
        simpa only [normal_step op a b i t z _ na nb] using sample
      obtain ⟨gs,F,bu,haveF,cert,cost⟩ := ih next i.castSucc h T av' incr'
        (Set.mem_insert_of_mem _ hg) mono (by simpa [next] using off) sam
      exact ⟨g::gs,F,⟨av _,av _,bu⟩,haveF,cert,by simp only [List.length_cons,Prog.size]; omega⟩

end GateElim.Port
#print axioms GateElim.Port.remove_aux
