import Frontier

namespace GateElim
open Finset Classical
variable {V : Type*} [DecidableEq V]
def bits (S : Finset V) : V → Bool := fun i => decide (i∈S)
def EdgeIn (R : V → V → Prop) (S : Finset V) := ∃ i∈S, ∃ j∈S, R i j
def Fits (R : V → V → Prop) (A : Finset V) (F : Fn V) : Prop :=
  ∀ S⊆A, (S.card≤2 → ¬EdgeIn R S → F (bits S)=false) ∧
    (EdgeIn R S → F (bits S)=true)
def Strong (R : V → V → Prop) (A : Finset V) (i : V) :=
  ∃ a∈A, ∃ b∈A, a≠b ∧ R i a ∧ R i b
def Separates (R : V → V → Prop) := ∀ i j a b, i≠j → a≠b → R i a → R i b →
  (a≠j ∧ ¬R j a) ∨ (b≠j ∧ ¬R j b)

theorem strong_mono {R : V → V → Prop} {A B : Finset V} (sub : B⊆A) (i : V) :
    Strong R B i → Strong R A i := by
  rintro ⟨a,ha,b,hb,h⟩; exact ⟨a,sub ha,b,sub hb,h⟩

theorem fits_erase {R : V → V → Prop} {A : Finset V} {F : Fn V} (h : Fits R A F) (i : V) :
    Fits R (A.erase i) (clamp i F) := by
  intro S sub
  have miss : i∉S := fun hi => (Finset.mem_erase.mp (sub hi)).1 rfl
  have eq : Function.update (bits S) i false=bits S := by
    funext u
    by_cases e : u=i
    · subst u; simp [bits,miss]
    · simp [e]
  simpa only [clamp,eq] using h S (Finset.Subset.trans sub (Finset.erase_subset _ _))

theorem fits_notbase {R : V → V → Prop} (loop : ∀ i, ¬R i i) {A : Finset V} {F : Fn V}
    (h : Fits R A F) (edge : EdgeIn R A) : F∉base A := by
  have off := (h ∅ (by simp)).1 (by simp) (by simp [EdgeIn])
  have on := (h A (by rfl)).2 edge
  rintro (⟨b,rfl⟩|⟨i,hi,rfl⟩)
  · simp_all [const]
  · have z := (h {i} (by simpa using hi)).1 (by simp) (by simpa [EdgeIn] using loop i)
    simp [bits,var] at z

theorem fits_robust {R : V → V → Prop} (loop : ∀ i, ¬R i i) (sym : ∀ ⦃u v⦄, R u v → R v u)
    (sep : Separates R) {A : Finset V} {F : Fn V} (fit : Fits R A F)
    (i : V) (hi : i∈A) (big : Strong R A i) (j : V) (hj : j∈A) (ne : i≠j) :
    RobustAgainst F i j := by
  obtain ⟨a,ha,b,hb,ab,ia,ib⟩ := big
  have pick : ∃ t∈A, R i t ∧ t≠j ∧ ¬R j t := by
    rcases sep i j a b ne ab ia ib with yes|yes
    · exact ⟨a,ha,ia,yes⟩
    · exact ⟨b,hb,ib,yes⟩
  obtain ⟨t,ht,it,tj,jt⟩ := pick
  intro z
  let D : Finset V := if z then {t,j} else {t}
  have inA : D⊆A := by
    cases z
    · simpa [D] using ht
    · exact Finset.insert_subset ht (Finset.singleton_subset_iff.mpr hj)
  have size : D.card≤2 := by cases z <;> simp [D,Finset.card_le_two]
  have absent : ¬EdgeIn R D := by
    cases z
    · simpa [D,EdgeIn] using loop t
    · simpa [D,EdgeIn,loop,tj,jt] using (show ¬R t j from fun h => jt (sym h))
  have ton : t∈D := by cases z <;> simp [D]
  have off := (fit D inA).1 size absent
  have on := (fit (insert i D) (Finset.insert_subset hi inA)).2
    ⟨i,by simp,t,Finset.mem_insert_of_mem ton,it⟩
  refine ⟨bits D,bits (insert i D),?_,?_,?_,by simp [off,on]⟩
  · intro u ui; simp [bits,ui]
  · cases z <;> simp [D,bits,tj.symm]
  · cases z <;> simp [D,bits,tj.symm,ne.symm]

theorem fits_essential {R : V → V → Prop} (loop : ∀ i, ¬R i i) {A : Finset V} {F : Fn V}
    (fit : Fits R A F) {i j : V} (hi : i∈A) (hj : j∈A) (ij : R i j) : Essential F i := by
  have off := (fit {j} (by simpa using hj)).1 (by simp) (by simpa [EdgeIn] using loop j)
  have on := (fit {i,j} (Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj))).2 ⟨i,by simp,j,by simp,ij⟩
  exact ⟨bits {j},bits {i,j},by intro u ne; simp [bits,ne],by simp [off,on]⟩

/-- A poor vertex is charged at most once. It remains poor after later deletions,
so all charges can be bounded using the final surviving set alone. -/
theorem peel_many {R : V → V → Prop} (loop : ∀ i, ¬R i i) (sym : ∀ ⦃u v⦄, R u v → R v u)
    (sep : Separates R) (k : ℕ) (A : Finset V) (F : Fn V) (gs : List (Node V))
    (ready : Ready (base A) gs F) (fit : Fits R A F)
    (continues : ∀ S⊆A, A.card<S.card+k → EdgeIn R S) :
    ∃ B⊆A, B.card+k=A.card ∧ ∃ G : Fn V, ∃ tail : List (Node V),
      Ready (base B) tail G ∧ Fits R B G ∧
      tail.length+2*k ≤ gs.length + ((A \ B).filter fun i => ¬Strong R B i).card := by
  classical
  induction k generalizing A F gs with
  | zero => exact ⟨A,by rfl,by simp,F,gs,ready,fit,by simp⟩
  | succ k ih =>
    have notbase := fits_notbase loop fit (continues A (by rfl) (by omega))
    obtain ⟨i,hi,rest,run,cost⟩ := peel A gs F ready notbase (Strong R A)
      (fun u hu h j hj ne => fits_robust loop sym sep fit u hu h j hj ne)
    have size := Finset.card_erase_add_one hi
    have cont (S : Finset V) (h : S⊆A.erase i) (enough : (A.erase i).card<S.card+k) :
        EdgeIn R S := continues S (Finset.Subset.trans h (Finset.erase_subset _ _)) (by omega)
    obtain ⟨B,sub,len,G,tail,final,good,budget⟩ := ih (A.erase i) _ _ run (fits_erase fit i) cont
    have bA := Finset.Subset.trans sub (Finset.erase_subset _ _)
    refine ⟨B,bA,by omega,G,tail,final,good,?_⟩
    let D := (((A.erase i) \ B).filter fun u => ¬Strong R B u)
    let E := ((A \ B).filter fun u => ¬Strong R B u)
    have de : D⊆E := by
      intro u hu
      obtain ⟨h,poor⟩ := Finset.mem_filter.mp hu
      obtain ⟨ha,nb⟩ := Finset.mem_sdiff.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_erase.mp ha).2,nb⟩,poor⟩
    change tail.length+2*k ≤ rest.length+D.card at budget
    change tail.length+2*(k+1) ≤ gs.length+E.card
    by_cases sg : Strong R A i
    · simp [sg] at cost; have := Finset.card_le_card de; omega
    · simp [sg] at cost
      have nB : i∉B := fun h => (Finset.mem_erase.mp (sub h)).1 rfl
      have mem : i∈E := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hi,nB⟩,fun h => sg (strong_mono bA i h)⟩
      have miss : i∉D := by simp [D]
      have plus := Finset.card_le_card (Finset.insert_subset mem de)
      rw [Finset.card_insert_of_notMem miss] at plus
      omega

end GateElim
#print axioms GateElim.peel_many
