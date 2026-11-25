import Compiler
import Peeling

namespace GateElim
open Classical Finset
variable {V : Type*} [DecidableEq V]

theorem core {R : V → V → Prop} (B : Finset V) {G : Fn V} {gs : List (Node V)}
    (run : Ready (base B) gs G) (fit : Fits R B G)
    (safe : Finset V → Prop) (start : safe B)
    (step : ∀ D⊆B, safe D → (∀ u∈B, u∉D → ¬Strong R D u) →
      ∀ i∈D, ¬Strong R D i → safe (D.erase i)) :
    ∃ D⊆B, safe D ∧ (∀ u∈B, u∉D → ¬Strong R D u) ∧ (∀ i∈D, Strong R D i) ∧
      ∃ F : Fn V, ∃ tail : List (Node V), Ready (base D) tail F ∧ Fits R D F ∧ tail.length≤gs.length := by
  classical
  suffices loop : ∀ k (D : Finset V), D.card=k → D⊆B → safe D →
      (∀ u∈B, u∉D → ¬Strong R D u) → ∀ F : Fn V, ∀ tail : List (Node V),
      Ready (base D) tail F → Fits R D F → tail.length≤gs.length →
      ∃ E⊆B, safe E ∧ (∀ u∈B, u∉E → ¬Strong R E u) ∧ (∀ i∈E, Strong R E i) ∧
        ∃ F : Fn V, ∃ tail : List (Node V), Ready (base E) tail F ∧ Fits R E F ∧ tail.length≤gs.length by
    exact loop B.card B rfl (by rfl) start (fun _ inside absent => (absent inside).elim) G gs run fit (by rfl)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro D size sub ok erased F tail ready fits cost
    by_cases done' : ∀ i∈D, Strong R D i
    · exact ⟨D,sub,ok,erased,done',F,tail,ready,fits,cost⟩
    · push Not at done'
      obtain ⟨i,hi,poor⟩ := done'
      have lt := Finset.card_erase_lt_of_mem hi
      apply ih (D.erase i).card (by omega) (D.erase i) rfl
        (Finset.Subset.trans (Finset.erase_subset _ _) sub) (step D sub ok erased i hi poor) ?_
        (clamp i F) (restricted i tail) (restrict_base D i ready) (fits_erase fits i)
      · exact (show (restricted i tail).length≤tail.length by simp [restricted,List.length_filter_le]).trans cost
      · intro u hu no strong
        have was := strong_mono (Finset.erase_subset _ _) u strong
        by_cases eq : u=i
        · exact poor (eq ▸ was)
        · exact erased u hu (fun h => no (Finset.mem_erase.mpr ⟨eq,h⟩)) was

/-- Remove unused input coordinates and apply the previously checked degree
count to a program on its surviving inputs. -/
theorem core_size {R : V → V → Prop} (loop : ∀ i, ¬R i i)
    (sym : ∀ ⦃i j⦄, R i j → R j i) (sep : Separates R) (D : Finset V)
    (G : Fn V) (gs : List (Node V)) (ready : Ready (base D) gs G) (fit : Fits R D G)
    (nonempty : 2≤D.card) (strong : ∀ i∈D, Strong R D i) :
    4*D.card≤3*gs.length+1 := by
  classical
  let idx : D ≃ Fin D.card := Fintype.equivFinOfCardEq (by simp)
  let expand (x : Fin D.card→Bool) (u : V) := if h : u∈D then x (idx ⟨u,h⟩) else false
  let pack (x : V→Bool) (i : Fin D.card) := x (idx.symm i).val
  have same (x : V→Bool) : G (expand (pack x))=G x := by
    obtain ⟨Z,inside,_,dep⟩ := frontier ready
    apply dep
    intro f hf
    rcases inside f hf with ⟨b,rfl⟩|⟨u,hu,rfl⟩
    · rfl
    · simp [var,expand,pack,hu]
  have available : ∀ f∈base D, Rep D.card [] (f ∘ expand) := by
    rintro f (⟨b,rfl⟩|⟨u,hu,rfl⟩)
    · exact Or.inl ⟨b,rfl⟩
    · let v := idx ⟨u,hu⟩
      exact Or.inr ⟨v.val,by simpa using v.isLt,by intro x; simp [Function.comp,var,expand,hu,Desk2008.WireMono.val_nil,v]⟩
  have nonconst (b : Bool) : G ∘ expand ≠ const b := by
    intro h
    have all (x : V→Bool) : G x=b := (same x).symm.trans (congrFun h (pack x))
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (by omega : 0<D.card)
    obtain ⟨j,hj,_,_,_,ij,_⟩ := strong i hi
    obtain ⟨x,y,_,diff⟩ := fits_essential loop fit hi hj ij
    exact diff ((all x).trans (all y).symm)
  obtain ⟨C,size,normal,hm,out,gives⟩ := finish expand ready available nonconst
  have robust : Desk2008.robust D.card C := by
    intro i j ne z
    let a := idx.symm i
    let b := idx.symm j
    have ab : a.val≠b.val := fun e => ne (idx.symm.injective (Subtype.ext e))
    obtain ⟨x,y,agree,hx,hy,diff⟩ := fits_robust loop sym sep fit a.val a.property
      (strong a.val a.property) b.val b.property ab z
    refine ⟨pack x,pack y,?_,hx,hy,?_⟩
    · intro u ui; apply agree
      intro e; exact ui (idx.symm.injective (Subtype.ext e))
    · simpa only [gives,Function.comp_apply,same] using diff
  have bound := Desk2008.Fanout.robust_size C nonempty hm out normal robust
  omega

end GateElim
#print axioms GateElim.core_size
