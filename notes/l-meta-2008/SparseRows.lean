import Frontier

namespace GateElim
set_option linter.unusedSectionVars false
open Finset Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mono_frontier {S : Set (Fn V)} {gs : List (Node V)} {F : Fn V} (h : Ready S gs F) :
    ∃ D : Finset (Fn V), (∀ f∈D, f∈S) ∧ D.card≤gs.length+1 ∧
    ∀ x y, (∀ d∈D, d x=true → d y=true) → F x=true → F y=true := by
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
        subst d
        cases o : g.useOr <;> simp_all [Node.value] <;> tauto
      · exact same d (by simp [E,eq,hd])
    · refine ⟨D,?_,by simp; omega,dep⟩
      intro d hd
      exact (inside d hd).resolve_left (fun eq => used (eq ▸ hd))

namespace Rows
def onSet (U : Finset V) : V → Bool := fun i => decide (i∈U)
def Increasing (f : Fn V) : Prop := ∀ X Y : Finset V, X⊆Y → f (onSet X)=true → f (onSet Y)=true
noncomputable def foot (f : Fn V) : Finset V := univ.filter fun i => f (onSet {i})=true
def Special (S : Finset V) (f : Fn V) : Prop :=
  f (onSet ∅)=false ∧ foot f⊆S ∧ 2≤(foot f).card

private theorem inc_node (g : Node V) (a : Increasing g.a) (b : Increasing g.b) : Increasing g.value := by
  intro X Y sub
  have ha := a X Y sub
  have hb := b X Y sub
  cases o : g.useOr <;> simp_all [Node.value] <;> tauto

private theorem inc_base (A : Finset V) (f : Fn V) (h : f∈base A) : Increasing f := by
  rcases h with ⟨b,rfl⟩|⟨i,_,rfl⟩
  · intro X Y _ a; exact a
  · intro X Y sub h; exact decide_eq_true (sub (of_decide_eq_true h))

private theorem non_special_base (S A : Finset V) (f : Fn V) (h : f∈base A) : ¬Special S f := by
  rcases h with ⟨b,rfl⟩|⟨i,_,rfl⟩
  · cases b <;> simp [Special,foot,const]
  · have h : foot (var i)={i} := by ext j; simp [foot,var,onSet,eq_comm]
    simp [Special,h]

private theorem skip {S : Finset V} {T G : Set (Fn V)} {gs : List (Node V)} {F : Fn V}
    (ready : Ready T gs F) (incs : ∀ f∈T, Increasing f) (sub : T⊆G)
    (all : ∀ f, Increasing f → ¬Special S f → f∈G) :
    Ready G (gs.filter (fun g => decide (Special S g.value))) F := by
  classical
  induction gs generalizing T G with
  | nil => exact sub ready
  | cons g gs ih =>
    have inc := inc_node g (incs _ ready.1) (incs _ ready.2.1)
    have incs' : ∀ f∈insert g.value T, Increasing f := by
      rintro f (rfl|h); exact inc; exact incs _ h
    by_cases sp : Special S g.value
    · simp only [List.filter_cons,sp,decide_true,↓reduceIte]
      exact ⟨sub ready.1,sub ready.2.1,ih ready.2.2 incs' (Set.insert_subset_insert sub)
        (fun f a b => Set.mem_insert_of_mem _ (all f a b))⟩
    · simp only [List.filter_cons,sp,decide_false,Bool.false_eq_true,↓reduceIte]
      exact ih ready.2.2 incs' (Set.insert_subset (all _ inc sp) sub) all

/-- A row is allowed to accept only some of the incident singleton inputs. It
must reject every small set outside the entire prescribed row. -/
theorem row_bound (S P : Finset V) (gs : List (Node V)) (F : Fn V) (A : Finset V)
    (ready : Ready (base A) gs F)
    (pos : ∀ i∈P, F (onSet {i})=true)
    (neg : ∀ U : Finset V, Disjoint U S → U.card<P.card → F (onSet U)=false) :
    P.card≤(gs.filter (fun g => decide (Special S g.value))).length+1 := by
  classical
  let G := {f : Fn V | Increasing f ∧ ¬Special S f}
  have run : Ready G (gs.filter (fun g => decide (Special S g.value))) F := by
    apply skip ready (inc_base A)
    · intro f h; exact ⟨inc_base A f h,non_special_base S A f h⟩
    · intro f inc ordinary; exact ⟨inc,ordinary⟩
  obtain ⟨D,pool,cost,dep⟩ := mono_frontier run
  by_contra! small
  have few : D.card<P.card := by omega
  let clean := D.filter fun f => f (onSet ∅)=false ∧ foot f⊆S
  let seen := clean.biUnion foot
  have single (f : Fn V) (hf : f∈clean) : (foot f).card≤1 := by
    have h := Finset.mem_filter.mp hf
    have no := (pool f h.1).2
    by_contra! big
    exact no ⟨h.2.1,h.2.2,big⟩
  have cardSeen : seen.card≤D.card := calc
    seen.card ≤ ∑ f∈clean, (foot f).card := Finset.card_biUnion_le
    _ ≤ ∑ _f∈clean, 1 := Finset.sum_le_sum single
    _ ≤ D.card := by simpa using (Finset.card_filter_le D _)
  obtain ⟨i,hi,miss⟩ := Finset.exists_mem_notMem_of_card_lt_card (cardSeen.trans_lt few)
  let dirt := D.filter fun f => ¬foot f⊆S
  have chooseW (f : Fn V) (hf : f∈dirt) : ∃ j, j∈foot f ∧ j∉S := by
    have no := (Finset.mem_filter.mp hf).2
    simpa [Finset.subset_iff] using no
  let W := dirt.attach.image fun f => (chooseW f.val f.property).choose
  have cardW : W.card<P.card := by
    have h := Finset.card_image_le (s:=dirt.attach) (f:=fun f => (chooseW f.val f.property).choose)
    simp only [Finset.card_attach] at h
    exact h.trans_lt ((Finset.card_filter_le D _).trans_lt few)
  have dis : Disjoint W S := by
    apply Finset.disjoint_left.mpr
    rintro j hj
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hj
    exact (chooseW _ f.property).choose_spec.2
  have bad := neg W dis cardW
  have yes := dep (onSet {i}) (onSet W) (by
    intro f hf fp
    have inc := (pool _ hf).1
    by_cases zero : f (onSet ∅)=true
    · exact inc _ _ (Finset.empty_subset _) zero
    by_cases dirty : ¬foot f⊆S
    · have hd : f∈dirt := Finset.mem_filter.mpr ⟨hf,dirty⟩
      let j := (chooseW f hd).choose
      have belongs : j∈W := Finset.mem_image.mpr ⟨⟨f,hd⟩,Finset.mem_attach _ _,rfl⟩
      exact inc {j} W (Finset.singleton_subset_iff.mpr belongs)
        (Finset.mem_filter.mp (chooseW f hd).choose_spec.1).2
    · exfalso; apply miss; apply Finset.mem_biUnion.mpr
      exact ⟨f,Finset.mem_filter.mpr ⟨hf,Bool.eq_false_iff.mpr zero,not_not.mp dirty⟩,
        Finset.mem_filter.mpr ⟨by simp,fp⟩⟩) (pos i hi)
  simp_all

private theorem count_disjoint {J : Type*} [Fintype J] [DecidableEq J]
    (S : J → Finset V) (linear : ∀ i j, i≠j → ((S i)∩(S j)).card≤1)
    (gs : List (Node V)) :
    ∑ i, (gs.filter (fun g => decide (Special (S i) g.value))).length ≤ gs.length := by
  classical
  induction gs with
  | nil => simp
  | cons g gs ih =>
    let hits := Finset.univ.filter fun j => Special (S j) g.value
    have small : hits.card≤1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra ne
      obtain ⟨_,left,large⟩ := (Finset.mem_filter.mp hi).2
      obtain ⟨_,right,_⟩ := (Finset.mem_filter.mp hj).2
      have sub : foot g.value ⊆ (S i)∩(S j) := Finset.subset_inter left right
      have num := (Finset.card_le_card sub).trans (linear i j ne)
      omega
    have add (j : J) : ((g::gs).filter (fun u => decide (Special (S j) u.value))).length =
        (gs.filter (fun u => decide (Special (S j) u.value))).length +
        (if Special (S j) g.value then 1 else 0) := by
      by_cases h : Special (S j) g.value <;> simp [h]
    simp_rw [add]
    rw [Finset.sum_add_distrib]
    have count : (∑ j, if Special (S j) g.value then 1 else 0)=hits.card := by
      exact (Finset.card_filter _ _).symm
    rw [count,List.length_cons]; omega

theorem circuit_bound {J : Type*} [Fintype J] [DecidableEq J]
    (S P : J → Finset V) (F : J → Fn V) (gs : List (Node V)) (A : Finset V)
    (linear : ∀ i j, i≠j → ((S i)∩(S j)).card≤1)
    (ready : ∀ j, Ready (base A) gs (F j))
    (pos : ∀ j i, i∈P j → F j (onSet {i})=true)
    (neg : ∀ j U, Disjoint U (S j) → U.card<(P j).card → F j (onSet U)=false) :
    ∑ j, ((P j).card-1) ≤ gs.length := by
  have bound (j : J) := row_bound (S j) (P j) gs (F j) A (ready j) (pos j) (neg j)
  exact (Finset.sum_le_sum (fun j _ => by have := bound j; omega)).trans (count_disjoint S linear gs)

end Rows
end GateElim
#print axioms GateElim.Rows.circuit_bound
