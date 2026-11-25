import Mathlib

/-! A semantic straight-line program still counts physical binary gates. Labeling
the operands by the functions they compute permits restrictions to remove gates
without any renumbering. A separate module translates the desk's circuit model. -/
namespace GateElim
set_option linter.unusedSectionVars false
open Finset Classical
variable {V : Type*} [DecidableEq V]
abbrev Fn (V : Type*) := (V → Bool) → Bool
def var (i : V) : Fn V := fun x => x i
def const (b : Bool) : Fn V := fun _ => b
def base (A : Finset V) : Set (Fn V) := {f |
  (∃ b, f=const b) ∨ ∃ i∈A, f=var i}

structure Node (V : Type*) where
  useOr : Bool
  a : Fn V
  b : Fn V

def Node.value (g : Node V) : Fn V := fun x =>
  if g.useOr then g.a x || g.b x else g.a x && g.b x

def Ready (S : Set (Fn V)) : List (Node V) → Fn V → Prop
  | [], F => F∈S
  | g::gs, F => g.a∈S ∧ g.b∈S ∧ Ready (insert g.value S) gs F

theorem weaken {S T : Set (Fn V)} {gs : List (Node V)} {F : Fn V}
    (h : Ready S gs F) (st : S⊆T) : Ready T gs F := by
  induction gs generalizing S T with
  | nil => exact st h
  | cons g gs ih => exact ⟨st h.1,st h.2.1,ih h.2.2 (Set.insert_subset_insert st)⟩

def clamp (i : V) (F : Fn V) : Fn V := fun x => F (Function.update x i false)
def Reads (g : Node V) (i : V) : Prop := g.a=var i ∨ g.b=var i
noncomputable def restricted (i : V) (gs : List (Node V)) : List (Node V) :=
  (gs.filter (fun g => decide (¬Reads g i))).map fun g => ⟨g.useOr,clamp i g.a,clamp i g.b⟩

private theorem clamped_read (g : Node V) (i : V) (r : Reads g i) :
    clamp i g.value=const false ∨ clamp i g.value=clamp i g.a ∨ clamp i g.value=clamp i g.b := by
  rcases g with ⟨o,a,b⟩
  change a=var i ∨ b=var i at r
  rcases r with rfl|rfl <;> cases o <;> simp [funext_iff,clamp,Node.value,const,var]

theorem restrict_ready {S T : Set (Fn V)} (i : V) {gs : List (Node V)} {F : Fn V}
    (ready : Ready S gs F) (zero : const false ∈ T) (lift : ∀ f∈S, clamp i f∈T) :
    Ready T (restricted i gs) (clamp i F) := by
  induction gs generalizing S T with
  | nil => exact lift F ready
  | cons g gs ih =>
    by_cases r : Reads g i
    · simp only [restricted,List.filter_cons,decide_not,decide_eq_true_eq,r,decide_true,
        Bool.not_true,Bool.false_eq_true,↓reduceIte]
      apply ih ready.2.2 zero
      intro f hf
      rcases hf with e|hf
      · subst f
        rcases clamped_read g i r with eq|eq|eq
        · simpa [eq] using zero
        · simpa [eq] using lift g.a ready.1
        · simpa [eq] using lift g.b ready.2.1
      · exact lift f hf
    · simp only [restricted,List.filter_cons,decide_not,r,decide_false,Bool.not_false,
        ↓reduceIte,List.map_cons]
      refine ⟨lift _ ready.1,lift _ ready.2.1,ih ready.2.2 (Set.mem_insert_of_mem _ zero) ?_⟩
      intro f hf
      rcases hf with e|hs
      · subst f; exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (lift _ hs)

theorem restrict_base (A : Finset V) (i : V) {gs : List (Node V)} {F : Fn V}
    (ready : Ready (base A) gs F) : Ready (base (A.erase i)) (restricted i gs) (clamp i F) := by
  apply restrict_ready i ready (Or.inl ⟨_,rfl⟩)
  intro f hf
  rcases hf with ⟨b,rfl⟩|⟨u,hu,rfl⟩
  · exact Or.inl ⟨_,rfl⟩
  · by_cases e : u=i
    · subst u; exact Or.inl ⟨false,by funext x; simp [clamp,var,const]⟩
    · exact Or.inr ⟨u,Finset.mem_erase.mpr ⟨e,hu⟩,by funext x; simp [clamp,var,e]⟩

/-- A tail that never reads a given variable can see it only through other
functions already in its input pool. -/
private theorem no_read {S : Set (Fn V)} {gs : List (Node V)} {F : Fn V}
    (ready : Ready S gs F) (i : V) (unused : ∀ g∈gs, ¬Reads g i) (nonvar : F≠var i)
    (x y : V → Bool) (agree : ∀ f∈S, f≠var i → f x=f y) : F x=F y := by
  induction gs generalizing S with
  | nil => exact agree _ ready nonvar
  | cons g gs ih =>
    have notread := unused g (by simp)
    have a := agree _ ready.1 (fun e => notread (Or.inl e))
    have b := agree _ ready.2.1 (fun e => notread (Or.inr e))
    apply ih ready.2.2 (fun k hk => unused k (by simp [hk]))
    intro f hf ne
    rcases hf with e|inS
    · subst f; simp [Node.value,a,b]
    · exact agree _ inS ne

def RobustAgainst (F : Fn V) (i j : V) : Prop := ∀ z : Bool, ∃ x y : V → Bool,
  (∀ u, u≠i → x u=y u) ∧ x j=z ∧ y j=z ∧ F x≠F y

def Essential (F : Fn V) (i : V) : Prop := ∃ x y : V → Bool,
  (∀ u, u≠i → x u=y u) ∧ F x≠F y

private theorem collapsed (g : Node V) {i j : V} (ha : g.a=var i) (hb : g.b=var j) :
    ∃ z, ∀ x y : V → Bool, x j=z → y j=z → g.value x=g.value y := by
  refine ⟨g.useOr,?_⟩
  intro x y hx hy
  cases e : g.useOr <;> simp_all [Node.value,var]

private theorem another_read (A : Finset V) (g : Node V) (gs : List (Node V)) (F : Fn V)
    (ready : Ready (base A) (g::gs) F) {i j : V} (ha : g.a=var i) (hb : g.b=var j)
    (nonvar : F≠var i) (rob : RobustAgainst F i j) : ∃ k∈gs, Reads k i := by
  by_contra! missing
  obtain ⟨z,absorb⟩ := collapsed g ha hb
  obtain ⟨x,y,agree,hx,hy,changeF⟩ := rob z
  apply changeF
  apply no_read ready.2.2 i missing nonvar x y
  intro f hf ne
  rcases hf with e|h
  · subst f; exact absorb x y hx hy
  · rcases h with ⟨c,rfl⟩|⟨u,_,rfl⟩
    · rfl
    · exact agree u (fun e => ne (e ▸ rfl))

private theorem len_drop {gs : List (Node V)} (i : V) (found : ∃ g∈gs, Reads g i) :
    (restricted i gs).length < gs.length := by
  obtain ⟨g,hg,hr⟩ := found
  simp only [restricted,List.length_map]
  exact List.length_filter_lt_length_iff_exists.mpr ⟨g,hg,by simp [hr]⟩

private theorem operands (A : Finset V) (g : Node V) (a : g.a∈base A) (b : g.b∈base A)
    (new : g.value∉base A) : ∃ i∈A, ∃ j∈A, i≠j ∧ g.a=var i ∧ g.b=var j := by
  have easy : ∀ (f : Fn V), (f=const false ∨ f=const true ∨ f=g.a ∨ f=g.b) → f∈base A := by
    rintro f (rfl|rfl|rfl|rfl)
    · exact Or.inl ⟨_,rfl⟩
    · exact Or.inl ⟨_,rfl⟩
    · exact a
    · exact b
  rcases a with ⟨c,ha⟩|⟨i,hi,ha⟩ <;> rcases b with ⟨d,hb⟩|⟨j,hj,hb⟩
  · exfalso; apply new; apply easy; cases c <;> cases d <;> cases o : g.useOr <;>
      simp [funext_iff,Node.value,ha,hb,const,o]
  · exfalso; apply new; apply easy; cases c <;> cases o : g.useOr <;>
      simp [funext_iff,Node.value,ha,hb,const,o]
  · exfalso; apply new; apply easy; cases d <;> cases o : g.useOr <;>
      simp [funext_iff,Node.value,ha,hb,const,o]
  · refine ⟨i,hi,j,hj,?_,ha,hb⟩
    intro e; subst j; apply new
    have eq : g.value=g.a := by funext x; cases o : g.useOr <;> simp [Node.value,ha,hb,o]
    exact eq ▸ (Or.inr ⟨i,hi,ha⟩ : g.a∈base A)

theorem peel (A : Finset V) (gs : List (Node V)) (F : Fn V) (ready : Ready (base A) gs F)
    (notbase : F∉base A) (good : V → Prop)
    (rob : ∀ i∈A, good i → ∀ j∈A, i≠j → RobustAgainst F i j) :
    ∃ i∈A, ∃ rest : List (Node V), Ready (base (A.erase i)) rest (clamp i F) ∧
      rest.length+1+(if good i then 1 else 0) ≤ gs.length := by
  classical
  induction gs with
  | nil => exact (notbase ready).elim
  | cons g gs ih =>
    by_cases old : g.value∈base A
    · have tail := weaken ready.2.2 (Set.insert_subset old (by rfl))
      obtain ⟨i,hi,t,run,len⟩ := ih tail
      exact ⟨i,hi,t,run,by simp; omega⟩
    · obtain ⟨i,hi,j,hj,ne,ha,hb⟩ := operands A g ready.1 ready.2.1 old
      refine ⟨i,hi,restricted i (g::gs),restrict_base A i ready,?_⟩
      have reads : Reads g i := Or.inl ha
      have len : (restricted i (g::gs)).length=(restricted i gs).length := by
        simp [restricted,reads]
      rw [len,List.length_cons]
      by_cases best : good i
      · have nonvar : F≠var i := fun e => notbase (Or.inr ⟨i,hi,e⟩)
        have extra := len_drop i (another_read A g gs F ready ha hb nonvar (rob i hi best j hj ne))
        simp [best]; omega
      · have small : (restricted i gs).length ≤ gs.length := by simp [restricted,List.length_filter_le]
        simp [best]; omega

end GateElim
#print axioms GateElim.peel
