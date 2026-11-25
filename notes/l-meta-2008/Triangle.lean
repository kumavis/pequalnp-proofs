import Grid

namespace GateElim.Plane.Grid
open Desk2008 Finset Classical
variable {q N : ℕ} {I : Fin N→Fin N→Prop}
abbrev XY (q : ℕ) := Fin q × Fin q
def rank (u : XY q) := u.1.val+u.2.val
def triangle (q t : ℕ) : Finset (XY q) := Finset.univ.filter fun u => rank u<t

private theorem diagonal (t : ℕ) (lt : t<q) :
    (Finset.univ.filter fun u : XY q => rank u=t).card=t+1 := by
  let index (i : Fin (t+1)) : XY q := (⟨i.val,by omega⟩,⟨t-i.val,by omega⟩)
  have inj : Function.Injective index := fun _ _ h => Fin.ext (congrArg (fun u : XY q => u.1.val) h)
  have eq : univ.filter (fun u : XY q => rank u=t)=univ.image index := by
    ext u; simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · intro h
      change u.1.val+u.2.val=t at h
      exact ⟨⟨u.1.val,by omega⟩,Prod.ext rfl (Fin.ext (by dsimp [index]; omega))⟩
    · rintro ⟨i,rfl⟩; dsimp [rank,index]; omega
  rw [eq,Finset.card_image_of_injective _ inj]; simp

theorem triangle_card (t : ℕ) (ht : t≤q) : 2*(triangle q t).card=t*(t+1) := by
  induction t with
  | zero => simp [triangle]
  | succ t ih =>
    let D := univ.filter fun u : XY q => rank u=t
    have dis : Disjoint (triangle q t) D := by
      apply Finset.disjoint_left.mpr; intro u a b
      have h := (Finset.mem_filter.mp a).2; have e := (Finset.mem_filter.mp b).2; omega
    have eq : triangle q (t+1)=triangle q t ∪ D := by
      ext u; simp only [triangle,D,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]; omega
    rw [eq,Finset.card_union_of_disjoint dis]
    have d : D.card=t+1 := diagonal t (by omega)
    have prev := ih (by omega); rw [d]; nlinarith

def initial (q k : ℕ) := univ.filter fun i : Fin q => i.val<k
theorem initial_card (q k : ℕ) : (initial q k).card≤k := by
  have sub : (initial q k).image Fin.val ⊆ Finset.range k := by
    rintro x h; obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  simpa [Finset.card_image_of_injective _ Fin.val_injective] using Finset.card_le_card sub

def blanket (g : Grid q N I) (t : ℕ) (u : XY q) :=
  (initial q (min u.1.val t)).image g.row ∪ (initial q (min u.2.val (t-min u.1.val t))).image g.col
def emptyBlanket (g : Grid q N I) (t : ℕ) := (initial q t).image g.row

theorem blanket_cost (g : Grid q N I) (t : ℕ) (u : XY q) : (blanket g t u).card≤t := by
  have r := (Finset.card_image_le (f:=g.row) (s:=initial q (min u.1.val t))).trans (initial_card ..)
  have c := (Finset.card_image_le (f:=g.col) (s:=initial q (min u.2.val (t-min u.1.val t)))).trans (initial_card ..)
  exact (Finset.card_union_le ..).trans (by omega)

theorem empty_cost (g : Grid q N I) (t : ℕ) : (emptyBlanket g t).card≤t :=
  Finset.card_image_le.trans (initial_card ..)

theorem witness (g : Grid q N I) (t : ℕ) (u v : XY q) (low : rank v<t)
    (order : rank v≤rank u) (diff : v≠u) :
    ∃ l∈blanket g t u, l∈g.lines ∧ I (g.cell v) l ∧ ¬I (g.cell u) l := by
  let r := min u.1.val t
  let c := min u.2.val (t-r)
  have either : v.1.val<r ∨ v.2.val<c := by
    by_contra! miss
    have ne : v.1.val≠u.1.val ∨ v.2.val≠u.2.val := by
      by_contra! eq; exact diff (Prod.ext (Fin.ext eq.1) (Fin.ext eq.2))
    dsimp [rank] at low order; dsimp [r,c] at miss; omega
  rcases either with hr|hc
  · refine ⟨g.row v.1,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v.1,by simpa [initial,r] using hr,rfl⟩),
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_,by simp,rfl⟩),(g.incRow ..).mpr rfl,?_⟩
    intro eq; have h := congrArg Fin.val ((g.incRow ..).mp eq); dsimp [r] at hr; omega
  · refine ⟨g.col v.2,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v.2,by simpa [initial,c,r] using hc,rfl⟩),
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,by simp,rfl⟩),(g.incCol ..).mpr rfl,?_⟩
    intro eq; have h := congrArg Fin.val ((g.incCol ..).mp eq); dsimp [c] at hc; omega

theorem empty_witness (g : Grid q N I) (t : ℕ) (v : XY q) (low : rank v<t) :
    ∃ l∈emptyBlanket g t, l∈g.lines ∧ I (g.cell v) l := by
  have le : v.1.val<t := by unfold rank at low; omega
  exact ⟨g.row v.1,Finset.mem_image.mpr ⟨v.1,by simpa [initial] using le,rfl⟩,
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_,by simp,rfl⟩),(g.incRow ..).mpr rfl⟩

end GateElim.Plane.Grid
#print axioms GateElim.Plane.Grid.witness
