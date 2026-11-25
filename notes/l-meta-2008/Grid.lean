import PlaneOrdered

namespace GateElim.Plane
open Desk2008 Desk2008.Residual Finset Classical
variable {q N : ℕ}

/-- Coordinates supplied by two pencils after their common line is omitted. -/
structure Grid (q N : ℕ) (I : Fin N→Fin N→Prop) where
  row : Fin q → Fin N
  col : Fin q → Fin N
  cell : Fin q × Fin q → Fin N
  row_inj : Function.Injective row
  col_inj : Function.Injective col
  separate : ∀ a b, row a ≠ col b
  incRow : ∀ x u, I (cell x) (row u) ↔ x.1=u
  incCol : ∀ x u, I (cell x) (col u) ↔ x.2=u

theorem plane_grid (I : Fin N→Fin N→Prop) [DecidableRel I] (hq : 2≤q)
    (ord : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) : Nonempty (Grid q N I) := by
  classical
  obtain ⟨pd,meet⟩ := dual_axioms I ord hd hj
  let A : Fin N := ⟨0,by omega⟩
  let B : Fin N := ⟨1,by omega⟩
  have diff : A≠B := fun e => by have := congrArg Fin.val e; simp [A,B] at this
  obtain ⟨k,⟨ak,bk⟩,uniq⟩ := hj A B diff
  let pencil (p : Fin N) := (Finset.univ.filter (I p)).erase k
  have len (p : Fin N) (pk : I p k) : (pencil p).card=q := by
    have orig : (univ.filter (I p)).card=q+1 := by simpa [Fintype.card_subtype] using pd p
    have mem : k∈univ.filter (I p) := Finset.mem_filter.mpr ⟨by simp,pk⟩
    have eq := Finset.card_erase_add_one mem
    change ((Finset.univ.filter (I p)).erase k).card=q; omega
  let enumerate (p : Fin N) (pk : I p k) := ((pencil p).equivFinOfCardEq (len p pk)).symm
  let row (i : Fin q) := (enumerate A ak i).val
  let col (i : Fin q) := (enumerate B bk i).val
  have ra (i : Fin q) := Finset.mem_erase.mp (enumerate A ak i).property
  have cb (i : Fin q) := Finset.mem_erase.mp (enumerate B bk i).property
  have onA (i : Fin q) : I A (row i) := (Finset.mem_filter.mp (ra i).2).2
  have onB (i : Fin q) : I B (col i) := (Finset.mem_filter.mp (cb i).2).2
  have aOff (i : Fin q) : ¬I A (col i) := fun h => (cb i).1 (uniq _ ⟨h,onB i⟩)
  have bOff (i : Fin q) : ¬I B (row i) := fun h => (ra i).1 (uniq _ ⟨onA i,h⟩)
  have split (i j : Fin q) : row i≠col j := fun h => aOff j (h ▸ onA i)
  let cell (u : Fin q×Fin q) := (meet (row u.1) (col u.2) (split u.1 u.2)).choose
  have both (u : Fin q×Fin q) : I (cell u) (row u.1) ∧ I (cell u) (col u.2) :=
    (meet (row u.1) (col u.2) (split u.1 u.2)).choose_spec.1
  have ir : Function.Injective row := fun _ _ h => (enumerate A ak).injective (Subtype.ext h)
  have ic : Function.Injective col := fun _ _ h => (enumerate B bk).injective (Subtype.ext h)
  refine ⟨⟨row,col,cell,ir,ic,split,?_,?_⟩⟩
  · intro u i
    have ne : cell u≠A := fun e => aOff u.2 (e ▸ (both u).2)
    exact ⟨fun ui => ir ((hj _ _ ne).unique ⟨(both u).1,onA _⟩ ⟨ui,onA _⟩),fun e => e ▸ (both u).1⟩
  · intro u i
    have ne : cell u≠B := fun e => bOff u.1 (e ▸ (both u).1)
    exact ⟨fun ui => ic ((hj _ _ ne).unique ⟨(both u).2,onB _⟩ ⟨ui,onB _⟩),fun e => e ▸ (both u).2⟩

namespace Grid
variable {I : Fin N→Fin N→Prop} (g : Grid q N I)
theorem injective : Function.Injective g.cell := by
  intro u v e
  exact Prod.ext ((g.incRow u v.1).mp (e ▸ (g.incRow v v.1).mpr rfl))
    ((g.incCol u v.2).mp (e ▸ (g.incCol v v.2).mpr rfl))

def lines := Finset.univ.image g.row ∪ Finset.univ.image g.col
def points := Finset.univ.image g.cell
theorem lines_card : g.lines.card=2*q := by
  have dis : Disjoint (univ.image g.row) (univ.image g.col) := by
    apply Finset.disjoint_left.mpr; rintro l hl hk
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨v,_,eq⟩ := Finset.mem_image.mp hk
    exact g.separate u v eq.symm
  simp [lines,Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ g.row_inj,
    Finset.card_image_of_injective _ g.col_inj,two_mul]
theorem points_card : g.points.card=q^2 := by
  simp [points,Finset.card_image_of_injective _ g.injective,pow_two]

end Grid
end GateElim.Plane
#print axioms GateElim.Plane.plane_grid
