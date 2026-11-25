import OrderedPeel
import PlaneRows
import Core

namespace GateElim.Plane
open Desk2008 Desk2008.Residual Desk2008.Fanout PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Finset Classical
attribute [-simp] Fin.natAdd_eq_addNat
variable {N q : ℕ}

noncomputable def box (P L : Finset (Fin N)) : Finset (Vertex N) :=
  Finset.univ.filter fun i => Fin.addCases (motive:=fun _ => Prop) (fun p => p∈P) (fun l => l∈L) i

@[simp] theorem in_left (P L : Finset (Fin N)) (p : Fin N) : left p∈box P L ↔ p∈P := by
  simp [box,left]
@[simp] theorem in_right (P L : Finset (Fin N)) (l : Fin N) : right l∈box P L ↔ l∈L := by
  simp [box,right]
@[simp] theorem in_pts (S : Finset (Vertex N)) (p : Fin N) : p∈pts S ↔ left p∈S := by simp [pts]
@[simp] theorem in_lns (S : Finset (Vertex N)) (l : Fin N) : l∈lns S ↔ right l∈S := by simp [lns]
@[simp] theorem pts_box (P L : Finset (Fin N)) : pts (box P L)=P := by ext; simp
@[simp] theorem lns_box (P L : Finset (Fin N)) : lns (box P L)=L := by ext; simp
@[simp] theorem card_box (P L : Finset (Fin N)) : (box P L).card=P.card+L.card := by simp [split_card]

theorem edge_iff (I : Fin N → Fin N → Prop) (S : Finset (Vertex N)) :
    EdgeIn (adj I) S ↔ ∃ p, left p∈S ∧ ∃ l, right l∈S ∧ I p l := by
  constructor
  · rintro ⟨u,hu,v,hv,p,l,pl,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
    · exact ⟨p,hu,l,hv,pl⟩
    · exact ⟨p,hv,l,hu,pl⟩
  · rintro ⟨p,hp,l,hl,pl⟩; exact ⟨_,hp,_,hl,(adjLR ..).mpr pl⟩

private theorem private_member (family : Fin N→Finset (Fin N)) (j : Fin N) (A K : Finset (Fin N))
    (inRow : K⊆family j) (absent : j∉A) (large : A.card<K.card)
    (linear : ∀ u v, u≠v → ((family u)∩(family v)).card≤1) :
    ∃ v∈K, ∀ r∈A, v∉family r := by
  let bad := A.biUnion (fun i => family j∩family i)
  have small : bad.card≤A.card := calc
    bad.card ≤ ∑ i∈A, (family j∩family i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i∈A, 1 := Finset.sum_le_sum (fun i hi => linear j i (fun e => absent (e ▸ hi)))
    _ = A.card := by simp
  obtain ⟨v,hv,miss⟩ := Finset.exists_mem_notMem_of_card_lt_card (small.trans_lt large)
  exact ⟨v,hv,fun r hr vr => miss (Finset.mem_biUnion.mpr ⟨r,hr,Finset.mem_inter.mpr ⟨inRow hv,vr⟩⟩)⟩

theorem desk_correct (q : ℕ) (I : Fin N→Fin N→Prop) (C : Circuit) (hm : Monotone2 C)
    (pos : ∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N→Bool, Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false) :
    Port.Correct (adj I) (fun S => (lns S).card≤q) univ (circuitFun (N+N) C) := by
  constructor
  · intro S _ edge
    obtain ⟨p,hp,l,hl,pl⟩ := (edge_iff I S).mp edge
    apply WireMono.mono C.gates hm _ _ _ C.output (pos _ _ pl)
    intro u on; rcases of_decide_eq_true on with rfl|rfl <;> simp_all [bits]
  · intro S _ legal free
    apply neg
    · simpa [Fintype.card_subtype,bits,lns] using legal
    · rintro ⟨p,l,pl,hp,hl⟩
      exact free ((edge_iff I S).mpr ⟨p,of_decide_eq_true hp,l,of_decide_eq_true hl,pl⟩)

@[simp] theorem lns_add_point (S : Finset (Vertex N)) (p : Fin N) : lns (insert (left p) S)=lns S := by
  ext l; simp [fun l p => Ne.symm (lr p l)]
@[simp] theorem pts_add_line (S : Finset (Vertex N)) (l : Fin N) : pts (insert (right l) S)=pts S := by
  ext p; simp [lr]
@[simp] theorem lns_add_line (S : Finset (Vertex N)) (l : Fin N) : lns (insert (right l) S)=insert l (lns S) := by
  ext r; simp
@[simp] theorem pts_add_point (S : Finset (Vertex N)) (p : Fin N) : pts (insert (left p) S)=insert p (pts S) := by
  ext r; simp
@[simp] theorem no_lines : lns (∅ : Finset (Vertex N))=∅ := by ext; simp
@[simp] theorem no_points : pts (∅ : Finset (Vertex N))=∅ := by ext; simp

/-- A deleted line has q+1 points. At most q other selected lines meet it at
at most q of those points. Add a private point to the negative input. -/
theorem delete_lines (q : ℕ) (hq : 1≤q) (I : Fin N→Fin N→Prop) [DecidableRel I]
    (ord : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (L : Finset (Fin N)) (survive : EdgeIn (adj I) (box univ L))
    {gs : List (Node (Vertex N))} {F : Fn (Vertex N)}
    (run : Ready (base univ) gs F) (good : Port.Correct (adj I) (fun S => (lns S).card≤q) univ F) :
    ∃ hs : List (Node (Vertex N)), ∃ G, Ready (base (box univ L)) hs G ∧
      Port.Correct (adj I) (fun S => (lns S).card≤q) (box univ L) G ∧ hs.length+2*(N-L.card)≤gs.length := by
  have ⟨deg,linear⟩ := row_geometry I ord hd hj false
  have small (i : Vertex N) (_ : i∈(univ : Finset _)) : (lns {i}).card≤q := by
    cases i using Fin.addCases with
    | left p => change (lns (insert (left p) ∅)).card≤q; rw [lns_add_point,no_lines]; simp
    | right l => change (lns (insert (right l) ∅)).card≤q; rw [lns_add_line,no_lines]; simpa using hq
  obtain ⟨hs,G,ready,ok,cost⟩ := Port.ordered (loopless I) univ (box univ L) (by simp)
    (fun S => (lns S).card≤q) survive (by simp) small (by
      intro i _ notB S _ absent legal free
      cases i using Fin.addCases with
      | left p => simp at notB
      | right l =>
        obtain ⟨p,hp,priv⟩ := private_member (rowSet false I) l (lns S) (rowSet false I l)
          (by rfl) (by simpa using absent) (legal.trans_lt (by rw [deg]; omega)) linear
        have pl : I p l := by simpa [rowSet] using hp
        let T := insert (left p) S
        refine ⟨T,Finset.insert_subset (by simp) Finset.subset_union_left,Finset.subset_insert ..,
          by simpa [T,fun l p => (lr p l).symm] using absent,by simpa [T] using legal,?_,?_⟩
        · intro yes; obtain ⟨u,hu,r,hr,ur⟩ := (edge_iff I T).mp yes
          have rin : right r∈S := (Finset.mem_insert.mp hr).resolve_left (lr _ _).symm
          rcases Finset.mem_insert.mp hu with ueq|uin
          · have e : u=p := Fin.castAdd_injective _ _ ueq
            exact priv r ((in_lns ..).mpr rin) (by simpa [rowSet,e] using ur)
          · exact free ((edge_iff I S).mpr ⟨u,uin,r,rin,ur⟩)
        · exact (edge_iff I _).mpr ⟨p,by simp [T],l,by simp,pl⟩) run good
  refine ⟨hs,G,ready,ok,?_⟩
  simpa [Nat.add_sub_add_left] using cost

end GateElim.Plane
#print axioms GateElim.Plane.delete_lines
