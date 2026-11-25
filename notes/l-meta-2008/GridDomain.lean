import Triangle

namespace GateElim.Port
open Finset Classical
variable {n : ℕ}
theorem restrict_sample {R : Fin n→Fin n→Prop} {K : Finset (Fin n)→Prop}
    (A B : Finset (Fin n)) (sub : B⊆A) {gs : List (Node (Fin n))} {F : Fn (Fin n)}
    (ready : Ready (base A) gs F) (valid : Correct R K A F) :
    ∃ hs : List (Node (Fin n)), ∃ H, Ready (base B) hs H ∧ Correct R K B H ∧ hs.length≤gs.length := by
  classical
  induction A using Finset.strongInduction generalizing gs F with
  | H A ih =>
    by_cases eq : A=B
    · subst A; exact ⟨gs,F,ready,valid,le_rfl⟩
    obtain ⟨i,hi,no⟩ := Finset.exists_mem_notMem_of_card_lt_card (Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨sub,Ne.symm eq⟩))
    have keep : B⊆A.erase i := fun u hu => Finset.mem_erase.mpr ⟨fun e => no (e ▸ hu),sub hu⟩
    have clamp_eq (S : Finset (Fin n)) (s : S⊆A.erase i) : clamp i F (bits S)=F (bits S) := by
      have miss : i∉S := fun h => Finset.notMem_erase _ _ (s h)
      unfold clamp; congr 1; funext j; by_cases eq : j=i <;> simp [eq,bits,miss]
    have ok : Correct R K (A.erase i) (clamp i F) := ⟨fun S s on => (clamp_eq S s).trans
      (valid.yes S (s.trans (Finset.erase_subset ..)) on),fun S s l off => (clamp_eq S s).trans
      (valid.no S (s.trans (Finset.erase_subset ..)) l off)⟩
    obtain ⟨hs,H,r,h,l⟩ := ih _ (Finset.erase_ssubset hi) keep (restrict_base A i ready) ok
    exact ⟨hs,H,r,h,l.trans (by simp [restricted,List.length_filter_le])⟩
end GateElim.Port

namespace GateElim.Plane.Grid
open Desk2008 Finset Classical
variable {q N : ℕ} {I : Fin N→Fin N→Prop}
attribute [-simp] Fin.natAdd_eq_addNat

noncomputable def region (g : Grid q N I) (U : Finset (XY q)) := box (U.image g.cell) g.lines

def permit (g : Grid q N I) (t : ℕ) (S : Finset (Vertex N)) : Prop :=
  (pts S).card≤1 ∧ ((pts S)=∅ → ((lns S) \ g.emptyBlanket t).card≤2) ∧
    ∀ u, g.cell u∈pts S → ((lns S) \ g.blanket t u).card≤2

theorem bounded (g : Grid q N I) (t : ℕ) (room : t+2≤q) (U : Finset (XY q))
    (S : Finset (Vertex N)) (sub : S⊆g.region U) (legal : g.permit t S) : (lns S).card≤q := by
  have count (W : Finset (Fin N)) (small : W.card≤t) (other : ((lns S)\W).card≤2) : (lns S).card≤q := by
    have h := Finset.card_sdiff_add_card_inter (lns S) W
    have inter := Finset.card_le_card (Finset.inter_subset_right (s₁:=lns S) (s₂:=W))
    omega
  by_cases miss : pts S=∅
  · exact count _ (g.empty_cost t) (legal.2.1 miss)
  · obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr miss
    have pin : p∈U.image g.cell := (in_left ..).mp (sub ((in_pts ..).mp hp))
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp pin
    exact count _ (g.blanket_cost t u) (legal.2.2 u hp)

theorem small_tests (g : Grid q N I) (t : ℕ) (S : Finset (Vertex N)) (point : (pts S).card≤1)
    (line : (lns S).card≤2) : g.permit t S :=
  ⟨point,fun _ => (Finset.card_le_card Finset.sdiff_subset).trans line,
    fun _ _ => (Finset.card_le_card Finset.sdiff_subset).trans line⟩

theorem erase_cell (g : Grid q N I) (U : Finset (XY q)) (v : XY q) :
    (g.region U).erase (left (g.cell v)) = g.region (U.erase v) := by
  ext i; cases i using Fin.addCases with
  | left p =>
    simp only [Finset.mem_erase,region,in_left,Fin.castAdd_inj,Finset.mem_image]
    constructor
    · rintro ⟨ne,u,hu,rfl⟩; exact ⟨u,⟨fun eq => ne (eq ▸ rfl),hu⟩,rfl⟩
    · rintro ⟨u,⟨ne,hu⟩,rfl⟩; exact ⟨fun eq => ne (g.injective (Fin.castAdd_injective _ _ eq)),u,hu,rfl⟩
  | right l => simp [region,fun l p => (lr p l).symm]

private theorem addition (L W : Finset (Fin N)) (l : Fin N) (hl : l∈W) :
    (insert l L)\W = L\W := by ext; simp; grind

theorem legal_witness (g : Grid q N I) (t : ℕ) (U : Finset (XY q)) (v : XY q)
    (low : rank v<t) (first : ∀ u∈U, rank v≤rank u) (S : Finset (Vertex N))
    (sub : S⊆g.region (U.erase v)) (ok : g.permit t S) (ind : ¬EdgeIn (adj I) S) :
    ∃ T⊆g.region (U.erase v), S⊆T ∧ g.permit t T ∧ ¬EdgeIn (adj I) T ∧ EdgeIn (adj I) (insert (left (g.cell v)) T) := by
  have add (l : Fin N) (hl : l∈g.lines) (on : I (g.cell v) l)
      (safe : ∀ p∈pts S, ¬I p l) (ok' : g.permit t (insert (right l) S)) :
      ∃ T⊆g.region (U.erase v), S⊆T ∧ g.permit t T ∧ ¬EdgeIn (adj I) T ∧ EdgeIn (adj I) (insert (left (g.cell v)) T) := by
    refine ⟨insert (right l) S,Finset.insert_subset ((in_right ..).mpr hl) sub,Finset.subset_insert ..,ok',?_,
      (edge_iff I _).mpr ⟨g.cell v,by simp,l,by simp,on⟩⟩
    intro e; obtain ⟨p,hp,r,hr,pr⟩ := (edge_iff I _).mp e
    have stay : left p∈S := (Finset.mem_insert.mp hp).resolve_left (lr _ _)
    rcases Finset.mem_insert.mp hr with eq|rin
    · have re : r=l := Fin.natAdd_injective _ _ eq
      exact safe p ((in_pts ..).mpr stay) (re ▸ pr)
    · exact ind ((edge_iff I S).mpr ⟨p,stay,r,rin,pr⟩)
  by_cases no : pts S=∅
  · obtain ⟨l,mask,hl,on⟩ := g.empty_witness t v low
    apply add l hl on (by simp [no])
    unfold permit; rw [pts_add_line,lns_add_line,no,addition _ _ _ mask]; simp [ok.2.1 no]
  · obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr no
    have member : p∈(U.erase v).image g.cell := (in_left ..).mp (sub ((in_pts ..).mp hp))
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp member
    obtain ⟨diff,old⟩ := Finset.mem_erase.mp hu
    obtain ⟨l,mask,hl,on,off⟩ := g.witness t u v low (first _ old) diff.symm
    have unique (p) (hp' : p∈pts S) : p=g.cell u := Finset.card_le_one.mp ok.1 _ hp' _ hp
    apply add l hl on (fun p hp => unique _ hp ▸ off)
    unfold permit; rw [pts_add_line,lns_add_line]
    refine ⟨ok.1,fun eq => (no eq).elim,?_⟩
    intro u' hu'; have e := g.injective (unique _ hu'); subst u'
    rw [addition _ _ _ mask]; exact ok.2.2 u hp

end GateElim.Plane.Grid
#print axioms GateElim.Plane.Grid.legal_witness
