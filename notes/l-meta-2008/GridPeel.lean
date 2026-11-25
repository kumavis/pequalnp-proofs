import GridDomain

namespace GateElim.Plane.Grid
open Desk2008 Finset Classical
attribute [-simp] Fin.natAdd_eq_addNat
variable {q N : ℕ} {I : Fin N→Fin N→Prop}

def keep (q t : ℕ) := Finset.univ \ triangle q t
@[simp] theorem kept (t : ℕ) (u : XY q) : u∈keep q t ↔ t≤rank u := by simp [keep,triangle]
theorem region_mono (g : Grid q N I) {A B : Finset (XY q)} (s : A⊆B) :
    g.region A ⊆ g.region B := by
  intro i; cases i using Fin.addCases with
  | left p =>
    intro h; apply (in_left ..).mpr
    obtain ⟨u,hu,e⟩ := Finset.mem_image.mp ((in_left (A.image g.cell) g.lines p).mp h)
    exact Finset.mem_image.mpr ⟨u,s hu,e⟩
  | right l => simp [region]

theorem keep_edge (g : Grid q N I) (t : ℕ) (room : t+2≤q) : EdgeIn (adj I) (g.region (keep q t)) := by
  let u : XY q := (⟨0,by omega⟩,⟨t,by omega⟩)
  have h : u∈keep q t := by simp [u,rank]
  exact (edge_iff I _).mpr ⟨g.cell u,(in_left ..).mpr (Finset.mem_image.mpr ⟨u,h,rfl⟩),
    g.row u.1,(in_right ..).mpr (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_,by simp,rfl⟩)),(g.incRow ..).mpr rfl⟩

theorem ordered_grid (g : Grid q N I) (t : ℕ) (room : t+2≤q) {gs : List (Node (Vertex N))} {F : Fn (Vertex N)}
    (run : Ready (base (g.region univ)) gs F) (ok : Port.Correct (adj I) (g.permit t) (g.region univ) F) :
    ∃ hs : List (Node (Vertex N)), ∃ G, Ready (base (g.region (keep q t))) hs G ∧
      Port.Correct (adj I) (g.permit t) (g.region (keep q t)) G ∧ hs.length+2*(triangle q t).card≤gs.length := by
  classical
  have loop (U : Finset (XY q)) (sub : keep q t⊆U) {gs : List (Node (Vertex N))} {F : Fn (Vertex N)}
      (run : Ready (base (g.region U)) gs F) (ok : Port.Correct (adj I) (g.permit t) (g.region U) F) :
      ∃ hs : List (Node (Vertex N)), ∃ G, Ready (base (g.region (keep q t))) hs G ∧
        Port.Correct (adj I) (g.permit t) (g.region (keep q t)) G ∧ hs.length+2*(U.card-(keep q t).card)≤gs.length := by
    induction U using Finset.strongInduction generalizing gs F with
    | H U ih =>
      by_cases done : U=keep q t
      · subst U; exact ⟨gs,F,run,ok,by simp⟩
      obtain ⟨u,hu,no⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,Ne.symm done⟩))
      have small : rank u<t := by simpa using no
      let vals := U.image rank
      have ne : vals.Nonempty := ⟨rank u,Finset.mem_image.mpr ⟨u,hu,rfl⟩⟩
      obtain ⟨v,hv,mv⟩ := Finset.mem_image.mp (vals.min'_mem ne)
      have first (z : XY q) (hz : z∈U) : rank v≤rank z := mv ▸ vals.min'_le _ (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
      have low := (first u hu).trans_lt small
      have remain : keep q t⊆U.erase v := by
        intro x hx; exact Finset.mem_erase.mpr ⟨fun h => (Nat.not_le_of_lt low) ((kept ..).mp (h ▸ hx)),sub hx⟩
      have survive : EdgeIn (adj I) ((g.region U).erase (left (g.cell v))) := by
        rw [g.erase_cell]
        obtain ⟨a,ha,b,hb,e⟩ := g.keep_edge t room
        exact ⟨a,g.region_mono remain ha,b,g.region_mono remain hb,e⟩
      obtain ⟨rest,H,ready,good,cost⟩ := Port.step (A:=g.region U) (loopless I) (left (g.cell v))
        ((in_left ..).mpr (Finset.mem_image.mpr ⟨v,hv,rfl⟩)) (g.permit t) survive
        (g.small_tests t ∅ (by simp) (by simp))
        (g.small_tests t {left (g.cell v)} (by change (pts (insert _ ∅)).card≤1; rw [pts_add_point,no_points]; simp)
          (by change (lns (insert _ ∅)).card≤2; rw [lns_add_point,no_lines]; simp))
        (by rw [g.erase_cell]; exact g.legal_witness t U v low first) run ok
      rw [g.erase_cell] at ready good
      obtain ⟨hs,G,r,yes,spent⟩ := ih _ (Finset.erase_ssubset hv) remain ready good
      have card := Finset.card_erase_add_one hv; have le := Finset.card_le_card remain
      exact ⟨hs,G,r,yes,by omega⟩
  obtain ⟨hs,G,r,yes,spent⟩ := loop univ (by simp) run ok
  have eq := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (triangle q t))
  change (keep q t).card+(triangle q t).card=univ.card at eq
  exact ⟨hs,G,r,yes,by omega⟩

theorem strong_keep (g : Grid q N I) (t : ℕ) (room : t+2≤q) :
    ∀ i∈g.region (keep q t), Strong (adj I) (g.region (keep q t)) i := by
  let hi : Fin q := ⟨t,by omega⟩
  let hj : Fin q := ⟨t+1,by omega⟩
  have ne : hi≠hj := fun h => by have := congrArg Fin.val h; simp [hi,hj] at this
  intro i member; cases i using Fin.addCases with
  | left p =>
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp ((in_left ..).mp member)
    exact ⟨right (g.row u.1),(in_right ..).mpr (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_,by simp,rfl⟩)),
      right (g.col u.2),(in_right ..).mpr (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,by simp,rfl⟩)),
      fun eq => g.separate _ _ (Fin.natAdd_injective _ _ eq),
      (adjLR ..).mpr ((g.incRow ..).mpr rfl),(adjLR ..).mpr ((g.incCol ..).mpr rfl)⟩
  | right l =>
    have has (u : XY q) (h : t≤rank u) : left (g.cell u)∈g.region (keep q t) :=
      (in_left ..).mpr (Finset.mem_image.mpr ⟨u,(kept ..).mpr h,rfl⟩)
    rcases Finset.mem_union.mp ((in_right ..).mp member) with left|right
    · obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp left
      exact ⟨_,has (r,hi) (by dsimp [hi,rank]; omega),_,has (r,hj) (by dsimp [hj,rank]; omega),
        fun eq => ne (congrArg Prod.snd (g.injective (Fin.castAdd_injective _ _ eq))),
        (adjRL ..).mpr ((g.incRow ..).mpr rfl),(adjRL ..).mpr ((g.incRow ..).mpr rfl)⟩
    · obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp right
      exact ⟨_,has (hi,c) (by dsimp [hi,rank]; omega),_,has (hj,c) (by dsimp [hj,rank]; omega),
        fun eq => ne (congrArg Prod.fst (g.injective (Fin.castAdd_injective _ _ eq))),
        (adjRL ..).mpr ((g.incCol ..).mpr rfl),(adjRL ..).mpr ((g.incCol ..).mpr rfl)⟩

end GateElim.Plane.Grid
#print axioms GateElim.Plane.Grid.ordered_grid
