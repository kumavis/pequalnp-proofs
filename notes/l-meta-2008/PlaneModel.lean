import Peeling
import DeskBridge
import ResidualDual

namespace GateElim.Plane
open Desk2008 Desk2008.Residual PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Finset Classical
variable {N : ℕ}
abbrev Vertex (N : ℕ) := Fin (N+N)
def pts (A : Finset (Vertex N)) := Finset.univ.filter (fun p => left p∈A)
def lns (A : Finset (Vertex N)) := Finset.univ.filter (fun l => right l∈A)

theorem split_card (A : Finset (Vertex N)) : A.card=(pts A).card+(lns A).card := by
  classical
  have split : A=(pts A).image left ∪ (lns A).image right := by
    ext u
    induction u using Fin.addCases with
    | left p =>
      simp only [Finset.mem_union,Finset.mem_image,pts,lns,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · intro h; exact Or.inl ⟨p,h,rfl⟩
      · rintro (⟨j,hj,e⟩|⟨j,_,e⟩)
        · exact e ▸ hj
        · exact (lr p j e.symm).elim
    | right l =>
      simp only [Finset.mem_union,Finset.mem_image,pts,lns,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · intro h; exact Or.inr ⟨l,h,rfl⟩
      · rintro (⟨j,_,e⟩|⟨j,hj,e⟩)
        · exact (lr j l e).elim
        · exact e ▸ hj
  have dis : Disjoint ((pts A).image left) ((lns A).image right) := by
    apply Finset.disjoint_left.mpr
    rintro u hu hv
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨l,_,e⟩ := Finset.mem_image.mp hv
    exact lr p l e.symm
  calc
    A.card = ((pts A).image left ∪ (lns A).image right).card := congrArg Finset.card split
    _ = _ := by rw [Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ (Fin.castAdd_injective _ _),
                  Finset.card_image_of_injective _ (Fin.natAdd_injective _ _)]

private theorem left_neighbor {I : Fin N → Fin N → Prop} {p : Fin N} {u : Vertex N}
    (h : adj I (left p) u) : ∃ l, u=right l ∧ I p l := by
  induction u using Fin.addCases with
  | left r => exact (adjLL _ _ _ h).elim
  | right l => exact ⟨l,rfl,(adjLR _ _ _).mp h⟩

private theorem right_neighbor {I : Fin N → Fin N → Prop} {l : Fin N} {u : Vertex N}
    (h : adj I (right l) u) : ∃ p, u=left p ∧ I p l := by
  induction u using Fin.addCases with
  | left p => exact ⟨p,rfl,(adjRL _ _ _).mp h⟩
  | right r => exact (adjRR _ _ _ h).elim

theorem separated (I : Fin N → Fin N → Prop)
    (join : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) : Separates (adj I) := by
  intro i j a b ij ab ia ib
  induction i using Fin.addCases with
  | left p =>
    obtain ⟨l,rfl,pl⟩ := left_neighbor ia
    obtain ⟨m,rfl,pm⟩ := left_neighbor ib
    induction j using Fin.addCases with
    | left r =>
      have pr : p≠r := fun e => ij (e ▸ rfl)
      by_cases rl : I r l
      · have rm : ¬I r m := fun h => ab (congrArg right ((join p r pr).unique ⟨pl,rl⟩ ⟨pm,h⟩))
        exact Or.inr ⟨(lr _ _).symm,fun h => rm ((adjLR _ _ _).mp h)⟩
      · exact Or.inl ⟨(lr _ _).symm,fun h => rl ((adjLR _ _ _).mp h)⟩
    | right r =>
      by_cases eq : right l=right r
      · exact Or.inr ⟨fun h => ab (eq.trans h.symm),adjRR _ _ _⟩
      · exact Or.inl ⟨eq,adjRR _ _ _⟩
  | right l =>
    obtain ⟨p,rfl,pl⟩ := right_neighbor ia
    obtain ⟨r,rfl,rl⟩ := right_neighbor ib
    induction j using Fin.addCases with
    | left s =>
      by_cases eq : left p=left s
      · exact Or.inr ⟨fun h => ab (eq.trans h.symm),adjLL _ _ _⟩
      · exact Or.inl ⟨eq,adjLL _ _ _⟩
    | right m =>
      by_cases pm : I p m
      · have pr : p≠r := fun e => ab (e ▸ rfl)
        have rm : ¬I r m := fun h => ij (congrArg right ((join p r pr).unique ⟨pl,rl⟩ ⟨pm,h⟩))
        exact Or.inr ⟨lr _ _,fun h => rm ((adjRL _ _ _).mp h)⟩
      · exact Or.inl ⟨lr _ _,fun h => pm ((adjRL _ _ _).mp h)⟩

noncomputable def weak (I : Fin N → Fin N → Prop) (A : Finset (Vertex N)) : Finset (Vertex N) :=
  Finset.univ.filter fun i => ¬Strong (adj I) A i

theorem low_left (I : Fin N → Fin N → Prop) [DecidableRel I] (A : Finset (Vertex N)):
    pts (weak I A) ⊆ Finset.univ.filter (fun p => degree I (lns A) p≤1) := by
  intro p hp
  apply Finset.mem_filter.mpr
  refine ⟨by simp,?_⟩
  by_contra! high
  obtain ⟨a,b,ha,hb,ne⟩ := Finset.one_lt_card_iff.mp high
  obtain ⟨aa,pa⟩ := Finset.mem_filter.mp ha
  obtain ⟨bb,pb⟩ := Finset.mem_filter.mp hb
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).2).2
    ⟨right a,(Finset.mem_filter.mp aa).2,right b,(Finset.mem_filter.mp bb).2,
    fun e => ne (Fin.natAdd_injective _ _ e),(adjLR _ _ _).mpr pa,(adjLR _ _ _).mpr pb⟩

theorem low_right (I : Fin N → Fin N → Prop) [DecidableRel I] (A : Finset (Vertex N)):
    lns (weak I A) ⊆ Finset.univ.filter (fun l => degree (fun l p => I p l) (pts A) l≤1) := by
  intro l hl
  apply Finset.mem_filter.mpr
  refine ⟨by simp,?_⟩
  by_contra! high
  obtain ⟨a,b,ha,hb,ne⟩ := Finset.one_lt_card_iff.mp high
  obtain ⟨aa,pa⟩ := Finset.mem_filter.mp ha
  obtain ⟨bb,pb⟩ := Finset.mem_filter.mp hb
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hl).2).2
    ⟨left a,(Finset.mem_filter.mp aa).2,left b,(Finset.mem_filter.mp bb).2,
    fun e => ne (Fin.castAdd_injective _ _ e),(adjRL _ _ _).mpr pa,(adjRL _ _ _).mpr pb⟩

theorem desk_fits (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (q : ℕ) (hq : 2≤q)
    (pos : ∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N → Bool, Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false) :
    Fits (adj I) Finset.univ (circuitFun (N+N) C) := by
  classical
  intro S _
  constructor
  · intro count independent
    apply neg
    · rw [Fintype.card_subtype]
      let L := Finset.univ.filter fun l : Fin N => bits S (right l)=true
      have sub : L.image right ⊆ S := by
        intro u hu; obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hu
        exact of_decide_eq_true (Finset.mem_filter.mp hl).2
      have c := Finset.card_le_card sub
      rw [Finset.card_image_of_injective L (Fin.natAdd_injective _ _)] at c
      exact c.trans (count.trans hq)
    · rintro ⟨p,l,pl,pon,lon⟩
      exact independent ⟨left p,of_decide_eq_true pon,right l,of_decide_eq_true lon,(adjLR _ _ _).mpr pl⟩
  · rintro ⟨i,hi,j,hj,p,l,pl,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
    all_goals
      apply WireMono.mono C.gates hm _ _ _ C.output (pos p l pl)
      intro u e
      rcases of_decide_eq_true e with rfl|rfl <;> simp_all [bits]

end GateElim.Plane
#print axioms GateElim.Plane.desk_fits
