import GridPeel
import ExactRows
import Cutoff

namespace GateElim.Plane
open Desk2008 Desk2008.Fanout PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Grid Finset Classical Reverse
attribute [-simp] Fin.natAdd_eq_addNat
variable {q N : ℕ} {I : Fin N → Fin N → Prop}

private theorem unpack {S : Set (Fn (Vertex N))} {gs : List (Node (Vertex N))} {F : Fn (Vertex N)}
    (h : Ready S gs F) : Built S gs ∧ F∈pool S gs := by
  induction gs generalizing S with
  | nil => exact ⟨True.intro,h⟩
  | cons g gs ih =>
    obtain ⟨bu,av⟩ := ih h.2.2
    exact ⟨⟨h.1,h.2.1,bu⟩,av⟩

/-- When two points and no line are selected the answer must be false.
A shared OR of the surviving line bits restores all these negative tests. -/
theorem line_guard (g : Grid q N I) (t : ℕ) (U : Finset (XY q))
    {gs : List (Node (Vertex N))} {F : Fn (Vertex N)}
    (ready : Ready (base (g.region U)) gs F) (ok : Port.Correct (adj I) (g.permit t) (g.region U) F) :
    ∃ hs : List (Node (Vertex N)), ∃ G, Ready (base (g.region U)) hs G ∧
      Fits (adj I) (g.region U) G ∧ hs.length≤gs.length+g.lines.card+1 := by
  obtain ⟨bu,av⟩ := unpack ready
  let S := base (g.region U)
  obtain ⟨ls,w,len,built,has,join⟩ := Cuts.join_values g.lines (fun l => var (right l)) (pool S gs)
    (fun l hl => pool_grows _ _ (Or.inr ⟨_,(in_right ..).mpr hl,rfl⟩))
    (pool_grows _ _ (Or.inl ⟨false,rfl⟩))
  let gate := Node.mk false F w
  have build : Built S (gs++ls++[gate]) := by
    apply build_append (build_append bu built); rw [pool_append]
    exact ⟨pool_grows _ _ av,has,True.intro⟩
  refine ⟨gs++ls++[gate],gate.value,ready_of_built build ?_,?_,by simp [len,Nat.add_assoc]⟩
  · rw [pool_append]; exact Set.mem_insert _ _
  · intro T sub
    constructor
    · intro small free
      by_cases none : (lns T)=∅
      · have zero : w (bits T)=false := by
          apply Bool.eq_false_iff.mpr; intro yes
          obtain ⟨l,_,on⟩ := (join _).mp yes
          have mem : l∈lns T := (in_lns ..).mpr (of_decide_eq_true on)
          simp [none] at mem
        simp [gate,Node.value,zero]
      · have le := split_card T
        have one := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr none)
        have no := ok.no T sub (g.small_tests t T (by omega) (by omega)) free
        simp [gate,Node.value,no]
    · intro hit; obtain ⟨p,hp,l,hl,_⟩ := (edge_iff I T).mp hit
      have line := (join (bits T)).mpr ⟨l,(in_right ..).mp (sub hl),decide_eq_true hl⟩
      simp [gate,Node.value,line,ok.yes T sub hit]

/-- The two forced deletion phases give an unrestricted gate lower bound,
using only the exact positivity/sparsity hypotheses of the desk. -/
theorem triangular_bound (q N t : ℕ) (hq : 2≤q) (room : t+2≤q)
    (I : Fin N→Fin N→Prop) [DecidableRel I] (C : Circuit)
    (ord : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C) (out : C.output<N+N+C.size) (norm : Normal (N+N) C)
    (pos : ∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N → Bool, Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false) :
    10*N+t*(t+1) ≤ 3*C.size+14*q+8 := by
  classical
  obtain ⟨g⟩ := plane_grid I hq ord hd hj
  obtain ⟨gs,len,run⟩ := from_desk C norm hm out
  have full := desk_correct q I C hm pos neg
  have smallBox : g.region univ ⊆ box univ g.lines := by
    intro i; cases i using Fin.addCases <;> simp [Grid.region]
  have still := (g.region_mono (Finset.subset_univ (keep q t))).trans smallBox
  obtain ⟨a,ha,b,hb,ab⟩ := g.keep_edge t room
  have edge : EdgeIn (adj I) (box univ g.lines) := ⟨a,still ha,b,still hb,ab⟩
  obtain ⟨hs,H,build,oks,cost⟩ := delete_lines q (by omega) I ord hd hj g.lines edge run full
  obtain ⟨ks,K,grid,okK,short⟩ := Port.restrict_sample _ _ smallBox build oks
  have tests := Port.correct_weaken okK (fun S sub allowed => g.bounded t room _ S sub allowed)
  obtain ⟨ps,G,paid,okG,peeled⟩ := g.ordered_grid t room grid tests
  obtain ⟨ls,W,live,fit,added⟩ := line_guard g t (keep q t) paid okG
  have count := triangle_card t (by omega : t≤q)
  have difference := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (triangle q t))
  change (keep q t).card+(triangle q t).card=(univ : Finset (XY q)).card at difference
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin] at difference
  have size : (g.region (keep q t)).card=(keep q t).card+2*q := by
    simp [Grid.region,Finset.card_image_of_injective _ g.injective,g.lines_card]
  have core := core_size (loopless I) (fun {_ _} h => adjSymm I h) (separated I hj) _ W ls live fit
    (by rw [size]; omega) (g.strong_keep t room)
  rw [size] at core
  rw [g.lines_card] at cost added
  have nq : N≥2*q := by nlinarith
  rw [←sq] at difference
  omega

theorem clean_bound {q N : ℕ} (I : Fin N→Fin N→Prop) [DecidableRel I] (C : Circuit)
    (hq : 2≤q) (ord : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C) (out : C.output<N+N+C.size) (norm : Normal (N+N) C)
    (pos : ∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Vertex N → Bool, Fintype.card {l : Fin N // x (right l)=true}≤q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false) :
    11*N ≤ 3*C.size+18*q+7 := by
  have h := triangular_bound q N (q-2) hq (by omega) I C ord hd hj hm out norm pos neg
  have eq : q=q-2+2 := by omega
  nlinarith [congrArg (fun v : ℕ => v^2) eq]

end GateElim.Plane
#print axioms GateElim.Plane.clean_bound
