import ExtendBackground

namespace GateElim.Plane.Background
open Desk2008 Reverse Cuts Products Rows Block Finset Classical
variable {N q : ℕ} {I : Fin N→Fin N→Prop} [DecidableRel I]

private theorem monotone_at (P : Prog n) (off k : ℕ) (x z : Fin n→Bool) (le : ∀ i,x i=true → z i=true) :
    atGate P off x k=some true → atGate P off z k=some true := by
  induction P generalizing off with
  | ret => simp [atGate]
  | @gate n op a b t ih =>
    have h : applyOp op (x a) (x b)=true → applyOp op (z a) (z b)=true := by
      have ha := le a; have hb := le b; cases op <;> simp [applyOp] <;> tauto
    by_cases eq : k=off
    · simpa [atGate,eq] using h
    · simp only [atGate,eq,↓reduceIte]
      apply ih; intro i; cases i using Fin.lastCases with
      | last => simpa only [snoc_last] using h
      | cast j => simpa only [snoc_old] using le j

private theorem persist_point (B C : Background I) (p : Fin N) (bp : B.points⊆C.points)
    (bl : B.lines⊆C.lines) (survives : p∈C.ptsOK) (i : Vertex N) :
    B.px i (onSet {p})=true → C.px i (onSet {p})=true := by
  have a := congrFun (B.pureX {p}) i; have b := congrFun (C.pureX {p}) i
  change B.px i (onSet {p})=_ at a; change C.px i (onSet {p})=_ at b; rw [a,b]
  intro on; apply decide_eq_true
  have mem := of_decide_eq_true on
  cases i using Fin.addCases with
  | left i =>
    rcases mem_union.mp ((in_left ..).mp mem) with old|add
    · exact (in_left ..).mpr (mem_union_left _ (bp old))
    · obtain rfl := mem_singleton.mp (mem_inter.mp add).1
      exact (in_left ..).mpr (mem_union_right _ (mem_inter.mpr ⟨mem_singleton_self _,survives⟩))
  | right i => exact (in_right ..).mpr (mem_union_left _ (bl (by simpa using (in_right ..).mp mem)))

private theorem persist_line (B C : Background I) (l : Fin N) (bp : B.points⊆C.points)
    (bl : B.lines⊆C.lines) (survives : l∈C.lnsOK) (i : Vertex N) :
    B.ly i (onSet {l})=true → C.ly i (onSet {l})=true := by
  have a := congrFun (B.pureY {l}) i; have b := congrFun (C.pureY {l}) i
  change B.ly i (onSet {l})=_ at a; change C.ly i (onSet {l})=_ at b; rw [a,b]
  intro on; apply decide_eq_true
  have mem := of_decide_eq_true on
  cases i using Fin.addCases with
  | right i =>
    rcases mem_union.mp ((in_right ..).mp mem) with old|add
    · exact (in_right ..).mpr (mem_union_left _ (bl old))
    · obtain rfl := mem_singleton.mp (mem_inter.mp add).1
      exact (in_right ..).mpr (mem_union_right _ (mem_inter.mpr ⟨mem_singleton_self _,survives⟩))
  | left i => exact (in_left ..).mpr (mem_union_left _ (bp (by simpa using (in_left ..).mp mem)))

/-- The chosen gate can never again be a genuine source of this same
incidence along any extension that keeps both endpoints available. -/
theorem fresh_source (P : Prog (N+N)) (B : Background I) (t q : ℕ) (room : B.lines.card+t+1≤q)
    (yes : ∀ S,EdgeIn (adj I) S → P.eval (bits S)=true)
    (no : ∀ S,(lns S).card≤q → ¬EdgeIn (adj I) S → P.eval (bits S)=false)
    (p l : Fin N) (hp : p∈B.ptsOK) (hl : l∈B.lnsOK) (inc : I p l)
    (miss : l∉endpointRows I t P B.px B.ly p)
    (g : Birth (Fin N)) (mem : g∈births P 0 B.px B.ly) (fire : g.fires (onSet {p}) (onSet {l})) :
    ∃ C : Background I, B.points⊆C.points ∧ B.lines⊆C.lines ∧ p∈C.ptsOK ∧ l∈C.lnsOK ∧
      ((C.points=B.points ∧ C.lines.card≤B.lines.card+t) ∨ (C.lines=B.lines ∧ C.points.card≤B.points.card+t)) ∧
      (∃ k∈births P 0 C.px C.ly,k.fires (onSet {p}) (onSet {l})) ∧
      ∀ D : Background I, C.points⊆D.points → C.lines⊆D.lines → p∈D.ptsOK → l∈D.lnsOK →
        ∀ k∈births P 0 D.px D.ly,k.fires (onSet {p}) (onSet {l}) → g.index≠k.index := by
  obtain ⟨C,cp,cl,px,ly,small,active⟩ := disable_source B t P p l hp hl miss g mem fire
  have remaining : C.lines.card+1≤q := by rcases small with a|a; omega; rw [a.1]; omega
  obtain ⟨new,_⟩ := residual_births q 1 (by decide) I C remaining P yes no p l px ly inc
  refine ⟨C,cp,cl,px,ly,small,new,?_⟩
  intro D a b pp ll k km kf same
  have off := separate_off P 0 D.px D.ly k km (onSet {p}) (onSet {l}) kf
  rw [same] at active
  rcases active with point|line
  · have on := monotone_at P 0 k.index _ _ (persist_point C D p a b pp) point
    simp [on] at off
  · have on := monotone_at P 0 k.index _ _ (persist_line C D l a b ll) line
    simp [on] at off

end GateElim.Plane.Background
#print axioms GateElim.Plane.Background.fresh_source
