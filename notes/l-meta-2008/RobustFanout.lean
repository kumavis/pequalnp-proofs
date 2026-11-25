import PlaneIncidence2008

/-! A gate-count bound for normalized monotone circuits whose function keeps each
input essential when one other input is fixed. Only input wires and gates lying on
a path to the output enter the count. Gate indices are wire indices throughout. -/
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation
namespace Desk2008.Fanout

/-- The predecessor set is empty for input wires and out-of-range indices. -/
def pred (n : ℕ) (C : Circuit) (v : ℕ) : Finset ℕ :=
  if h : n ≤ v ∧ v < n+C.size then
    (C.gates[v-n]'(by change _ < C.size; omega)).inputs.toFinset else ∅

def Edge (n : ℕ) (C : Circuit) (u v : ℕ) := u ∈ pred n C v

def Normal (n : ℕ) (C : Circuit) := ∀ i g, C.gates[i]? = some g →
  ∃ a b : ℕ, g.inputs = [a,b] ∧ a<b ∧ b<n+i

theorem spec {n : ℕ} {C : Circuit} (normal : Normal n C) {v : ℕ}
    (vg : n≤v ∧ v<n+C.size) :
    ∃ (g : Gate) (a b : ℕ), C.gates[v-n]? = some g ∧ g.inputs=[a,b] ∧ a<b ∧ b<v ∧
      pred n C v = {a,b} := by
  have ix : v-n<C.gates.length := by change _ < C.size; omega
  let g := C.gates[v-n]
  have hg : C.gates[v-n]? = some g := List.getElem?_eq_getElem ix
  obtain ⟨a,b,hab,lt,back⟩ := normal _ _ hg
  refine ⟨g,a,b,hg,hab,lt,by omega,?_⟩
  simp [pred,vg,show C.gates[v-n] = g from rfl,hab]

theorem edge_range {n : ℕ} {C : Circuit} {u v : ℕ} (e : Edge n C u v) :
    n ≤ v ∧ v < n+C.size := by
  by_contra! h
  have : ¬(n≤v ∧ v<n+C.size) := by omega
  simp [Edge,pred,this] at e

theorem eval_gate {n : ℕ} {C : Circuit} {v a b : ℕ} {g : Gate}
    (vg : n≤v ∧ v<n+C.size) (hg : C.gates[v-n]? = some g)
    (hab : g.inputs=[a,b]) (ha : a<v) (hb : b<v) (x : Fin n → Bool) :
    WireMono.val C.gates x v = g.op.eval [WireMono.val C.gates x a, WireMono.val C.gates x b] := by
  have ix : v-n<C.gates.length := by change _ < C.size; omega
  have e : C.gates[v-n] = g := Option.some.inj ((List.getElem?_eq_getElem ix).symm.trans hg)
  have hv : n+(v-n)=v := by omega
  have t := WireMono.val_gate C.gates x (v-n) ix
  rw [hv,e,hab] at t
  simpa [ha,hb] using t

/-- A changed output can be traced back to the changed primary input along a path
all of whose wires change. -/
theorem trace {n : ℕ} {C : Circuit} (normal : Normal n C) (j : Fin n)
    {x y : Fin n → Bool} (fix : ∀ u, u ≠ j → x u = y u) (v : ℕ) (hv : v<n+C.size)
    (diff : WireMono.val C.gates x v ≠ WireMono.val C.gates y v) :
    ReflTransGen (fun u w => Edge n C u w ∧ WireMono.val C.gates x w ≠ WireMono.val C.gates y w) j.val v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    by_cases hi : v<n
    · have ev : v=j.val := by
        by_contra h
        apply diff
        rw [WireMono.val_lt _ _ _ hi, WireMono.val_lt _ _ _ hi]
        exact fix ⟨v,hi⟩ (fun eq => h (congrArg Fin.val eq))
      exact ev ▸ ReflTransGen.refl
    · obtain ⟨g,a,b,hg,hab,ab,bv,pr⟩ := spec normal ⟨by omega,hv⟩
      have av : a<v := by omega
      have ev := eval_gate ⟨by omega,hv⟩ hg hab av bv
      have split : WireMono.val C.gates x a ≠ WireMono.val C.gates y a ∨
          WireMono.val C.gates x b ≠ WireMono.val C.gates y b := by
        by_contra! he
        apply diff
        rw [ev x, ev y, he.1, he.2]
      rcases split with d | d
      · exact (ih a av (by omega) d).tail ⟨by simp [Edge,pr],diff⟩
      · exact (ih b bv (by omega) d).tail ⟨by simp [Edge,pr],diff⟩

/-- Fixing one input of a live AND or OR to its absorbing value keeps its
output fixed under every change to the remaining inputs. -/
theorem absorber {n : ℕ} {C : Circuit} (normal : Normal n C) (hm : Monotone2 C)
    (i : Fin n) {v : ℕ} (edge : Edge n C i.val v) :
    ∃ z : Bool, ∀ x y : Fin n → Bool, x i=z → y i=z →
      WireMono.val C.gates x v = WireMono.val C.gates y v := by
  have vg := edge_range edge
  obtain ⟨g,a,b,hg,hab,ab,bv,pr⟩ := spec normal vg
  have ev := eval_gate vg hg hab (by omega) bv
  have mem := List.mem_of_getElem? hg
  have op : g.op = .and ∨ g.op = .or := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using (hm g mem).1
  have side : i.val=a ∨ i.val=b := by simpa [Edge,pr] using edge
  rcases op with andOp | orOp
  · refine ⟨false, ?_⟩
    intro x y hx hy
    rw [ev x, ev y, andOp]
    rcases side with h|h <;> subst_vars <;>
      simp [GateOp.eval,WireMono.val_lt _ _ _ i.isLt,hx,hy]
  · refine ⟨true, ?_⟩
    intro x y hx hy
    rw [ev x, ev y, orOp]
    rcases side with h|h <;> subst_vars <;>
      simp [GateOp.eval,WireMono.val_lt _ _ _ i.isLt,hx,hy]

theorem path_mono {r t : ℕ → ℕ → Prop} (h : ∀ a b, r a b → t a b) {u v : ℕ}
    (p : ReflTransGen r u v) : ReflTransGen t u v := by
  induction p with
  | refl => exact .refl
  | tail _ e ih => exact ih.tail (h _ _ e)

def Live (n : ℕ) (C : Circuit) (v : ℕ) := ReflTransGen (Edge n C) v C.output

noncomputable def gates (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical exact (Finset.Ico n (n+C.size)).filter (Live n C)

noncomputable def users (n : ℕ) (C : Circuit) (u : ℕ) : Finset ℕ := by
  classical exact (gates n C).filter (Edge n C u)

theorem live_step {n : ℕ} {C : Circuit} {u v : ℕ} (e : Edge n C u v)
    (h : Live n C v) : v ∈ users n C u := by
  obtain ⟨a,b⟩ := edge_range e
  classical
  simp [users,gates,a,b,h,e]

theorem input_live {n : ℕ} {C : Circuit} (normal : Normal n C) (ho : C.output<n+C.size)
    (hr : robust n C) (hn : 2≤n) (j : Fin n) : Live n C j.val ∧ j.val ≠ C.output := by
  obtain ⟨k,jk⟩ : ∃ k : Fin n, j≠k := by
    by_cases h : j.val=0
    · exact ⟨⟨1,by omega⟩,fun e => by have h1 : _ = 1 := congrArg Fin.val e; omega⟩
    · exact ⟨⟨0,by omega⟩,fun e => h (congrArg Fin.val e)⟩
  obtain ⟨x,y,f,_,_,d⟩ := hr j k jk false
  have path := trace normal j f C.output ho d
  refine ⟨path_mono (fun _ _ e => e.1) path, ?_⟩
  intro e
  obtain ⟨x',y',f',_,_,d'⟩ := hr k j jk.symm false
  apply d'
  change WireMono.val C.gates x' C.output = WireMono.val C.gates y' C.output
  rw [← e, WireMono.val_lt _ _ _ j.isLt, WireMono.val_lt _ _ _ j.isLt]
  exact f' j jk

/-- A gate with a primary operand cannot be the output of a robust function. -/
theorem input_gate_not_out {n : ℕ} {C : Circuit} (normal : Normal n C) (hm : Monotone2 C)
    (hr : robust n C) (hn : 2≤n) {v : ℕ} (i : Fin n) (e : Edge n C i.val v) : v ≠ C.output := by
  obtain ⟨b,abs⟩ := absorber normal hm i e
  obtain ⟨k,ik⟩ : ∃ k : Fin n, i≠k := by
    by_cases h : i.val=0
    · exact ⟨⟨1,by omega⟩,fun e => by have h1 : _ = 1 := congrArg Fin.val e; omega⟩
    · exact ⟨⟨0,by omega⟩,fun e => h (congrArg Fin.val e)⟩
  obtain ⟨x,y,_,fx,fy,d⟩ := hr k i ik.symm b
  rintro rfl
  exact d (abs x y fx fy)

theorem next_change {n : ℕ} {C : Circuit} {x y : Fin n → Bool} {u v : ℕ}
    (path : ReflTransGen (fun a w => Edge n C a w ∧ WireMono.val C.gates x w ≠ WireMono.val C.gates y w) u C.output)
    (ne : u≠C.output) (unique : ∀ k ∈ users n C u, k=v) :
    WireMono.val C.gates x v ≠ WireMono.val C.gates y v ∧
    ReflTransGen (fun a w => Edge n C a w ∧ WireMono.val C.gates x w ≠ WireMono.val C.gates y w) v C.output := by
  obtain eq | ⟨k,⟨edge,changed⟩,tail⟩ := path.cases_head
  · contradiction
  · obtain rfl := unique k (live_step edge (path_mono (fun _ _ e => e.1) tail))
    exact ⟨changed,tail⟩

noncomputable def next (n : ℕ) (C : Circuit) (u : ℕ) : ℕ :=
  if h : (users n C u).Nonempty then (users n C u).min' h else 0

theorem next_mem {n : ℕ} {C : Circuit} {u : ℕ} (h : (users n C u).Nonempty) :
    next n C u ∈ users n C u := by simp [next,h,Finset.min'_mem]

theorem next_unique {n : ℕ} {C : Circuit} {u : ℕ} (h : (users n C u).card=1) :
    ∀ k ∈ users n C u, k=next n C u := by
  intro k hk
  exact Finset.card_le_one_iff.mp (by omega : (users n C u).card ≤ 1) hk
    (next_mem ⟨k,hk⟩)

theorem next_edge {n : ℕ} {C : Circuit} {u : ℕ} (h : (users n C u).Nonempty) :
    Edge n C u (next n C u) := by
  classical exact (Finset.mem_filter.mp (next_mem h)).2

theorem reachable_user {n : ℕ} {C : Circuit} {u : ℕ} (live : Live n C u)
    (ne : u ≠ C.output) : (users n C u).Nonempty := by
  obtain eq | ⟨v,e,rest⟩ := live.cases_head
  · contradiction
  · exact ⟨v,live_step e rest⟩

/-- Private primary inputs have different first gates. Fixing the other primary
operand would otherwise block the only path carrying a change to the output. -/
theorem private_inj {n : ℕ} {C : Circuit} (normal : Normal n C) (hm : Monotone2 C)
    (ho : C.output<n+C.size) (hr : robust n C) (hn : 2≤n)
    {i j : ℕ} (hi : i<n) (hj : j<n) (pi : (users n C i).card=1)
    (eq : next n C i = next n C j) : i=j := by
  by_contra ij
  let a : Fin n := ⟨i,hi⟩
  let b : Fin n := ⟨j,hj⟩
  have il := input_live normal ho hr hn a
  have jl := input_live normal ho hr hn b
  have ej := next_edge (reachable_user jl.1 jl.2)
  obtain ⟨z,abs⟩ := absorber normal hm b ej
  obtain ⟨x,y,fix,hx,hy,d⟩ := hr a b (fun e => ij (congrArg Fin.val e)) z
  have path := trace normal a fix C.output ho d
  have neq := (next_change path il.2 (next_unique pi)).1
  rw [eq] at neq
  exact neq (abs x y hx hy)

/-- A private input's first gate has no other primary operand, whether that
operand is private or shared. -/
theorem private_only {n : ℕ} {C : Circuit} (normal : Normal n C) (hm : Monotone2 C)
    (ho : C.output<n+C.size) (hr : robust n C) (hn : 2≤n)
    {i j : ℕ} (hi : i<n) (hj : j<n) (pi : (users n C i).card=1)
    (ej : Edge n C j (next n C i)) : i=j := by
  by_contra ij
  let a : Fin n := ⟨i,hi⟩
  let b : Fin n := ⟨j,hj⟩
  have il := input_live normal ho hr hn a
  obtain ⟨z,abs⟩ := absorber normal hm b ej
  obtain ⟨x,y,fix,hx,hy,d⟩ := hr a b (fun e => ij (congrArg Fin.val e)) z
  have path := trace normal a fix C.output ho d
  exact (next_change path il.2 (next_unique pi)).1 (abs x y hx hy)

/-- If both the input and its first gate have just one user, their next gate
has no primary operand at all. -/
theorem no_primary_after {n : ℕ} {C : Circuit} (normal : Normal n C) (hm : Monotone2 C)
    (ho : C.output<n+C.size) (hr : robust n C) (hn : 2≤n)
    {i j : ℕ} (hi : i<n) (hj : j<n) (pi : (users n C i).card=1)
    (pg : (users n C (next n C i)).card=1) (ej : Edge n C j (next n C (next n C i))) : False := by
  classical
  let a : Fin n := ⟨i,hi⟩
  let b : Fin n := ⟨j,hj⟩
  have il := input_live normal ho hr hn a
  have ei := next_edge (reachable_user il.1 il.2)
  have mem := next_mem (Finset.card_pos.mp (by omega : 0 < (users n C (next n C i)).card))
  have es : Edge n C (next n C i) (next n C (next n C i)) := (Finset.mem_filter.mp mem).2
  have gr : next n C i < next n C (next n C i) := by
    obtain ⟨g,u,v,_,_,uv,vt,pr⟩ := spec normal (edge_range es)
    have : next n C i = u ∨ next n C i = v := by simpa [Edge,pr] using es
    omega
  have ij : a ≠ b := by
    intro e
    have e' : i=j := congrArg Fin.val e
    subst j
    have toGate : next n C (next n C i) ∈ users n C i := by
      classical
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp mem).1,ej⟩
    have := next_unique pi _ toGate
    omega
  obtain ⟨z,abs⟩ := absorber normal hm b ej
  obtain ⟨x,y,fix,hx,hy,d⟩ := hr a b ij z
  have path := trace normal a fix C.output ho d
  have p1 := (next_change path il.2 (next_unique pi)).2
  exact (next_change p1 (input_gate_not_out normal hm hr hn a ei) (next_unique pg)).1 (abs x y hx hy)

theorem pred_card {n : ℕ} {C : Circuit} (normal : Normal n C) (g : ℕ) :
    (pred n C g).card ≤ 2 := by
  by_cases h : n≤g ∧ g<n+C.size
  · obtain ⟨_,a,b,_,_,_,_,p⟩ := spec normal h
    rw [p]; exact Finset.card_le_two
  · simp [pred,h]

/-- Double-count the directed edges entering the live gates. -/
theorem users_sum {n : ℕ} {C : Circuit} (normal : Normal n C) (V : Finset ℕ) :
    ∑ u ∈ V, (users n C u).card ≤ 2*(gates n C).card := by
  classical
  let G := gates n C
  calc
    ∑ u ∈ V, (users n C u).card =
        ∑ u ∈ V, ∑ g ∈ G, (if Edge n C u g then 1 else 0 : ℕ) := by
      apply Finset.sum_congr rfl
      intro u _
      simp [users,G,Finset.sum_boole]
    _ = ∑ g ∈ G, ∑ u ∈ V, (if Edge n C u g then 1 else 0 : ℕ) :=
      Finset.sum_comm
    _ ≤ ∑ _g ∈ G, 2 := by
      apply Finset.sum_le_sum
      intro g _
      rw [Finset.sum_boole]
      have sub : V.filter (fun u => Edge n C u g) ⊆ pred n C g :=
        fun u hu => (Finset.mem_filter.mp hu).2
      exact (Finset.card_le_card sub).trans (pred_card normal g)
    _ = 2*(gates n C).card := by simp [G,Nat.mul_comm]

def hasPrimary (n : ℕ) (C : Circuit) (g : ℕ) := ∃ i, i<n ∧ Edge n C i g

/-- A private primary wire receives weight two on its only use. A shared primary
wire receives weight one on each use. Each input supplies at least two units,
and each gate can receive at most two. -/
theorem primary_count {n : ℕ} {C : Circuit} (normal : Normal n C) (hm : Monotone2 C)
    (ho : C.output<n+C.size) (hr : robust n C) (hn : 2≤n) :
    ∀ (R : Finset ℕ), (∀ g, g∈R ↔ g∈gates n C ∧ hasPrimary n C g) → n≤R.card := by
  classical
  intro R hR
  let U := Finset.range n
  let G := gates n C
  let d := fun i => (users n C i).card
  let wt := fun i => if d i=1 then 2 else 1
  let P := fun g => U.filter (fun i => Edge n C i g)
  have pos (i : ℕ) (hi : i∈U) : 0<d i := by
    have it := input_live normal ho hr hn ⟨i,Finset.mem_range.mp hi⟩
    exact Finset.card_pos.mpr (reachable_user it.1 it.2)
  have perInput (i : ℕ) (hi : i∈U) : 2 ≤ ∑ g ∈ G, (if Edge n C i g then wt i else 0) := by
    rw [← Finset.sum_filter]
    change 2 ≤ ∑ _ ∈ users n C i, wt i
    rw [Finset.sum_const, smul_eq_mul]
    change 2 ≤ d i * wt i
    have := pos i hi
    by_cases h : d i=1 <;> simp [wt,h]; omega
  have perGate (g : ℕ) (hg : g∈G) : (∑ i ∈ P g, wt i) ≤ 2 := by
    by_cases h : ∃ i ∈ P g, d i=1
    · obtain ⟨i,hi,di⟩ := h
      obtain ⟨iU,ei⟩ := Finset.mem_filter.mp hi
      have user : g ∈ users n C i := Finset.mem_filter.mpr ⟨hg,ei⟩
      have eg := next_unique di _ user
      have only : P g = {i} := by
        ext j
        simp only [Finset.mem_singleton]
        constructor
        · intro hj
          obtain ⟨jU,ej⟩ := Finset.mem_filter.mp hj
          exact (private_only normal hm ho hr hn (Finset.mem_range.mp iU) (Finset.mem_range.mp jU)
            di (eg ▸ ej)).symm
        · rintro rfl; exact hi
      simp [only,wt,di]
    · have unit : ∀ i ∈ P g, wt i = 1 := by
        intro i hi
        simp [wt,show d i≠1 from fun e => h ⟨i,hi,e⟩]
      rw [Finset.sum_congr rfl unit]
      simp only [Finset.sum_const,smul_eq_mul,Nat.mul_one]
      exact (Finset.card_le_card (show P g ⊆ pred n C g from fun i hi => (Finset.mem_filter.mp hi).2)).trans
        (pred_card normal g)
  have total : 2*n ≤ 2*R.card := calc
    2*n = ∑ _i ∈ U, 2 := by simp [U,Nat.mul_comm]
    _ ≤ ∑ i ∈ U, ∑ g ∈ G, (if Edge n C i g then wt i else 0) := Finset.sum_le_sum perInput
    _ = ∑ g ∈ G, ∑ i ∈ U, (if Edge n C i g then wt i else 0) := Finset.sum_comm
    _ ≤ ∑ g ∈ G, (if g∈R then 2 else 0) := by
      apply Finset.sum_le_sum
      intro g hg
      rw [← Finset.sum_filter]
      by_cases h : g∈R
      · rw [ite_eq_left h]; exact perGate g hg
      · have empty : P g = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i hi
          obtain ⟨hU,ei⟩ := Finset.mem_filter.mp hi
          exact h ((hR g).mpr ⟨hg,i,Finset.mem_range.mp hU,ei⟩)
        change (∑ i ∈ P g, wt i) ≤ _
        simp [empty,h]
    _ = 2*R.card := by
      rw [← Finset.sum_filter]
      have eq : G.filter (fun g => g ∈ R) = R := by
        ext g
        simp only [Finset.mem_filter]
        exact ⟨And.right, fun h => ⟨((hR g).mp h).1,h⟩⟩
      simp [eq,Nat.mul_comm]
  omega

/-- The branching budget and the obstruction to adjacent private inputs give
four input units per three gate units, up to the single output boundary. -/
theorem robust_size {n : ℕ} (C : Circuit) (hn : 2≤n) (hm : Monotone2 C)
    (ho : C.output<n+C.size) (normal : Normal n C) (hr : robust n C) :
    4*n ≤ 3*C.size+1 := by
  classical
  let G := gates n C
  let U := Finset.range n
  let V := U ∪ G
  let d := fun w => (users n C w).card
  let f := next n C
  let branches := V.filter (fun w => 2 ≤ d w)
  let good := U.filter (fun i => d i=1 ∧ d (f i)=1)
  let A := good.image f
  have hiU {u : ℕ} (hu : u∈U) : u<n := Finset.mem_range.mp hu
  have gLower {g : ℕ} (hg : g∈G) : n≤g := (Finset.mem_Ico.mp (Finset.mem_filter.mp hg).1).1
  have ncard : U.card=n := Finset.card_range n
  have sg : G.card ≤ C.size := by
    have := Finset.card_le_card (Finset.filter_subset (Live n C) (Finset.Ico n (n+C.size)))
    simpa [G,gates] using this
  have incard : V.card=n+G.card := by
    have dis : Disjoint U G := Finset.disjoint_left.mpr (fun u hu hg => (Nat.not_le_of_lt (hiU hu)) (gLower hg))
    rw [Finset.card_union_of_disjoint dis,ncard]
  have liveV {w : ℕ} (hw : w∈V) : Live n C w := by
    rcases Finset.mem_union.mp hw with p|g
    · exact (input_live normal ho hr hn ⟨w,hiU p⟩).1
    · exact (Finset.mem_filter.mp g).2
  have degree (w : ℕ) (hw : w∈V) :
      1 + (if 2≤d w then 1 else 0) ≤ d w + (if w=C.output then 1 else 0) := by
    by_cases h : w=C.output
    · simp [h]; split <;> omega
    · have pos := Finset.card_pos.mpr (reachable_user (liveV hw) h)
      change 0<d w at pos
      simp [h]; split <;> omega
  have aggregate := Finset.sum_le_sum degree
  have root : (V.filter (fun w => w=C.output)).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro a b ha hb
    exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.sum_boole,smul_eq_mul,
    Nat.mul_one] at aggregate
  change V.card+branches.card ≤ (∑ w ∈ V, d w) + (V.filter (fun w => w=C.output)).card at aggregate
  have sumd := users_sum normal V
  change (∑ w ∈ V, d w) ≤ 2*G.card at sumd
  have budget : n+branches.card ≤ G.card+1 := by omega
  have ipos {i : ℕ} (hi : i∈U) : (users n C i).Nonempty := by
    have il := input_live normal ho hr hn ⟨i,hiU hi⟩
    exact reachable_user il.1 il.2
  have fG {i : ℕ} (hi : i∈U) : f i ∈ G := (Finset.mem_filter.mp (next_mem (ipos hi))).1
  have fp {i : ℕ} (hi : i∈U) : (users n C (f i)).Nonempty := by
    have e := next_edge (ipos hi)
    exact reachable_user (Finset.mem_filter.mp (fG hi)).2
      (input_gate_not_out normal hm hr hn ⟨i,hiU hi⟩ e)
  have inject {i j : ℕ} (hi : i∈U) (hj : j∈U) (di : d i=1) (eq : f i=f j) : i=j :=
    private_inj normal hm ho hr hn (hiU hi) (hiU hj) di eq
  have gsub : good ⊆ U := Finset.filter_subset _ _
  have cardA : A.card=good.card := Finset.card_image_iff.mpr (by
    intro i hi j hj eq
    exact inject (gsub hi) (gsub hj) (Finset.mem_filter.mp hi).2.1 eq)
  have subA : A ⊆ G := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact fG (gsub hi)
  -- Each remaining input can be assigned a distinct branch, at the input itself
  -- or at its private first gate.
  let charge (i : ℕ) := if d i=1 then f i else i
  have cb (i : ℕ) (hi : i ∈ U \ good) : charge i ∈ branches := by
    obtain ⟨iu,ig⟩ := Finset.mem_sdiff.mp hi
    have ip := Finset.card_pos.mpr (ipos iu)
    have gp := Finset.card_pos.mpr (fp iu)
    change 0<d i at ip
    change 0<d (f i) at gp
    by_cases e : d i=1
    · have e' : d (f i) ≠ 1 := fun h => ig (Finset.mem_filter.mpr ⟨iu,e,h⟩)
      rw [show charge i=f i by simp [charge,e]]
      exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (fG iu),by omega⟩
    · rw [show charge i=i by simp [charge,e]]
      exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ iu,by omega⟩
  have cinj : Set.InjOn charge ↑(U \ good) := by
    intro i hi j hj eq
    have iu := (Finset.mem_sdiff.mp hi).1
    have ju := (Finset.mem_sdiff.mp hj).1
    have ilt := hiU iu
    have jlt := hiU ju
    have ig := gLower (fG iu)
    have jg := gLower (fG ju)
    by_cases ei : d i=1 <;> by_cases ej : d j=1 <;> simp [charge,ei,ej] at eq
    · exact inject iu ju ei eq
    · omega
    · omega
    · exact eq
  have bad : (U \ good).card ≤ branches.card := by
    rw [← Finset.card_image_iff.mpr cinj]
    exact Finset.card_le_card (by
      intro w hw
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
      exact cb i hi)
  let R := G.filter (hasPrimary n C)
  have hR (g : ℕ) : g∈R ↔ g∈gates n C ∧ hasPrimary n C g := Finset.mem_filter
  have many := primary_count normal hm ho hr hn R hR
  -- The distinct first gates of good inputs send their only wire to gates
  -- without primary operands. Each such target has at most two predecessors.
  have cover : A ⊆ (G \ R).biUnion (pred n C) := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
    have iu := gsub hi
    have di := (Finset.mem_filter.mp hi).2
    have mem := next_mem (fp iu)
    have targetG : f (f i) ∈ G := (Finset.mem_filter.mp mem).1
    have targetR : f (f i) ∉ R := by
      intro h
      obtain ⟨j,hj,ej⟩ := ((hR _).mp h).2
      exact no_primary_after normal hm ho hr hn (hiU iu) hj di.1 di.2 ej
    exact Finset.mem_biUnion.mpr ⟨f (f i), Finset.mem_sdiff.mpr ⟨targetG,targetR⟩,
      (Finset.mem_filter.mp mem).2⟩
  have cnt : A.card ≤ 2*(G \ R).card := calc
    A.card ≤ _ := Finset.card_le_card cover
    _ ≤ ∑ v ∈ G \ R, (pred n C v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ G \ R, 2 := Finset.sum_le_sum (fun v _ => pred_card normal v)
    _ = _ := by simp [Nat.mul_comm]
  have diffG := Finset.card_sdiff_add_card_eq_card (show R ⊆ G from Finset.filter_subset _ _)
  have diffU := Finset.card_sdiff_add_card_eq_card gsub
  omega

/-- The bound is unconditional on circuit layout for the normalized circuits in
the desk statement. Only rejection tests with at most two selected lines are used. -/
theorem plane_size {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2≤q) (order : N=q^2+q+1)
    (degree : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (joins : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C) (out : C.output<N+N+C.size) (back : Normal (N+N) C)
    (pos : ∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (right l)=true} ≤ 2 →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false) :
    8*N ≤ 3*C.size+1 := by
  have h := robust_size C (by omega : 2≤N+N) hm out back (plane_robust I C hq order degree joins hm pos neg)
  omega

/-- In particular the exact target holds through order 266. -/
theorem through_266 (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 100<q) (hN : N=q^2+q+1) (hd : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hj : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (hm : Monotone2 C)
    (ho : C.output<N+N+C.size) (back : Normal (N+N) C)
    (pos : ∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (right l)=true} ≤ q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false)
    (cutoff : q≤266) : N*q≤100*C.size := by
  have h := plane_size I C (by omega) hN hd hj hm ho back pos
    (fun x sparse => neg x (sparse.trans (by omega)))
  have nq := Nat.mul_le_mul_left N cutoff
  omega

/-- A convenient unmarked formulation of what remains at one order. -/
def TargetAt (q : ℕ) : Prop := ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
    N=q^2+q+1 → (∀ l, Fintype.card {p : Fin N // I p l}=q+1) →
    (∀ p r, p≠r → ∃! l, I p l ∧ I r l) → Monotone2 C →
    C.output<N+N+C.size → Normal (N+N) C →
    (∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true) →
    (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (right l)=true} ≤ q →
      (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false) →
    N*q≤100*C.size

theorem residual_iff : Desk2008.Posted ↔ ∀ q, 266<q → TargetAt q := by
  constructor
  · intro h q hq N I inst C
    exact (Desk2008.marking_equivalence.mp h) q N I C (by omega)
  · intro high
    apply Desk2008.marking_equivalence.mpr
    intro q N I inst C hq order hd hj hm ho back pos neg
    by_cases h : q≤266
    · exact through_266 q N I C hq order hd hj hm ho back pos neg h
    · exact high q (by omega) N I C order hd hj hm ho back pos neg

end Desk2008.Fanout
#print axioms Desk2008.Fanout.robust_size
#print axioms Desk2008.Fanout.through_266
#print axioms Desk2008.Fanout.residual_iff
