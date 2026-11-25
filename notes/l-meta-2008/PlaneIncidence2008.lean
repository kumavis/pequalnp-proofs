import Mathlib
import PEqualNP.Defs

-- Partial results for desk step L-meta-2008. This file imports only the public definitions
-- and Mathlib. The theorem residual_iff isolates the unsolved range q > 200.
-- Sensitivity.core and its supporting lemmas are adapted from the project's
-- L_meta_2004. Wire monotonicity is from L_meta_2855 / L_meta_1406 (Apache 2.0).
-- There are N points and N lines. The posted target is N*q <= 100*size.
-- Every one of the 2N input coordinates remains essential after any other input
-- is fixed to either bit. To see this, choose a neighbor of the coordinate
-- that distinguishes it from the fixed input, using uniqueness of the line
-- through two points. The two test assignments activate at most two lines.
-- In a two-input first gate, holding its other input at its absorbing value
-- keeps that gate fixed while the circuit output changes. The suffix therefore
-- still needs 2N-1 gates, giving 2N in total. The same argument applies to
-- a prefix of m input-disjoint gates, giving 2N+m-1 for that circuit layout.
-- The all-layout result proves the requested inequality up to order 200.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Desk2008.Sensitivity

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wv (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

lemma wv_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wv (gs ++ [g]) x = step (wv gs x) g := by
  simp [wv, List.foldl_append]

lemma wv_len (gs : List Gate) (x : List Bool) : (wv gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wv]
  | append_singleton gs g ih =>
    rw [wv_snoc]
    simp [step, ih]
    omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false = if i < w.length then w.getD i false
      else if i = w.length then g.op.eval (g.inputs.map fun k => w.getD k false) else false := by
  unfold step
  rcases lt_trichotomy i w.length with hi | hi | hi
  · rw [List.getD_append _ _ _ _ hi]
    simp [hi]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hi]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - w.length = k + 1 := ⟨i - w.length - 1, by omega⟩
    have h1 : ¬ i < w.length := by omega
    have h2 : i ≠ w.length := by omega
    rw [hk]
    simp [h1, h2]

lemma gate_cases (l : List ℕ) (h : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
  match l, h with
  | [], _ => exact Or.inl rfl
  | [a], _ => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | [a, b], _ => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
  | _ :: _ :: _ :: _, h => simp at h

lemma image_merge {ι : Type} [DecidableEq ι] (X : Finset ι) (a b : ι) :
    X.card ≤ (X.image (fun x => if x = a then b else x)).card + 1 := by
  have h1 : X.erase a ⊆ X.image (fun x => if x = a then b else x) := by
    intro x hx
    rw [Finset.mem_erase] at hx
    exact Finset.mem_image.mpr ⟨x, hx.2, by simp [hx.1]⟩
  have h2 := Finset.card_le_card h1
  have h3 := Finset.pred_card_le_card_erase (s := X) (a := a)
  omega

lemma ofFn_getD (n : ℕ) (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> simp

lemma cf_eq (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    PEqualNP.MetaComplexity.circuitFun n C x = (wv C.gates (List.ofFn x)).getD C.output false :=
  rfl

lemma gate_key (n : ℕ) (W : (Fin n → Bool) → ℕ → Bool) (c : Fin n → Fin n)
    (hc : ∀ i, ∃ k, ∀ x y : Fin n → Bool, (∀ j, c j = c k → x j = y j) → W x i = W y i)
    (g : Gate) (hlen : g.inputs.length ≤ 2) :
    ∃ c' : Fin n → Fin n,
      (Finset.univ.image c).card ≤ (Finset.univ.image c').card + 1 ∧
      (∀ v v', c v = c v' → c' v = c' v') ∧
      ∃ k, ∀ x y : Fin n → Bool, (∀ j, c' j = c' k → x j = y j) →
        g.op.eval (g.inputs.map (W x)) = g.op.eval (g.inputs.map (W y)) := by
  rcases gate_cases g.inputs hlen with hi | ⟨a, hi⟩ | ⟨a, b, hi⟩
  · obtain ⟨k, _⟩ := hc 0
    refine ⟨c, Nat.le_add_right _ _, fun _ _ h => h, k, ?_⟩
    intro x y _
    rw [hi]
    rfl
  · obtain ⟨k, hk⟩ := hc a
    refine ⟨c, Nat.le_add_right _ _, fun _ _ h => h, k, ?_⟩
    intro x y h
    rw [hi, List.map_singleton, List.map_singleton, hk x y h]
  · obtain ⟨ka, hka⟩ := hc a
    obtain ⟨kb, hkb⟩ := hc b
    refine ⟨fun v => if c v = c ka then c kb else c v, ?_, ?_, kb, ?_⟩
    · have e : Finset.univ.image (fun v => if c v = c ka then c kb else c v) =
          (Finset.univ.image c).image (fun x => if x = c ka then c kb else x) := by
        rw [Finset.image_image]
        rfl
      rw [e]
      exact image_merge (Finset.univ.image c) (c ka) (c kb)
    · intro v v' h
      simp only [h]
    · intro x y h
      have e : (if c kb = c ka then c kb else c kb) = c kb := by split <;> rfl
      simp only [e] at h
      have h1 : W x a = W y a := by
        apply hka
        intro j hj
        apply h
        simp [hj]
      have h2 : W x b = W y b := by
        apply hkb
        intro j hj
        apply h
        simp [hj]
      rw [hi]
      simp only [List.map_cons, List.map_nil, h1, h2]

lemma core (n : ℕ) (k0 : Fin n) (gs : List Gate) :
    (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∃ c : Fin n → Fin n,
      n ≤ (Finset.univ.image c).card + gs.length ∧
      ∀ i, ∃ k, ∀ x y : Fin n → Bool, (∀ j, c j = c k → x j = y j) →
        (wv gs (List.ofFn x)).getD i false = (wv gs (List.ofFn y)).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨id, by simp, ?_⟩
    intro i
    by_cases hin : i < n
    · refine ⟨⟨i, hin⟩, ?_⟩
      intro x y h
      show (List.ofFn x).getD i false = (List.ofFn y).getD i false
      rw [ofFn_getD, ofFn_getD]
      simp only [hin, dite_true]
      exact h _ rfl
    · refine ⟨k0, ?_⟩
      intro x y _
      show (List.ofFn x).getD i false = (List.ofFn y).getD i false
      rw [ofFn_getD, ofFn_getD]
      simp [hin]
  | append_singleton gs g ih =>
    intro hm
    obtain ⟨c, hc1, hc2⟩ := ih (fun g' hg' => hm g' (by simp [hg']))
    have hg := hm g (by simp)
    obtain ⟨c', k1, k2, k3, hk3⟩ := gate_key n (fun x i => (wv gs (List.ofFn x)).getD i false)
      c hc2 g hg
    refine ⟨c', ?_, ?_⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · intro i
      by_cases hi : i < n + gs.length
      · obtain ⟨k, hk⟩ := hc2 i
        refine ⟨k, ?_⟩
        intro x y h
        rw [wv_snoc, wv_snoc, step_getD, step_getD, wv_len, wv_len]
        simp only [List.length_ofFn, hi, ite_true]
        exact hk x y (fun j hj => h j (k2 j k hj))
      · by_cases hi2 : i = n + gs.length
        · refine ⟨k3, ?_⟩
          intro x y h
          rw [wv_snoc, wv_snoc, step_getD, step_getD, wv_len, wv_len]
          simp only [List.length_ofFn, hi2, ite_true, lt_irrefl, ite_false]
          exact hk3 x y h
        · refine ⟨k0, ?_⟩
          intro x y _
          rw [wv_snoc, wv_snoc, step_getD, step_getD, wv_len, wv_len]
          simp [hi, hi2]

lemma main (n : ℕ) (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (he : ∀ i : Fin n, ∃ (x : Fin n → Bool) (y : Fin n → Bool), (∀ j : Fin n, j ≠ i → x j = y j) ∧
      PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) :
    n ≤ C.size + 1 := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · omega
  obtain ⟨c, hc1, hc2⟩ := core n ⟨0, hpos⟩ C.gates (fun g hg => (hM g hg).2)
  obtain ⟨k, hk⟩ := hc2 C.output
  have hle : (Finset.univ.image c).card ≤ 1 := by
    have hall : ∀ i, c i = c k := by
      intro i
      obtain ⟨x, y, hxy, hne⟩ := he i
      by_contra hci
      apply hne
      rw [cf_eq, cf_eq]
      apply hk
      intro j hj
      apply hxy
      rintro rfl
      exact hci hj
    rw [Finset.card_le_one]
    intro a ha a' ha'
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v', _, rfl⟩ := Finset.mem_image.mp ha'
    rw [hall v, hall v']
  have : C.size = C.gates.length := rfl
  omega

end Desk2008.Sensitivity

namespace Desk2008


-- The exact leased proposition and the version with the marking removed.
def Posted : Prop :=
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → ∀ (x15 : Finset ℕ), (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x16]? = Option.some x17 → x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x16 ∉ x15 → ¬((∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.false)).getD x21 Bool.false ≠ (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.true)).getD x21 Bool.false) ∨ ∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x23)).getD x21 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x23)).getD x21 Bool.false)) → (100 : ℕ) * x15.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size

def Unmarked : Prop :=
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size

theorem marking_equivalence : Posted ↔ Unmarked := by
  constructor
  · intro posted q n incidence inst circuit hq hn hline hpairs hmono hout hwire hpos hneg
    by_contra small
    have cost : 100 * circuit.size < n * q := Nat.lt_of_not_ge small
    let marks := Finset.range circuit.size
    apply small
    apply posted q n incidence circuit hq hn hline hpairs hmono hout hwire hpos hneg marks
    · intro i g lookup _ unmarked
      have hi := (List.getElem?_eq_some_iff.mp lookup).choose
      exact (unmarked (Finset.mem_range.mpr hi)).elim
    · simpa [marks] using cost
  · intro target q n incidence inst circuit hq hn hline hpairs hmono hout hwire hpos hneg marks hmarks hcost
    exact target q n incidence circuit hq hn hline hpairs hmono hout hwire hpos hneg



end Desk2008

-- Wire monotonicity from L_meta_2855 and its source L_meta_1406 (Apache 2.0).
open PEqualNP.CircuitLowerBounds
namespace Desk2008.WireMono
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl, val_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, val_ge gs x j (by omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget, val_snoc, if_neg (by omega), ih k hk2]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [if_pos hj, if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, if_neg hj]

lemma mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hle : ∀ v, x v = true → x' v = true) :
    ∀ i, val gs x i = true → val gs x' i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i < n
    · rw [val_lt gs x i h1] at hi
      rw [val_lt gs x' i h1]
      exact hle _ hi
    · by_cases h2 : n + gs.length ≤ i
      · rw [val_ge gs x i h2] at hi
        exact absurd hi (by simp)
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gs.length := by omega
        rw [val_gate gs x k hk] at hi
        rw [val_gate gs x' k hk]
        obtain ⟨hop, hlen⟩ := hg _ (List.getElem_mem hk)
        generalize gs[k] = g at hi hop hlen ⊢
        obtain ⟨op, ins⟩ := g
        simp only at hi hop hlen ⊢
        have rd : ∀ a : ℕ, (if a < n + k then val gs x a else false) = true →
            (if a < n + k then val gs x' a else false) = true := by
          intro a ha
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at ha ⊢
            exact ih a hlt ha
          · rw [if_neg hlt] at ha
            exact absurd ha (by simp)
        match ins, hlen with
        | [], _ =>
          rcases hop with rfl | rfl
          · simp [GateOp.eval]
          · simp [GateOp.eval] at hi
        | [a], _ =>
          rcases hop with rfl | rfl
          · have h := rd a (by simpa [GateOp.eval] using hi)
            simpa [GateOp.eval] using h
          · have h := rd a (by simpa [GateOp.eval] using hi)
            simpa [GateOp.eval] using h
        | [a, b], _ =>
          rcases hop with rfl | rfl
          · have h : (if a < n + k then val gs x a else false) = true ∧
                (if b < n + k then val gs x b else false) = true := by
              simpa [GateOp.eval] using hi
            have h1 := rd a h.1
            have h2 := rd b h.2
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              Bool.and_true, id_eq, Bool.and_eq_true]
            exact ⟨h1, h2⟩
          · have h : (if a < n + k then val gs x a else false) = true ∨
                (if b < n + k then val gs x b else false) = true := by
              simpa [GateOp.eval] using hi
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              Bool.or_false, id_eq, Bool.or_eq_true]
            rcases h with h | h
            · exact Or.inl (rd a h)
            · exact Or.inr (rd b h)
        | _ :: _ :: _ :: _, h => simp at h


end Desk2008.WireMono

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Desk2008
open Sensitivity

-- Every original input remains essential after fixing any other input to either bit.
def robust (n : Nat) (C : Circuit) : Prop :=
  ∀ j k : Fin n, j ≠ k → ∀ v : Bool, ∃ x y : Fin n → Bool,
    (∀ u, u ≠ j → x u = y u) ∧ x k = v ∧ y k = v ∧ circuitFun n C x ≠ circuitFun n C y

theorem extra_gate (n : Nat) (C : Circuit) (hn : 2 ≤ n) (hm : Monotone2 C)
    (back : ∀ i g, C.gates[i]? = some g → ∃ a b : Nat, g.inputs = [a,b] ∧ a < b ∧ b < n+i)
    (hr : robust n C) : n ≤ C.size := by
  have other (j : Fin n) : ∃ k, j ≠ k := by
    let k : Fin n := if j.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
    refine ⟨k, fun h => ?_⟩
    have hv := congrArg Fin.val h
    by_cases hz : j.val = 0 <;> simp [k, hz] at hv
  have essential (j : Fin n) : ∃ x y : Fin n → Bool,
      (∀ u, u ≠ j → x u = y u) ∧ circuitFun n C x ≠ circuitFun n C y := by
    obtain ⟨k,ne⟩ := other j
    obtain ⟨x,y,h,_,_,diff⟩ := hr j k ne false
    exact ⟨x,y,h,diff⟩
  cases C with
  | mk gs out =>
    cases gs with
    | nil =>
      have bound := Sensitivity.main n ⟨[],out⟩ hm essential
      change n ≤ 0+1 at bound
      omega
    | cons g gs =>
      obtain ⟨a,b,hinputs,hab,hb⟩ := back 0 g (by simp)
      let A : Fin n := ⟨a, by omega⟩
      let B : Fin n := ⟨b, by omega⟩
      have ab : A ≠ B := fun h => (Nat.ne_of_lt hab) (congrArg Fin.val h)
      let f (x : Fin n → Bool) := g.op.eval [x A, x B]
      let C' : Circuit := ⟨g::gs,out⟩
      have freeze (j : Fin n) : ∃ x y : Fin n → Bool,
          (∀ u, u ≠ j → x u = y u) ∧ f x = f y ∧ circuitFun n C' x ≠ circuitFun n C' y := by
        have op : g.op = .and ∨ g.op = .or := (hm g (by simp)).1
        let v := g.op.eval [false,true]
        by_cases ja : j = A
        · subst j
          obtain ⟨x,y,h,hx,hy,ne⟩ := hr A B ab v
          refine ⟨x,y,h,?_,ne⟩
          rcases op with h | h <;> simp [f,hx,hy,v,h,GateOp.eval]
        by_cases jb : j = B
        · subst j
          obtain ⟨x,y,h,hx,hy,ne⟩ := hr B A ab.symm v
          refine ⟨x,y,h,?_,ne⟩
          rcases op with h | h <;> simp [f,hx,hy,v,h,GateOp.eval]
        obtain ⟨x,y,h,ne⟩ := essential j
        exact ⟨x,y,h,by simp [f, h A (Ne.symm ja), h B (Ne.symm jb)],ne⟩
      let extend (x : Fin n → Bool) : Fin (n+1) → Bool := Fin.snoc x (f x)
      have evaluate (x : Fin n → Bool) : circuitFun n C' x =
          (wv gs (List.ofFn (extend x))).getD out false := by
        have hlist : List.ofFn (extend x) = List.ofFn x ++ [f x] := by
          rw [List.ofFn_succ']
          simp [extend, Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
        rw [hlist]
        change (wv gs (step (List.ofFn x) g)).getD out false = _
        congr 2
        simp [step, hinputs, f, A, B, ofFn_getD, show a < n by omega, show b < n by omega]
      obtain ⟨c, hcount, wires⟩ := Sensitivity.core (n+1) (Fin.last n) gs
        (fun g' mem => (hm g' (by simp [mem])).2)
      obtain ⟨k,hk⟩ := wires out
      have same (j : Fin n) : c j.castSucc = c k := by
        by_contra different
        obtain ⟨x,y,agree,unchanged,ne⟩ := freeze j
        apply ne
        rw [evaluate, evaluate]
        apply hk
        intro u
        refine Fin.lastCases ?_ (fun i => ?_) u
        · intro _
          simpa [extend, Fin.snoc_last] using unchanged
        · intro h
          have ne : i ≠ j := fun e => different (e ▸ h)
          simpa [extend, Fin.snoc_castSucc] using agree i ne
      have hsub : Finset.univ.image c ⊆ {c k, c (Fin.last n)} := by
        intro u hu
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simp [same j]
      have bound := Finset.card_le_card hsub
      have two := Finset.card_insert_le (c k) ({c (Fin.last n)} : Finset (Fin (n+1)))
      simp only [Finset.card_singleton] at two
      change n ≤ gs.length + 1
      omega
end Desk2008


namespace Desk2008
abbrev left {N : Nat} (i : Fin N) := Fin.castAdd N i
abbrev right {N : Nat} (i : Fin N) := Fin.natAdd N i
theorem lr {N : Nat} (p l : Fin N) : left p ≠ right l := by
  intro e
  have := congrArg Fin.val e
  simp [left,right] at this
  omega
def adj {N : Nat} (I : Fin N → Fin N → Prop) (i j : Fin (N+N)) : Prop :=
  ∃ p l, I p l ∧ ((i = left p ∧ j = right l) ∨ (i = right l ∧ j = left p))
theorem adjLR {N : Nat} (I : Fin N → Fin N → Prop) (p l : Fin N) : adj I (left p) (right l) ↔ I p l := by
  constructor
  · rintro ⟨a,b,h,⟨ea,eb⟩ | ⟨e,_⟩⟩
    · exact (show p = a from Fin.castAdd_injective _ _ ea) ▸
        (show l = b from Fin.natAdd_injective _ _ eb) ▸ h
    · exact (lr _ _ e).elim
  · intro h
    exact ⟨p,l,h,Or.inl ⟨rfl,rfl⟩⟩
theorem adjRL {N : Nat} (I : Fin N → Fin N → Prop) (p l : Fin N) : adj I (right l) (left p) ↔ I p l := by
  constructor
  · rintro ⟨a,b,h,⟨e,_⟩ | ⟨eb,ea⟩⟩
    · exact (lr _ _ e.symm).elim
    · exact (show p = a from Fin.castAdd_injective _ _ ea) ▸
        (show l = b from Fin.natAdd_injective _ _ eb) ▸ h
  · intro h
    exact ⟨p,l,h,Or.inr ⟨rfl,rfl⟩⟩
theorem adjLL {N : Nat} (I : Fin N → Fin N → Prop) (p r : Fin N) : ¬ adj I (left p) (left r) := by
  rintro ⟨a,b,_,⟨_,e⟩ | ⟨e,_⟩⟩ <;> exact lr _ _ e
theorem adjRR {N : Nat} (I : Fin N → Fin N → Prop) (l s : Fin N) : ¬ adj I (right l) (right s) := by
  rintro ⟨a,b,_,⟨e,_⟩ | ⟨_,e⟩⟩ <;> exact lr _ _ e.symm
theorem loopless {N : Nat} (I : Fin N → Fin N → Prop) (i : Fin (N+N)) : ¬ adj I i i := by
  exact Fin.addCases (fun p => adjLL I p p) (fun l => adjRR I l l) i
theorem adjSymm {N : Nat} (I : Fin N → Fin N → Prop) {i j : Fin (N+N)} : adj I i j → adj I j i := by
  rintro ⟨p,l,h,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
  · exact ⟨p,l,h,Or.inr ⟨rfl,rfl⟩⟩
  · exact ⟨p,l,h,Or.inl ⟨rfl,rfl⟩⟩

theorem separate (q N : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (order : N = q^2+q+1) (hq : 2 ≤ q)
    (deg : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) :
    ∀ j k : Fin (N+N), j ≠ k → ∃ t, adj I j t ∧ t ≠ k ∧ ¬ adj I k t := by
  classical
  let S (l : Fin N) := Finset.univ.filter (fun p => I p l)
  have card (l : Fin N) : (S l).card = q+1 := by simpa [S,Fintype.card_subtype] using deg l
  have pair (l : Fin N) : ∃ a b, I a l ∧ I b l ∧ a ≠ b := by
    have big : 1 < (S l).card := by rw [card]; omega
    simpa [S] using Finset.one_lt_card_iff.mp big
  have pickLine (p : Fin N) (l : Fin N) : ∃ m, I p m ∧ m ≠ l := by
    have ex : ∃ r, r ≠ p ∧ ¬ I r l := by
      by_contra! all
      have sub : (Finset.univ : Finset (Fin N)) ⊆ insert p (S l) := by
        intro i _
        by_cases h : i = p
        · simp [h]
        · simpa [S, h] using all i h
      have c1 := Finset.card_le_card sub
      have c2 := Finset.card_insert_le p (S l)
      simp [card] at c1 c2
      have sq : 2 ≤ q^2 := by nlinarith
      omega
    obtain ⟨r,rp,miss⟩ := ex
    obtain ⟨m,⟨pm,rm⟩,_⟩ := unique p r rp.symm
    exact ⟨m,pm,fun e => miss (e ▸ rm)⟩
  have pickPoint (l : Fin N) (p : Fin N) : ∃ r, I r l ∧ r ≠ p := by
    obtain ⟨a,b,ha,hb,ne⟩ := pair l
    by_cases eq : a = p
    · exact ⟨b,hb,eq ▸ ne.symm⟩
    · exact ⟨a,ha,eq⟩
  intro j
  induction j using Fin.addCases with
  | left p =>
    intro k
    induction k using Fin.addCases with
    | left r =>
      intro ne
      have pr : p ≠ r := fun e => ne (e ▸ rfl)
      obtain ⟨l,⟨pl,rl⟩,only⟩ := unique p r pr
      obtain ⟨m,pm,ml⟩ := pickLine p l
      exact ⟨right m,(adjLR _ _ _).mpr pm,(lr _ _).symm,fun z => ml (only m ⟨pm,(adjLR _ _ _).mp z⟩)⟩
    | right l =>
      intro _
      obtain ⟨m,pm,ml⟩ := pickLine p l
      exact ⟨right m,(adjLR _ _ _).mpr pm,fun e => ml (Fin.natAdd_injective _ _ e),adjRR _ _ _⟩
  | right l =>
    intro k
    induction k using Fin.addCases with
    | left p =>
      intro _
      obtain ⟨r,rl,rp⟩ := pickPoint l p
      exact ⟨left r,(adjRL _ _ _).mpr rl,fun e => rp (Fin.castAdd_injective _ _ e),adjLL _ _ _⟩
    | right m =>
      intro ne
      have lm : l ≠ m := fun e => ne (e ▸ rfl)
      have ex : ∃ p, I p l ∧ ¬ I p m := by
        by_contra! all
        obtain ⟨a,b,al,bl,ab⟩ := pair l
        exact lm ((unique a b ab).unique ⟨al,bl⟩ ⟨all a al,all b bl⟩)
      obtain ⟨p,pl,pm⟩ := ex
      exact ⟨left p,(adjRL _ _ _).mpr pl,lr _ _,fun z => pm ((adjRL _ _ _).mp z)⟩
end Desk2008

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Desk2008

theorem plane_robust {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (order : N=q^2+q+1)
    (degree : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (joins : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C)
    (yes : ∀ p l, I p l → circuitFun (N+N) C
      (fun i => decide (i=left p ∨ i=right l)) = true)
    (no : ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (right l) = true} ≤ 2 →
      (¬∃ p l, I p l ∧ x (left p) = true ∧ x (right l) = true) →
      circuitFun (N+N) C x = false) : robust (N+N) C := by
  classical
  intro j k jk v
  obtain ⟨t,jt,tk,kt⟩ := separate q N I order hq degree joins j k jk
  let x (i : Fin (N+N)) := decide (i=t ∨ i=k ∧ v=true)
  let y (i : Fin (N+N)) := decide (i=j ∨ i=t ∨ i=k ∧ v=true)
  have sparse : Fintype.card {l : Fin N // x (right l) = true} ≤ 2 := by
    rw [Fintype.card_subtype]
    let L := Finset.univ.filter fun l : Fin N => x (right l) = true
    change L.card ≤ 2
    have sub : L.image right ⊆ ({t,k} : Finset (Fin (N+N))) := by
      intro i mem
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp mem
      have bit := (Finset.mem_filter.mp hl).2
      change decide (_ ∨ _) = true at bit
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases of_decide_eq_true bit with h | ⟨h,_⟩
      · exact Or.inl h
      · exact Or.inr h
    have le := Finset.card_le_card sub
    rw [Finset.card_image_of_injective L (Fin.natAdd_injective _ _)] at le
    have two := Finset.card_insert_le t ({k} : Finset (Fin (N+N)))
    simp only [Finset.card_singleton] at two
    omega
  have off : circuitFun (N+N) C x = false := by
    apply no x sparse
    rintro ⟨p,l,incident,pon,lon⟩
    have a := (adjLR I p l).mpr incident
    rcases of_decide_eq_true pon with hp | ⟨hp,_⟩ <;>
      rcases of_decide_eq_true lon with hl | ⟨hl,_⟩ <;> rw [hp,hl] at a
    · exact loopless I t a
    · exact kt (adjSymm I a)
    · exact kt a
    · exact loopless I k a
  have onBit (i : Fin (N+N)) (hi : i=j ∨ i=t) : y i = true := by
    apply decide_eq_true
    tauto
  have on : circuitFun (N+N) C y = true := by
    obtain ⟨p,l,incident,pair⟩ := jt
    let atom (i : Fin (N+N)) := decide (i=left p ∨ i=right l)
    have le (i : Fin (N+N)) (hi : atom i = true) : y i = true := by
      apply onBit
      rcases of_decide_eq_true hi with e|e <;> rcases pair with ⟨a,b⟩|⟨a,b⟩ <;> grind
    exact WireMono.mono C.gates hm atom y le C.output (yes p l incident)
  refine ⟨x,y,?_,?_,?_,?_⟩
  · intro u uj
    simp [x,y,uj]
  · cases v <;> simp [x,tk.symm]
  · cases v <;> simp [y,tk.symm,jk.symm]
  · rw [off,on]
    decide

-- Applies also to smaller planes, under the same two-line rejection tests.
theorem normalized_plane_size {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (order : N=q^2+q+1)
    (degree : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (joins : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (hm : Monotone2 C)
    (back : ∀ i g, C.gates[i]? = some g → ∃ a b : Nat, g.inputs = [a,b] ∧ a<b ∧ b<N+N+i)
    (pos : ∀ p l, I p l → circuitFun (N+N) C (fun i => decide (i=left p ∨ i=right l))=true)
    (neg : ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (right l)=true} ≤ 2 →
       (¬∃ p l, I p l ∧ x (left p)=true ∧ x (right l)=true) → circuitFun (N+N) C x=false) :
    N+N ≤ C.size := by
  apply extra_gate _ C (by nlinarith) hm back
  exact plane_robust I C hq order degree joins hm pos neg

theorem size_at_least_twice_vertex_count_per_side :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → x2 + x2 ≤ x5.size := by
  intro q N I inst C hq order degree joins hm _ back pos neg
  exact normalized_plane_size I C (by omega) order degree joins hm back pos
    (fun x sparse => neg x (sparse.trans (by omega)))

theorem through_200 :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → x1 ≤ 200 → x2 * x1 ≤ 100 * x5.size := by
  intro q N I inst C hq order degree joins hm out back pos neg cutoff
  have sz := size_at_least_twice_vertex_count_per_side q N I C hq order degree joins hm out back pos neg
  calc
    N*q ≤ N*200 := Nat.mul_le_mul_left N cutoff
    _ = 100*(N+N) := by ring
    _ ≤ 100*C.size := Nat.mul_le_mul_left _ sz

end Desk2008

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Desk2008
open Sensitivity

-- If each coordinate can independently change the output while leaving the entire
-- prefix of intermediate values fixed, the suffix still needs at least n-1 gates.
theorem suffix_count (n : Nat) (front tail : List Gate) (out : Nat) (hn : 0 < n)
    (fanin : ∀ g ∈ tail, g.inputs.length ≤ 2)
    (witness : ∀ j : Fin n, ∃ x y : Fin n → Bool,
      (∀ i, i ≠ j → x i = y i) ∧
      (∀ k : Fin front.length, WireMono.val front x (n+k.val) = WireMono.val front y (n+k.val)) ∧
      circuitFun n ⟨front ++ tail, out⟩ x ≠ circuitFun n ⟨front ++ tail, out⟩ y) :
    n ≤ tail.length + 1 := by
  let p := front.length
  let extend (x : Fin n → Bool) (i : Fin (n+p)) := WireMono.val front x i.val
  have extList (x : Fin n → Bool) : List.ofFn (extend x) = wv front (List.ofFn x) := by
    have len : (wv front (List.ofFn x)).length = n+p := by simp [wv_len,p]
    apply List.ext_getElem
    · simp [len]
    · intro i h1 h2
      simp only [List.getElem_ofFn]
      change (wv front (List.ofFn x)).getD i false = _
      simp [List.getD_eq_getElem?_getD, h2]
  have evaluate (x : Fin n → Bool) : circuitFun n ⟨front++tail,out⟩ x =
      (wv tail (List.ofFn (extend x))).getD out false := by
    rw [extList,cf_eq]
    simp [wv,List.foldl_append]
  obtain ⟨c,count,wire⟩ := core (n+p) ⟨0,by omega⟩ tail fanin
  obtain ⟨a,depend⟩ := wire out
  have allMain (j : Fin n) : c (Fin.castAdd p j) = c a := by
    by_contra outside
    obtain ⟨x,y,hxy,frozen,ne⟩ := witness j
    apply ne
    rw [evaluate,evaluate]
    apply depend
    intro i
    induction i using Fin.addCases with
    | left k =>
      intro hk
      have hkj : k ≠ j := fun e => outside (e ▸ hk)
      change WireMono.val front x k.val = WireMono.val front y k.val
      rw [WireMono.val_lt _ _ _ k.isLt, WireMono.val_lt _ _ _ k.isLt]
      simpa using hxy k hkj
    | right k =>
      intro _
      exact frozen k
  let extra := (Finset.univ : Finset (Fin p)).image (fun k => c (Fin.natAdd n k))
  have sub : Finset.univ.image c ⊆ insert (c a) extra := by
    intro u h
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
    induction i using Fin.addCases with
    | left j => exact Finset.mem_insert.mpr (Or.inl (allMain j))
    | right k => exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩))
  have c1 := Finset.card_le_card sub
  have c2 := Finset.card_insert_le (c a) extra
  have c3 : extra.card ≤ p := by
    exact (Finset.card_image_le).trans_eq (by simp)
  omega
end Desk2008

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Desk2008

def firstLayer {n m : Nat} (A B : Fin m → Fin n) (useOr : Fin m → Bool) : List Gate :=
  List.ofFn fun k => ⟨if useOr k then .or else .and, [(A k).val,(B k).val]⟩

def value2 (o a b : Bool) := if o then a || b else a && b

theorem firstLayer_value {n m : Nat} (A B : Fin m → Fin n) (useOr : Fin m → Bool)
    (x : Fin n → Bool) (k : Fin m) :
    WireMono.val (firstLayer A B useOr) x (n+k.val) = value2 (useOr k) (x (A k)) (x (B k)) := by
  have hk : k.val < (firstLayer A B useOr).length := by simpa [firstLayer] using k.isLt
  rw [WireMono.val_gate _ _ _ hk]
  have ha := (A k).isLt
  have hb := (B k).isLt
  simp only [firstLayer,List.getElem_ofFn,List.map_cons,List.map_nil]
  simp only [show (A k).val < n+k.val by omega, show (B k).val < n+k.val by omega, ite_true]
  rw [WireMono.val_lt _ _ _ ha, WireMono.val_lt _ _ _ hb]
  cases h : useOr k <;> simp [h,value2,GateOp.eval]

theorem disjoint_layer_bound {n m : Nat} (A B : Fin m → Fin n) (useOr : Fin m → Bool)
    (tail : List Gate) (out : Nat) (hn : 2 ≤ n)
    (distinct : ∀ k, A k ≠ B k)
    (disjoint : ∀ j k l, (j=A k ∨ j=B k) → (j=A l ∨ j=B l) → k=l)
    (fanin : ∀ g ∈ tail, g.inputs.length ≤ 2)
    (rob : robust n ⟨firstLayer A B useOr ++ tail,out⟩) :
    n+m ≤ (firstLayer A B useOr ++ tail).length + 1 := by
  let C : Circuit := ⟨firstLayer A B useOr ++ tail,out⟩
  -- Only one first-layer gate needs to keep its output fixed when this coordinate changes.
  have single (j : Fin n) (k : Fin m) (touch : j=A k ∨ j=B k) : ∃ x y : Fin n → Bool,
      (∀ i, i ≠ j → x i = y i) ∧
      value2 (useOr k) (x (A k)) (x (B k)) = value2 (useOr k) (y (A k)) (y (B k)) ∧
      circuitFun n C x ≠ circuitFun n C y := by
    rcases touch with rfl | rfl
    · obtain ⟨x,y,h,hx,hy,ne⟩ := rob (A k) (B k) (distinct k) (useOr k)
      refine ⟨x,y,h,?_,ne⟩
      cases op : useOr k <;> simp [value2,hx,hy,op]
    · obtain ⟨x,y,h,hx,hy,ne⟩ := rob (B k) (A k) (distinct k).symm (useOr k)
      refine ⟨x,y,h,?_,ne⟩
      cases op : useOr k <;> simp [value2,hx,hy,op]
  have hcount : n ≤ tail.length + 1 := by
    apply suffix_count _ _ _ _ (by omega) fanin
    intro j
    by_cases active : ∃ k, j=A k ∨ j=B k
    · obtain ⟨k,touch⟩ := active
      obtain ⟨x,y,agree,hold,ne⟩ := single j k touch
      refine ⟨x,y,agree,?_,ne⟩
      intro i
      let l : Fin m := ⟨i.val,by simpa [firstLayer] using i.isLt⟩
      change WireMono.val _ x (n+l.val) = WireMono.val _ y (n+l.val)
      rw [firstLayer_value,firstLayer_value]
      by_cases eq : k=l
      · exact eq ▸ hold
      have unused : ¬(j=A l ∨ j=B l) := fun z => eq (disjoint _ _ _ touch z)
      rw [agree (A l) (fun eq => unused (Or.inl eq.symm)),
          agree (B l) (fun eq => unused (Or.inr eq.symm))]
    · let v : Fin n := if j.val = 0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
      have jv : j ≠ v := by
        intro e
        have hv := congrArg Fin.val e
        by_cases z : j.val=0 <;> simp [v,z] at hv
      obtain ⟨x,y,agree,_,_,ne⟩ := rob j v jv false
      refine ⟨x,y,agree,?_,ne⟩
      intro i
      let l : Fin m := ⟨i.val,by simpa [firstLayer] using i.isLt⟩
      change WireMono.val _ x (n+l.val) = WireMono.val _ y (n+l.val)
      rw [firstLayer_value,firstLayer_value,agree (A l) (fun e => active ⟨l,Or.inl e.symm⟩),
          agree (B l) (fun e => active ⟨l,Or.inr e.symm⟩)]
  simp [firstLayer]
  omega
end Desk2008

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Desk2008

-- Every disjoint first-layer gate costs an extra gate beyond the fan-in count.
theorem plane_with_disjoint_first_layer {q N m : Nat} (I : Fin N → Fin N → Prop)
    [DecidableRel I] (A B : Fin m → Fin (N+N)) (useOr : Fin m → Bool)
    (tail : List Gate) (out : Nat) (hq : 2 ≤ q) (order : N=q^2+q+1)
    (degree : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (joins : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (diff : ∀ k, A k ≠ B k)
    (apart : ∀ j k l, (j=A k ∨ j=B k) → (j=A l ∨ j=B l) → k=l) :
    let C : Circuit := ⟨firstLayer A B useOr ++ tail,out⟩
    Monotone2 C →
    (∀ p l, I p l → circuitFun (N+N) C
        (fun i => decide (i=left p ∨ i=right l)) = true) →
    (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (right l) = true} ≤ 2 →
        (¬∃ p l, I p l ∧ x (left p) = true ∧ x (right l) = true) →
        circuitFun (N+N) C x = false) → (N+N)+m ≤ C.size+1 := by
  intro C hm pos neg
  apply disjoint_layer_bound A B useOr tail out (by nlinarith) diff apart
  · intro g mem
    exact (hm g (by simp [C,mem])).2
  · exact plane_robust I C hq order degree joins hm pos neg
end Desk2008

namespace Desk2008

theorem layer_width {n m : Nat} (A B : Fin m → Fin n) (diff : ∀ k, A k ≠ B k)
    (apart : ∀ j k l, (j=A k ∨ j=B k) → (j=A l ∨ j=B l) → k=l) : m+m ≤ n := by
  have inj : Function.Injective (Sum.elim A B) := by
    intro s t e
    cases s with
    | inl k =>
      cases t with
      | inl l =>
        have eq := apart (A k) k l (Or.inl rfl) (Or.inl e)
        exact congrArg Sum.inl eq
      | inr l =>
        have eq := apart (A k) k l (Or.inl rfl) (Or.inr e)
        subst l
        exact (diff k e).elim
    | inr k =>
      cases t with
      | inl l =>
        have eq := apart (B k) k l (Or.inr rfl) (Or.inl e)
        subst l
        exact (diff k e.symm).elim
      | inr l =>
        have eq := apart (B k) k l (Or.inr rfl) (Or.inr e)
        exact congrArg Sum.inr eq
  simpa using Fintype.card_le_of_injective _ inj

-- Even the maximum such layer gives fewer than N*q/100 gates at q >= 300.
theorem limit_of_layer_estimate (N q m : Nat) (hN : 0 < N) (hq : 300 ≤ q)
    (hm : m+m ≤ N+N) : 100 * ((N+N)+m-1) < N*q := by
  have bound := Nat.mul_le_mul_left N hq
  omega
end Desk2008

namespace Desk2008

-- Orders 201 and larger give exactly the remaining obligation.
def HigherOrders : Prop :=
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size

theorem residual_iff : Posted ↔ HigherOrders := by
  constructor
  · intro full q N I inst C hq
    exact (marking_equivalence.mp full) q N I C (by omega)
  · intro large
    apply marking_equivalence.mpr
    intro q N I inst C hq order degree joins hm out back pos neg
    rcases le_or_gt q 200 with low | high
    · exact through_200 q N I C hq order degree joins hm out back pos neg low
    · exact large q N I C high order degree joins hm out back pos neg

end Desk2008

#print axioms Desk2008.size_at_least_twice_vertex_count_per_side
#print axioms Desk2008.through_200
#print axioms Desk2008.residual_iff
#print axioms Desk2008.plane_with_disjoint_first_layer
