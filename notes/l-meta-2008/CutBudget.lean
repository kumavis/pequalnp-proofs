import CutQuery

namespace GateElim.Cuts
open Reverse Finset Classical
variable {J V : Type*} [Fintype J] [DecidableEq J] {n k : ℕ}

def prepCost (k h m : ℕ) := 8*k*h+(2*h^2+h)*m
def rowCost (k h m : ℕ) := (8*h+5)*k+(2*h^2+3*h+1)*m

/-- Process exceptional AND gates in forward order. Two reverse queries give
their operands at every row, after which a pointwise AND pays for the cut. -/
theorem prepare (G : Net n k) (x : Fin n → Fn V) (sel : J → Fin n)
    (M : ℕ→Bool) (S : Set (Fn V)) (has : ∀ i, G.run comb x i∈S) (cs : ∀ b, const b∈S) :
    ∃ gs : List (Node V), gs.length≤prepCost k (tally M k) (Fintype.card J) ∧
      Built S gs ∧ Paid M x (inputs x sel) (pool S gs) G := by
  induction G with
  | empty => exact ⟨[],by simp [prepCost,tally],True.intro,True.intro⟩
  | @add k pre op a b ih =>
    let z := inputs x sel
    have av (i : Fin (n+k)) : pre.run comb x i∈S := by simpa [Net.run] using has i.castSucc
    obtain ⟨gs,gl,gb,gp⟩ := ih av
    let T := pool S gs
    have lift : S⊆T := pool_grows _ _
    by_cases bad : M k=true
    · obtain ⟨hs,hl,hb,ha⟩ := query pre a x sel M T (fun i => lift (av i)) (fun b => lift (cs b)) gp
      let U := pool T hs
      have liftU : T⊆U := pool_grows _ _
      obtain ⟨ks,kl,kb,ka⟩ := query pre b x sel M U (fun i => liftU (lift (av i)))
        (fun b => liftU (lift (cs b))) (paid_lift _ gp liftU)
      let W := pool U ks
      have liftW : U⊆W := pool_grows _ _
      obtain ⟨ps,pl,pb,res⟩ := batch op (fun j => pre.row M x (z j) a) (fun j => pre.row M x (z j) b)
        W (fun j => ⟨liftW (ha j),ka j⟩)
      refine ⟨gs++hs++ks++ps,?_,?_,?_⟩
      · change _ ≤ prepCost (k+1) (tally M k+(if M k=true then 1 else 0)) _
        simp only [List.length_append,bad,↓reduceIte,pl]
        change gs.length≤prepCost k (tally M k) _ at gl
        change hs.length≤4*k+(2*tally M k+1)*Fintype.card J at hl
        change ks.length≤4*k+(2*tally M k+1)*Fintype.card J at kl
        unfold prepCost at gl ⊢; nlinarith
      · apply build_append (build_append (build_append gb hb) (by rwa [pool_append]))
        simpa only [pool_append,T,U,W] using pb
      · simp only [pool_append]
        refine ⟨paid_lift pre gp (Set.Subset.trans liftU (Set.Subset.trans liftW (pool_grows _ _))),
          fun _ j => res j⟩
    · refine ⟨gs,?_,gb,gp,fun h => (bad h).elim⟩
      change _ ≤ prepCost (k+1) (tally M k+(if M k=true then 1 else 0)) _
      simp [bad]
      change gs.length≤prepCost k (tally M k) _ at gl
      unfold prepCost at gl ⊢; nlinarith

/-- One circuit over the unselected inputs returns the marked model for every singleton
selector simultaneously, for any chosen set of marks. -/
theorem extract_marked {V : Type} (P : Reverse.Prog n) (M : ℕ→Bool) (x : Fin n → Fn V) (sel : J → Fin n)
    (S : Set (Fn V)) (av : ∀ i, x i∈S) (cs : ∀ b, const b∈S) :
    ∃ gs : List (Node V), gs.length≤rowCost P.size (tally M P.size) (Fintype.card J) ∧
      ∀ j, Ready S gs (fun y => Prog.model P M 0 (fun i => x i y) (selected x (sel j) y)) := by
  obtain ⟨m,G,o,len,ev⟩ := mark_history (Net.empty (n:=n)) P
  simp only [Nat.zero_add] at len; subst m
  obtain ⟨gs,gl,gb,has⟩ := bases G x S av
  let T := pool S gs
  have lift : S⊆T := pool_grows _ _
  obtain ⟨hs,hl,hb,paid⟩ := prepare G x sel M T has (fun b => lift (cs b))
  let U := pool T hs
  have liftU : T⊆U := pool_grows _ _
  obtain ⟨ks,kl,kb,known⟩ := query G o x sel M U (fun i => liftU (has i)) (fun b => liftU (lift (cs b))) paid
  refine ⟨gs++hs++ks,?_,?_⟩
  · simp only [List.length_append,gl]; unfold rowCost prepCost at *; nlinarith
  · intro j
    apply ready_of_built (build_append (build_append gb hb) (by rwa [pool_append]))
    simp only [pool_append]
    have eq : G.row M x (inputs x sel j) o = fun y => Prog.model P M 0 (fun i => x i y) (selected x (sel j) y) := by
      funext y; exact ev V M x (inputs x sel j) y
    exact eq ▸ known j

end GateElim.Cuts
#print axioms GateElim.Cuts.extract_marked
