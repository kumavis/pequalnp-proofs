import RemovePort
import ParseDesk
import Compiler

namespace GateElim.Port
open Reverse Finset Classical Desk2008 Desk2008.Fanout
variable {n : ℕ}
def supported (A : Finset (Fin n)) (x : Fin n → Bool) := ∀ i, x i=true → i∈A
def sources (A : Finset (Fin n)) (i : Fin n) : Fn (Fin n) := if i∈A then var i else const false

private theorem has_sources (A : Finset (Fin n)) (i : Fin n) : sources A i∈base A := by
  by_cases h : i∈A
  · exact Or.inr ⟨i,h,by simp [sources,h]⟩
  · exact Or.inl ⟨false,by simp [sources,h]⟩

private theorem src_inc (A : Finset (Fin n)) (i : Fin n) : inc (sources A i) := by
  by_cases h : i∈A <;> simp only [sources,h,↓reduceIte]
  · intro x y le hi; exact le i hi
  · intro x y _ h; exact h

private theorem src_id (A : Finset (Fin n)) (x : Fin n → Bool) (ok : supported A x) :
    (fun j => sources A j x)=x := by
  funext j
  by_cases h : j∈A
  · simp [sources,h,var]
  · have z : x j=false := Bool.eq_false_iff.mpr (fun v => h (ok j v))
    simp [sources,h,const,z]

private theorem rep_inputs (A : Finset (Fin n)) (f : Fn (Fin n)) (h : f∈base A) : Rep n [] (f ∘ id) := by
  rcases h with ⟨b,rfl⟩|⟨j,_,rfl⟩
  · exact Or.inl ⟨_,rfl⟩
  · exact Or.inr ⟨j.val,by simpa using j.isLt,fun x => (Desk2008.WireMono.val_lt [] x j.val j.isLt).symm⟩

theorem choose_input (A : Finset (Fin n)) (i : Fin n) (gs : List (Node (Fin n))) (F : Fn (Fin n))
    (ready : Ready (base A) gs F) (pos neg : (Fin n→Bool)→Prop)
    (posEx : ∃ y, pos y) (negEx : ∃ y, neg y)
    (pSupp : ∀ y, pos y → supported (A.erase i) y) (nSupp : ∀ y, neg y → supported (A.erase i) y)
    (correct : Answers pos neg F)
    (privateWitness : ∀ y, neg y → ∃ t, neg t ∧ below y t ∧ F (Function.update t i true)=true)
    (silent : F (Function.update (fun _ => false) i true)=false) :
    ∃ rest : List (Node (Fin n)), ∃ G, Ready (base (A.erase i)) rest G ∧
      Answers pos neg G ∧ rest.length+2≤gs.length := by
  classical
  obtain ⟨p,hp⟩ := posEx; obtain ⟨m,hm⟩ := negEx
  have nc (b : Bool) : F ∘ id≠const b := by
    intro e; have y := congrFun e p; have no := congrFun e m
    change F p=b at y; change F m=b at no
    have diff := (correct.1 p hp).symm.trans (y.trans (no.symm.trans (correct.2 m hm)))
    cases diff
  obtain ⟨C,cost,norm,mono,out,fnC⟩ := finish id ready (rep_inputs A) nc
  obtain ⟨P,_,len,ev⟩ := parse_desk C norm mono out
  have f (x) : P.eval x=F x := (ev x).trans (congrFun fnC x)
  let B := A.erase i
  let z := sources B
  have zoff : z i=const false := by simp [z,B,sources]
  have matchOff (y : Fin n→Bool) (supp : supported B y) :
      tag P z i (guard none) y=F y := by
    rw [tag_zero P z i zoff _ y rfl]; unfold fn; rw [show (fun j => z j y)=y from src_id B y supp,f]
  have matchOn (y : Fin n→Bool) (supp : supported B y) :
      tag P z i (const true) y=F (Function.update y i true) := by
    unfold tag; rw [show (fun j => z j y)=y from src_id B y supp]; exact f _
  have check : Sample pos neg (tag P z i (guard none)) (tag P z i (const true)) := {
    yes := fun y h => (matchOff _ (pSupp _ h)).trans (correct.1 _ h)
    no := fun y h => (matchOff _ (nSupp _ h)).trans (correct.2 _ h)
    witness := by
      intro y h; obtain ⟨t,nt,le,on⟩ := privateWitness _ h
      exact ⟨t,nt,le,(matchOn _ (nSupp _ nt)).trans on⟩
    silent := ⟨fun _ => false,(matchOn _ (by intro _ h; cases h)).trans silent⟩ }
  obtain ⟨rest,G,bu,av,ans,small⟩ := remove_aux P z i none (base B) pos neg
    ⟨_,hp⟩ ⟨_,hm⟩ (has_sources B) (src_inc B) (Or.inl ⟨false,rfl⟩) (fun _ _ _ h => h) zoff check
  refine ⟨rest,G,ready_of_built bu av,ans,?_⟩
  simp [fee] at small; omega

end GateElim.Port
#print axioms GateElim.Port.choose_input
