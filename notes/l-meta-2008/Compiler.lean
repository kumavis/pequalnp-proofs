import DeskBridge
import Frontier

/-! Compile a function-labelled program back to the actual normalized fan-in-two
circuit format, simplifying constant operands and aliases without counting them.
The change of input coordinates is explicit. -/
namespace GateElim
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Desk2008.Fanout Desk2008.WireMono
open Classical
variable {V : Type*}

def combine {U : Type*} (o : Bool) (f g : Fn U) : Fn U :=
  fun x => if o then f x || g x else f x && g x

def Rep (n : ℕ) (pre : List Gate) (f : Fn (Fin n)) :=
  (∃ b, f=const b) ∨ ∃ i<n+pre.length, ∀ x, f x=val pre x i

def Clean (n : ℕ) (gs : List Gate) := Monotone2 ⟨gs,0⟩ ∧ Normal n ⟨gs,0⟩

private theorem snoc_clean {n : ℕ} {pre : List Gate} (clean : Clean n pre)
    (o : Bool) {a b : ℕ} (ab : a<b) (bound : b<n+pre.length) :
    Clean n (pre++[⟨if o then .or else .and,[a,b]⟩]) := by
  constructor
  · intro g hg
    change g∈pre++[_] at hg
    rcases List.mem_append.mp hg with orig|last
    · exact clean.1 g orig
    · have eq := List.mem_singleton.mp last; subst g
      cases o <;> simp
  · intro j g look
    change (pre++[_])[j]?=some g at look
    by_cases early : j<pre.length
    · rw [List.getElem?_append_left early] at look
      exact clean.2 j g look
    · rw [List.getElem?_append_right (by omega)] at look
      have pos := (List.getElem?_eq_some_iff.mp look).choose
      simp only [List.length_singleton] at pos
      have eq : j=pre.length := by omega
      subst j; simp at look; subst g; exact ⟨a,b,rfl,ab,bound⟩

private theorem old_rep {n : ℕ} {pre : List Gate} {f : Fn (Fin n)} (r : Rep n pre f) (g : Gate) :
    Rep n (pre++[g]) f := by
  rcases r with c|⟨i,hi,look⟩
  · exact Or.inl c
  · exact Or.inr ⟨i,by simp; omega,by intro x; rw [look,val_snoc,ite_eq_right (by omega)]⟩

private theorem add_wire {n : ℕ} {pre : List Gate} (clean : Clean n pre) (op : Bool)
    (f g : Fn (Fin n)) (fr : Rep n pre f) (gr : Rep n pre g) :
    ∃ after : List Gate, after.length≤pre.length+1 ∧ Clean n after ∧
      (∀ h, Rep n pre h → Rep n after h) ∧ Rep n after (combine op f g) := by
  have reuse (h : Rep n pre (combine op f g)) :
      ∃ after : List Gate, after.length≤pre.length+1 ∧ Clean n after ∧
        (∀ h, Rep n pre h → Rep n after h) ∧ Rep n after (combine op f g) :=
    ⟨pre,by omega,clean,fun _ r => r,h⟩
  rcases fr with ⟨v,e⟩|⟨a,ha,fa⟩
  · subst f; apply reuse
    cases v <;> cases op <;> first | exact gr | exact Or.inl ⟨_,rfl⟩ | simpa [combine,const] using gr
  rcases gr with ⟨v,e⟩|⟨b,hb,gb⟩
  · subst g; apply reuse
    have fr' : Rep n pre f := Or.inr ⟨_,ha,fa⟩
    cases v <;> cases op
    · exact Or.inl ⟨false,by funext x; simp [combine,const]⟩
    · exact Or.inr ⟨a,ha,by intro x; simpa [combine,const] using fa x⟩
    · exact Or.inr ⟨a,ha,by intro x; simpa [combine,const] using fa x⟩
    · exact Or.inl ⟨true,by funext x; simp [combine,const]⟩
  by_cases same : a=b
  · apply reuse; exact Or.inr ⟨a,ha,by intro x; cases op <;> simp [combine,fa,gb,←same]⟩
  let fresh : Gate := ⟨if op then .or else .and,[min a b,max a b]⟩
  refine ⟨pre++[fresh],by simp,snoc_clean clean op (by omega) (by omega),fun _ h => old_rep h fresh,?_⟩
  apply Or.inr
  refine ⟨n+pre.length,by simp,?_⟩
  intro x
  rw [val_snoc,ite_eq_left rfl]
  by_cases ab : a≤b
  · cases op <;> simp [fresh,combine,fa,gb,GateOp.eval,Nat.min_eq_left ab,Nat.max_eq_right ab]
  · have ba : b≤a := by omega
    cases op <;> simp [fresh,combine,fa,gb,GateOp.eval,Nat.min_eq_right ba,Nat.max_eq_left ba,
      Bool.and_comm,Bool.or_comm]

theorem compile {n : ℕ} (embed : (Fin n→Bool)→(V→Bool)) {S : Set (Fn V)}
    {gs : List (Node V)} {F : Fn V} (ready : Ready S gs F) (pre : List Gate)
    (clean : Clean n pre) (available : ∀ f∈S, Rep n pre (f ∘ embed)) :
    ∃ after : List Gate, after.length≤pre.length+gs.length ∧ Clean n after ∧ Rep n after (F ∘ embed) := by
  induction gs generalizing S pre with
  | nil => exact ⟨pre,by simp,clean,available F ready⟩
  | cons g gs ih =>
    obtain ⟨pre',size,ok,old,new⟩ := add_wire clean g.useOr _ _ (available _ ready.1) (available _ ready.2.1)
    obtain ⟨after,cost,norm,rep⟩ := ih ready.2.2 pre' ok (by
      intro f hf
      rcases hf with e|orig
      · subst f; exact new
      · exact old _ (available _ orig))
    exact ⟨after,by simp; omega,norm,rep⟩

theorem finish {n : ℕ} (embed : (Fin n→Bool)→(V→Bool)) {S : Set (Fn V)}
    {gs : List (Node V)} {F : Fn V} (ready : Ready S gs F)
    (available : ∀ f∈S, Rep n [] (f ∘ embed)) (nonconst : ∀ b, F ∘ embed ≠ const b) :
    ∃ C : Circuit, C.size≤gs.length ∧ Normal n C ∧ Monotone2 C ∧ C.output<n+C.size ∧
      circuitFun n C=F ∘ embed := by
  have empty : Clean n [] := by
    constructor
    · intro g hg; cases hg
    · intro j g hg; change ([] : List Gate)[j]?=some g at hg; simp at hg
  obtain ⟨pre,size,clean,r⟩ := compile embed ready [] empty available
  rcases r with ⟨b,e⟩|⟨i,bound,look⟩
  · exact (nonconst b e).elim
  · exact ⟨⟨pre,i⟩,by simpa [Circuit.size] using size,clean.2,clean.1,bound,by funext x; exact (look x).symm⟩

end GateElim
#print axioms GateElim.finish
