import Reverse
import RobustFanout

namespace GateElim.Reverse
open Desk2008 Desk2008.Fanout PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def opFlag : GateOp → Bool
  | .or => true
  | _ => false

/-- Parse the original gates in their original order, retaining operand indices.
The desk hypotheses independently guarantee that each gate is AND or OR. -/
def decode (n : ℕ) : List Gate → ℕ → Option (Prog n)
  | [], out => if h : out<n then some (.ret ⟨out,h⟩) else none
  | g::gs, out => match g.inputs with
    | [a,b] => if ha : a<n then if hb : b<n then
        (decode (n+1) gs out).map (.gate (opFlag g.op) ⟨a,ha⟩ ⟨b,hb⟩)
      else none else none
    | _ => none

private def allowed (n : ℕ) (gs : List Gate) :=
  ∀ k g, gs[k]?=some g → ∃ a b, g.inputs=[a,b] ∧ a<n+k ∧ b<n+k

private def assigns (n : ℕ) (gs : List Gate) (y : ℕ → Bool) :=
  ∀ k g a b, gs[k]?=some g → g.inputs=[a,b] →
    y (n+k)=applyOp (opFlag g.op) (y a) (y b)

private theorem decode_ok (n : ℕ) (gs : List Gate) (out : ℕ) (ho : out<n+gs.length)
    (ok : allowed n gs) :
    ∃ p, decode n gs out=some p ∧ p.size=gs.length ∧
      ∀ y : ℕ → Bool, assigns n gs y → p.eval (fun i => y i.val)=y out := by
  induction gs generalizing n with
  | nil =>
    have h : out<n := by simpa using ho
    exact ⟨.ret ⟨out,h⟩,by simp [decode,h],rfl,fun _ _ => rfl⟩
  | cons g gs ih =>
    obtain ⟨a,b,ins,ha,hb⟩ := ok 0 g (by simp)
    simp only [Nat.add_zero] at ha hb
    have tailOk : allowed (n+1) gs := by
      intro k h hk; obtain ⟨u,v,uv,hu,hv⟩ := ok (k+1) h (by simpa using hk)
      exact ⟨u,v,uv,by omega,by omega⟩
    obtain ⟨p,par,len,ev⟩ := ih (n+1) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ho) tailOk
    refine ⟨.gate (opFlag g.op) ⟨a,ha⟩ ⟨b,hb⟩ p,by simp [decode,ins,ha,hb,par],
      by simp [Prog.size,len],?_⟩
    intro y run
    have tailRun : assigns (n+1) gs y := by
      intro k h u v hk uv
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run (k+1) h u v (by simpa using hk) uv
    have write := run 0 g a b (by simp) ins
    have wire : snoc (fun i : Fin n => y i.val)
        (applyOp (opFlag g.op) (y a) (y b)) = fun i : Fin (n+1) => y i.val := by
      funext i; cases i using Fin.lastCases with
      | last => simpa using write.symm
      | cast i => simp
    simpa only [Prog.eval,wire] using ev y tailRun

theorem parse_desk {n : ℕ} (C : Circuit) (normal : Normal n C) (hm : Monotone2 C)
    (out : C.output<n+C.size) :
    ∃ p, decode n C.gates C.output=some p ∧ p.size=C.size ∧ ∀ x, p.eval x=circuitFun n C x := by
  have ok : allowed n C.gates := by
    intro k g h
    obtain ⟨a,b,ins,ab,bl⟩ := normal _ _ h
    exact ⟨a,b,ins,by omega,bl⟩
  obtain ⟨p,par,len,ev⟩ := decode_ok n C.gates C.output out ok
  refine ⟨p,par,len,?_⟩
  intro x
  let y := Desk2008.WireMono.val C.gates x
  have run : assigns n C.gates y := by
    intro k g a b hg ins
    have range : k<C.size := (List.getElem?_eq_some_iff.mp hg).choose
    obtain ⟨u,v,uv,lt,back⟩ := normal _ _ hg
    rw [ins] at uv
    have eq : a=u ∧ b=v := by simpa using uv
    have result := eval_gate (n:=n) (C:=C) (v:=n+k) (a:=a) (b:=b) (g:=g)
      ⟨by omega,by omega⟩ (by simpa using hg) ins (by omega) (by omega) x
    have ops : g.op=.and ∨ g.op=.or := by
      simpa [Set.mem_insert_iff,Set.mem_singleton_iff] using (hm _ (List.mem_of_getElem? hg)).1
    rcases ops with op|op <;> simpa [applyOp,opFlag,op,GateOp.eval,y] using result
  have start : (fun i : Fin n => y i.val)=x := by
    funext i; exact Desk2008.WireMono.val_lt _ _ _ i.isLt
  change p.eval x=y C.output
  simpa only [start] using ev y run

end GateElim.Reverse
#print axioms GateElim.Reverse.parse_desk
