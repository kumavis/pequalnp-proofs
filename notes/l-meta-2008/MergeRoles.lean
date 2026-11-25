import MergeTrace

namespace GateElim.MergeTrace
open Reverse Finset Classical
variable {A J : Type*} [DecidableEq A] [Fintype J] {n : ℕ}

def roles {n : ℕ} (P : Prog n) (W : J→Fin n→Signal A) : List (Finset J) :=
  match P with
  | .ret _ => []
  | .gate op a b t => (univ.filter (fun j => merge op (W j a) (W j b)))::
      roles t (fun j => snoc (W j) (gate op (W j a) (W j b)))

@[simp] theorem roles_length (P : Prog n) (W : J→Fin n→Signal A) : (roles P W).length=P.size := by
  induction P with
  | ret => rfl
  | gate op a b t ih => simp [roles,Prog.size,ih]

theorem roles_total (P : Prog n) (W : J→Fin n→Signal A) :
    ((roles P W).map Finset.card).sum=∑ j,count P (W j) := by
  induction P with
  | ret => simp [roles,count]
  | gate op a b t ih =>
    simp only [roles,List.map_cons,List.sum_cons,ih,count,sum_add_distrib]
    rw [Finset.card_filter]

theorem threshold (L : List (Finset J)) (c : ℕ) :
    (L.map Finset.card).sum≤c*L.length+Fintype.card J*(L.filter (fun D => decide (c < D.card))).length := by
  induction L with
  | nil => simp
  | cons D L ih =>
    have cap := Finset.card_le_univ D
    by_cases h : c<D.card <;> simp [h,Nat.mul_add] <;> omega

end GateElim.MergeTrace
#print axioms GateElim.MergeTrace.roles_total
