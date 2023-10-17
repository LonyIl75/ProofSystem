Require Import Arith.
Inductive is_fact : nat -> nat ->Prop :=
| is_fact_O : is_fact 0 (S 0) 
| is_fact_n : forall (n1 n2 :nat)  ,is_fact n1 n2 -> is_fact (S n1) (mult n2 (S n1)).

Fixpoint fact (n: nat ) {struct n} : nat :=
match n with 
|0=> 1
|S p => mult  n (fact p)
end.


Inductive is_fact2 : nat -> nat -> Prop :=
  | is_fact_O2 : is_fact2 O (S O)
  | is_fact_S2 : forall n m : nat, is_fact2 n m -> is_fact2 (S n) (mult m (S n)).


Fixpoint fact2 (n : nat) : nat :=
  match n with
    | O => (S O)
    | (S p) => (mult (fact2 p) n)
  end.

Require Import FunInd.
Functional Scheme fact_ind2 := Induction for fact2 Sort Prop.

Print fact_ind2 .


fact_ind2 = 
fun (P : nat -> nat -> Prop) (f0 : forall n : nat, n = 0 -> P 0 1)
  (f : forall n p : nat, n = S p -> P p (fact2 p) -> P (S p) (fact2 p * n)) =>
fix fact3 (n : nat) : P n (fact2 n) :=
  eq_ind_r (fun n0 : nat => P n n0)
    (let f1 : n = 0 -> P 0 1 := f0 n in
     let f2 : forall p : nat, n = S p -> P p (fact2 p) -> P (S p) (fact2 p * n) :=
       f n in
     match
       n as n0
       return
         (n = n0 ->
          (forall p : nat, n0 = S p -> P p (fact2 p) -> P (S p) (fact2 p * n0)) ->
          (n0 = 0 -> P 0 1) ->
          P n0 match n0 with
               | 0 => 1
               | S p => fact2 p * n0
               end)
     with
     | 0 =>
         fun (_ : n = 0)
           (_ : forall p : nat, 0 = S p -> P p (fact2 p) -> P (S p) (fact2 p * 0))
           (f4 : 0 = 0 -> P 0 1) => let f5 : P 0 1 := f4 eq_refl in f5
     | S n0 =>
         fun (_ : n = S n0)
           (f3 : forall p : nat,
                 S n0 = S p -> P p (fact2 p) -> P (S p) (fact2 p * S n0))
           (_ : S n0 = 0 -> P 0 1) =>
         let f5 : P n0 (fact2 n0) -> P (S n0) (fact2 n0 * S n0) :=
           let p := n0 in let H : S n0 = S p := eq_refl in f3 p H in
         let f6 : P (S n0) (fact2 n0 * S n0) :=
           let Hrec : P n0 (fact2 n0) := fact3 n0 in f5 Hrec in
         f6
     end eq_refl f2 f1) (fact2_equation n)
     : forall P : nat -> nat -> Prop,
       (forall n : nat, n = 0 -> P 0 1) ->
       (forall n p : nat, n = S p -> P p (fact2 p) -> P (S p) (fact2 p * n)) ->
       forall n : nat, P n (fact2 n)

Arguments fact_ind2 (_ _ _)%function_scope _%nat_scope
