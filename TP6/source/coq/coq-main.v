

Require Import Arith.EqNat.
Require Import Bool. 

Require Export ZArith_base.
Local Open Scope Z_scope.

(* le type id est un type qui est definit par lui même  avec comme seul constructeur Id *)
Inductive id : Set :=
    Id : nat -> id. (* chaque relatif est associé à une id Z->id correspond au couple (v1 ,x1 ) avec v1 e Z*) 


(* nous definissons beq_id qui comme sont nom l'indique renvoie un booleen 
et correpond à la relation eq pour le type id *)


Definition beq_id (X1 : id) (X2 : id) : bool :=
    match (X1, X2) with
      (Id x1, Id x2) => beq_nat x1 x2 (* si X1 et X2 sont le resultat de la fonction Id appliqué à x1 et x2 resp alors beq_id X1 X2 <-> beq_nat x1x2 *)
    end.

(* nous devons definir une semantique pour chaque constructeur du type inductif id *)

(* State est un mapping de id vers nat , il représente l'état/valeurs des variables identifier par id  *)

Definition state := id ->Z.

(*
Parameter get : id -> state  -> option Z.

Require Import Omega. 

Definition binds (x:id) (v: Z) (E: state ) := get x E = Some v.

*)
(* soit empty_state une fonction totale qui associe à tout id de l'environement 0 *)
Definition empty_state : state := 
  fun _ => 0.

(* la fonction qui enrichie le contexte un peu a la maniere d'un cons voir Exemple *)
Definition update (st : state) (X : id) (z : Z) : state :=
  fun (X1 : id) => if (beq_id X X1) then z else st X1. (*cette ligne prend une id puis renvoie un nat donc c'est un state *)

(* si X1 est egal à X (X est la nouvelle var introduite par l'update st X n ) alors renvoie n
sinon renvoie sa valeur grace à "l'ancien"  state  *)


Definition X1 := Id 7.


Eval compute in (empty_state X1).  (* X1:=0 *)
Eval compute in ((update empty_state X1 (-100)) X1). (* X1:=100 *)

Eval compute in ((update (update empty_state X1 (-100)) X1 (-102)) X1). (* overwrite X1 *)

Definition X2 := Id 7.
Eval compute in ((update (update empty_state X1 100) X2 101) X1). (* beq_id X1 X2 donc X1=X2 := 101 *)

Definition X3 := Id 8.
Eval compute in ((update (update empty_state X1 100) X3 101) X3). (* X3:=101  *)



Inductive aexp : Type :=
  | ANum : Z -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp.

Definition X := Id 0.
Definition Y := Id 1.
Definition W := Id 2.
  
Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.



Fixpoint aeval (st : state) (a : aexp) : Z :=
  match a with
    | ANum z =>  z (* regle *)
    | AId id => st id
    | APlus e1 e2 => (aeval st e1) + (aeval st e2) (* ici != avant : aeval prend un state et une aexp donc ok *)
    | AMinus e1 e2 => (aeval st e1) - (aeval st e2)
    | AMult e1 e2 => (aeval st e1) * (aeval st e2)
    | ADiv e1 e2 => (aeval st e1) / (aeval st e2)
  end.


Fixpoint beval (st : state) (e : bexp) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => Zeq_bool (aeval st a1) (aeval st a2)
  | BLe a1 a2 => Zle_bool (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.


Inductive instr_dlh : Set :=
  | ISkip : instr_dlh
  | IAss : id -> aexp -> instr_dlh
  | ISeq : instr_dlh -> instr_dlh -> instr_dlh
  | IIf : bexp -> instr_dlh -> instr_dlh -> instr_dlh
  | IWhile : bexp -> instr_dlh -> instr_dlh.

Notation "'SKIP'" :=
  ISkip.
Notation "X '::=' a" :=
  (IAss X a) (at level 60).
Notation "i1 ; i2" :=
  (ISeq i1 i2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (IWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (IIf e1 e2 e3) (at level 80, right associativity).




Reserved Notation "i1 '/' st '||' st'" (at level 40, st at level 39). (* le reserved pour le where *)

Inductive ceval : instr_dlh -> state -> state -> Prop :=
  | E_Skip : forall (st : state),
      SKIP / st || st
  | E_Ass : forall (st : state) (a : aexp) (z : Z) (X : id),
       aeval st a = z ->  (X ::= a) / st || (update st X z)
  | E_Seq : forall (i1 i2 : instr_dlh) (st st' st'' : state),
       (i1 / st || st') -> (i2 / st' || st'') -> (i1 ; i2) / st || st''
  | E_IfTrue : forall (st st': state) (i1 i2 : instr_dlh ) (b : bexp),
       beval st b = true -> i1 / st || st' -> (IFB b THEN i1 ELSE i2 FI) / st || st'
  | E_IfFalse : forall (st st': state) (i1 i2 : instr_dlh ) (b : bexp),
       beval st b = false -> i2 / st || st' -> (IFB b THEN i1 ELSE i2 FI) / st || st'
  | E_WhileEnd : forall (st : state) (i1 : instr_dlh ) (b : bexp),
       beval st b = false -> (WHILE b DO i1 END) / st || st
  | E_WhileLoop : forall (st st' st'': state) (i1 : instr_dlh) (b : bexp),
       beval st b = true -> 
       i1 / st || st' ->
       (WHILE b DO i1 END) / st' || st'' -> 
       (WHILE b DO i1 END) / st || st''
  where "i1 '/' st '||' st'" := (ceval i1 st st').

(*

Inductive ceval : instr_dlh -> state -> state -> Prop :=
  | E_Skip : forall (st : state),
      (ceval ISkip  st  st)
  | E_Ass : forall (st : state) (a : aexp) (z : Z) (X : id),
       aeval st a = z ->  (ceval (IAss X  a)  st  (update st X z))
  | E_Seq : forall (i1 i2 : instr_dlh) (st st' st'' : state),
       (ceval i1  st  st' ) -> (ceval i2  st' st'') -> (ceval (ISeq i1  i2)  st  st'')
  | E_IfTrue : forall (st st': state) (i1 i2 : instr_dlh ) (b : bexp),
       beval st b = true -> (ceval i1  st st') -> ( ceval (IIf b  i1  i2 )  st st')
  | E_IfFalse : forall (st st': state) (i1 i2 : instr_dlh ) (b : bexp),
       beval st b = false -> (ceval i2  st  st') -> (ceval (IIf b  i1  i2 ) st st')
  | E_WhileEnd : forall (st : state) (i1 : instr_dlh ) (b : bexp),
       beval st b = false -> (ceval (IWhile b  i1 ) st  st)
  | E_WhileLoop : forall (st st' st'': state) (i1 : instr_dlh) (b : bexp),
       beval st b = true -> 
       (ceval i1  st st') ->
       (ceval (IWhile b  i1 )  st'  st'') -> 
       (ceval (IWhile b  i1 ) st  st'').


*)

(*

Inductive ceval : instr_dlh -> state -> state -> Prop :=
  | E_Skip : forall (E : state),
      E |- ISkip   ~~> E
  | E_Ass : forall (E : state) (e : aexp) (v : Z) (x : id),
       (aeval E e = v) ->  E |- x ::=  e  ~~>  (update E x v)
  | E_Seq : forall (i1 i2 : instr_dlh) (E E1 E2 : state),
       ( E |- i1  ~~>E1 ) -> (E1 |- i2  ~~> E2) -> E |- i1 ; i2 ~~>  E2
  | E_IfTrue : forall (E E': state) (i1 i2 : instr_dlh ) (e : bexp),
       (beval E e = true) -> (E |- i1 ~~> E') ->  E |- IFB e  THEN i1 ELSE i2 ~~> E'
  | E_IfFalse : forall (E E': state) (i1 i2 : instr_dlh ) (e : bexp),
       (beval E e = false) -> (E |- i2  ~~>  E') -> E |- IFB e THEN  i1 ELSE i2  ~~> E'
  | E_WhileTop : forall (E : state) (i : instr_dlh ) (e : bexp),
      (beval E e = false ) -> E |- WHILE e  DO i1  ~~>  E
  | E_WhileBot : forall (E E' E'': state) (i : instr_dlh) (e : bexp),
       beval E e = true -> 
       (E |- i  ~~> E') ->
       (E' |- WHILE e  DO i  ~~>  E'') -> 
       E |- WHILE e DO i  ~~>  E''
  where "E '|-' i '~~>' E'" := (ceval i E E').


*)







