Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.ZArith. (*Z instead of nat?*)
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import FSets.FMapList.
From Coq Require Import Lists.ListSet.
Require Import Maps.
Import ListNotations.

(** * Arithmetic and Boolean Expressions *)

Module SymPaths. (*NOT Module Type! just module*)

  (*We want ints, booleans and vars to be the basic expressions that we use to build other expressions on.  I diferentiate between boolean and arithmetic expressions and include variables with the arithmetic expressions*)
  (*OBS: we assume that all variables are global and that they only hold numbers. We use strings to represent variables*)


  Inductive aexpr : Type := (*arithmetic expressions based on Integers*)
  | ANum (n : nat)
  | APlus (a1 a2 : aexpr)
  | AVar (s : string) (*seems to be best*)
  | AMult (a1 a2 : aexpr).

  Inductive bexpr : Type := (*boolean expressions*)
  | BTrue
  | BFalse
  (*| BVar (x : string)  (*have not changed it yet*) *)
  | BNot (b1 : bexpr)
  | BAnd (b1 b2 : bexpr)
  | BEq (a1 a2 : aexpr)
  | BLessThan (a1 a2 : aexpr).

  (*Add Notation!*)

  Coercion ANum : nat >-> aexpr. (*to avoid writing Anum everytime*)
  Coercion AVar : string >-> aexpr.
  (**Coercion BVar : string >-> bexpr. (*look here!*)  *)
  Definition bool_to_bexpr (b : bool) : bexpr :=
    if b then BTrue else BFalse.
  Coercion bool_to_bexpr : bool >-> bexpr. 

  (*scope*)
  Bind Scope expr_scope with aexpr.
  Bind Scope expr_scope with bexpr.
  Delimit Scope expr_scope with expr.

  Notation "x + y" := (APlus x y) (at level 50, left associativity) : expr_scope.

  Notation "x * y" := (AMult x y) (at level 40, left associativity) : expr_scope.
  Notation "x < y" := (BLessThan x y) (at level 70, no associativity) : expr_scope.
  Notation "x = y" := (BEq x y) (at level 70, no associativity) : expr_scope.
  Notation "x && y" := (BAnd x y) (at level 40, left associativity) : expr_scope.
  Notation "'~' b" := (BNot b) (at level 75, right associativity) : expr_scope.

  Check (1 + "X"%string)%expr. (*-> with notation*)
  Check (APlus 1  3). (*-> without notation*)
  Check (APlus (ANum 1) (ANum 3)). (* -> without coercion*)

  
  Inductive LInt : Type := x (n: nat).
  Inductive LBool : Type := b (n: nat).

  Check x(1).
  Check b(101).

  Inductive symExprInt : Type :=
  | SymLInt (x : LInt)
  | SymInt (n : nat)
  | SymPlus (a1 a2 : symExprInt)
  | SymMult (a1 a2 : symExprInt).

  Inductive symExprBool : Type :=
  | SymLBool (b : LBool)
  | SymBool (b : bool)
  | SymNot (b : symExprBool)
  | SymAnd (b1 b2 : symExprBool)
  | SymEqInt (a1 a2 : symExprInt)
  | SymEqBool (b1 b2 : symExprBool). (*can i define SymEq for both bool and int?*)

  Coercion SymInt : nat >-> symExprInt.
  Coercion SymLInt : LInt >-> symExprInt.
  Coercion SymBool : bool >-> symExprBool.
  Coercion SymLBool : LBool >-> symExprBool.

  Bind Scope symexpr_scope with symExprInt.
  Bind Scope symexpr_scope with symExprBool.
  Delimit Scope symexpr_scope with symexpr.


  Notation "x + y" := (SymPlus x y) (at level 50, left associativity) : symexpr_scope.
  Notation "x * y" := (SymMult x y) (at level 40, left associativity) : symexpr_scope.
  Notation "x = y" := (SymEqInt x y) (at level 70, no associativity) : symexpr_scope.
  Notation "x == y" := (SymEqBool x y) (at level 70, no associativity) : symexpr_scope.
  Notation "x && y" := (SymAnd x y) (at level 40, left associativity) : symexpr_scope.
  Notation "'~' b" := (SymNot b) (at level 75, right associativity) : symexpr_scope.

  Check (x(2))%symexpr.
  Check (b(2))%symexpr.
  Check (1 + x(2))%symexpr.
  Check (1 = 2)%symexpr.
  Check (true == true)%symexpr.


  Check (1 + 2)%expr.
  Check (1 + AVar "x")%expr.

  Inductive statements : Type :=
  | SAss (x : string) (a : aexpr) (*Cannot use AVar, maybe better to just define it here?
                                   No connection between var here and var in expr which
                                   is a bit unfortunate*)
  | SSkip
  | SIf (b : bexpr) (s1 s2 : statements)
  | SWhile (b : bexpr) (s : statements)
  | SNWhile (b : bexpr) (n : nat) (s : statements) (*more correct to use aexpr?*)
  | SSeq (s1 s2 : statements).

  Bind Scope stm_scope with statements.
  (***Bind Scope expr_scope with bexpr.
Bind Scope expr_scope with bexpr.
Delimit Scope stm_scope with expr. ***)

  Delimit Scope stm_scope with stm.
  (*better to have own scope with access to expr scope!*)

  Notation "'skip'" :=
    SSkip : expr_scope.
  Notation "x '::=' a" := (*cannot use :=*)
    (SAss x a) (at level 60) : stm_scope.
  Notation "s1 ;; s2" := (*cannot use ;*)
    (SSeq s1 s2) (at level 80, right associativity) : stm_scope.
  Notation "'WHILE' b 'DO' s 'END'" := (*cannot use byilt in syntax from Coq, that is why it needs to be written like this*)
    (SWhile b s) (at level 80, right associativity) : stm_scope.
  Notation "'WHILE' b 'FOR' n 'DO' s 'END'" := (*need to separate args*)
    (SNWhile b n s) (at level 80, right associativity) : stm_scope.
  Notation "'If' b 'THEN' s1 'ELSE' s2" :=
    (SIf b s1 s2) (at level 80, right associativity) : stm_scope.

  (*Definition test : statements :=*)

  (*Variables we are working with*)
  Definition X : string := "X".
  Definition Y : string := "Y".
  Definition Z : string := "Z". (*changed back, diff from AVar*)
  Definition W : string := "W". (*we differentiate between var between assign and after!*)
  (*that should not happen, we could use the same *)

  Check (Z ::= 1)%stm.
  Check (Z ::= X)%stm.
 (* Check (WHILE ~(W = 0) DO Y ::= Y * Z END)%stm.*)

  Definition test_statement : statements :=
    (Z ::= X;;
     Y ::= 1;;
     WHILE ~(Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z + 1
                   END)%stm.

  Definition test_nwhile : statements := 
    (Z ::= X;;
    WHILE ~(Z = 0) FOR 4 DO
       Y ::= Y * Z;;
       Z ::= Z + 1
                   END)%stm.
    

  Definition test_if : statements :=
    (If ~(Z = 0) THEN Y ::= 1 ELSE Y ::= 2)%stm.
  Check test_if. 
  (*One more type: program that kan have more proc and each proc has a S: statement*)

  Inductive procedure : Type :=
  | Proc (s : statements).
  Inductive program : Set := Prog (p : list procedure).

  Check Prog(Proc(test_statement) :: Proc(test_statement) :: nil). (*var 1*)
  Check Prog[].
  Check Prog[Proc(test_statement) ; Proc(test_statement)].
  Check Prog[Proc(test_statement)].


  Definition state := total_map nat.

  Definition empty_st := (_ !-> 0).

(** Now we can add a notation for a "singleton state" with just one
    variable bound to a value. *)
  Notation "a '!->' x" := (t_update empty_st a x) (at level 100).


  Fixpoint aeval (st : state) (a : aexpr) : nat :=
  match a with
  | ANum n => n
  | AVar v => st v                                (* <--- NEW , this is the state!*)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

  Fixpoint beval (st : state) (b : bexpr) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BNot b1 => negb (beval st b1)
    | BAnd b1 b2 => andb (beval st b1) (beval st b2)
    | BEq a1 a2 => (aeval st a1) =? (aeval st a2) (***does this work for strings*)
    | BLessThan a1 a2 => (aeval st a1) <? (aeval st a2)
    end.
  (*** we need to update the state*)
  
                
  Check aeval empty_st (1 + "X"%string)%expr.
  Compute aeval empty_st (1 + "X"%string)%expr.

  Compute beval empty_st (1 = 2)%expr.
  
  Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).

  (***need to add the others *)
  Inductive ceval : statements -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SSkip ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall s1 s2 st st' st'',
      st  =[ s1 ]=> st'  ->
      st' =[ s2 ]=> st'' ->
      st  =[ s1 ;; s2 ]=> st''                                          
  | E_IfTrue : forall st st' b s1 s2,
      beval st b = true ->
      st =[ s1 ]=> st' ->
      st =[ If b THEN s1 ELSE s2 ]=> st'
  | E_IfFalse : forall st st' b s1 s2,
      beval st b = false ->
      st =[ s2 ]=> st' ->
      st =[ If b THEN s1 ELSE s2 ]=> st'
  | E_WhileFalse : forall b st s,
      beval st b = false ->
      st =[ WHILE b DO s END ]=> st
  | E_WhileTrue : forall st st' st'' b s,
      beval st b = true ->
      st  =[ s ]=> st' ->
      st' =[ WHILE b DO s END ]=> st'' ->
      st  =[ WHILE b DO s END ]=> st''
  | E_WhileNFalse : forall b st n s,
      beval st b = false ->
      st =[ WHILE b FOR n DO s END ]=> st
  | E_WhileN0 : forall b st n s,
      beval st b = true ->
      n = 0 ->
      st =[ WHILE b FOR n DO s END ]=> st                                         
  | E_WhileNTrue : forall st st' st'' b n s,
      beval st b = true ->
      n > 0 ->
      st' =[ WHILE b FOR n-1 DO s END ]=> st'' ->
      st =[ WHILE b FOR n-1 DO s END ]=> st'' (*** where do we have n-1***)                                                                                 
  where "st =[ s ]=> st'" := (ceval s st st').

  Check empty_st =[ ("X"%string ::= 1) ]=> ("X"%string !-> 1).
  Example ceval_ex1:
    empty_st =[ ("X"%string ::= 1) ]=> ("X"%string !-> 1).
  Proof.
    apply E_Ass. simpl. reflexivity.
  Qed.

  Example ceval_ex2:
    empty_st =[
      "X"%string ::= 1 ;;
      If "X"%string < 1
         THEN "Y"%string ::= 3
         ELSE "Z"%string ::= 5
    ]=> ( "Z"%string !->5 ;  "X"%string !-> 1  ).
  Proof.
    apply E_Seq with (X !-> 1).
    - apply E_Ass. reflexivity.
    - apply E_IfFalse. reflexivity.
      apply E_Ass. reflexivity. Qed.

  (***Example ceval_ex3:
    empty_st =[
      "X"%string ::= 2 ;;
      WHILE ("X"%string > 1) DO
            "X"%string ::= "X"%string - 1
    END ]=> ("X"%string !-> 1 ).  (***does not work yet*) *)
    

  
End SymPaths.
