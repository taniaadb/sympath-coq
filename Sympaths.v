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
    (SWhile b n s) (at level 80, right associativity) : stm_scope.
  Notation "'IF' b 'THEN' s1 'ELSE' s2" :=
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

  (*One more type: program that kan have more proc and each proc has a S: statement*)

  Inductive procedure : Type :=
  | Proc (s : statements).
  Inductive program : Set := Prog (p : list procedure).

  Check Prog(Proc(test_statement) :: Proc(test_statement) :: nil). (*var 1*)
  Check Prog[].
  Check Prog[Proc(test_statement) ; Proc(test_statement)].
  Check Prog[Proc(test_statement)].

  (*Inductive threadId : Type := id (n: nat).*)

  Inductive thread : Type :=
  | TIdle
  | Thread (id : nat) (s : statements) . (*Should we just use a nat instead of threadId? NO? Why*)

  Notation "'idle'" := TIdle.
  Notation "'<<' i '|' s '>>'" := (Thread i s).

  Check idle.
  Check Thread(0)(test_statement). (*Without taking notation in consideration*)

  Definition thread_1 : thread :=  (<< 0 | test_statement >>).
  Check thread_1.
  Check [thread_1; << 1 | Z ::= 1%stm >>]. (*do not need to declare thread pool! it is just a list of threads *)
  (*how to make it set though? I cannot figure it out*)

  
  (* same variables from Expr- not sure if possible*)
  (*tests on set*)
  Check empty_set.
  Definition test_set : set nat := 
    [3 ; 2; 3].
  Check test_set.
  Print test_set.

  Definition V1 : list aexpr := [AVar "X"%string; AVar "Y"%string].
  Check V1.
  Definition V2 : list aexpr := [AVar "Z"%string].
  Check V2.

  (*we represent symPath as list of events (boolean)*)
  Inductive symEvent : Type := SymEventBool (id : nat) (e : symExprBool) (V1 V2 : list aexpr).
  Notation " id (( e -- V1 -- V2 )) " := (SymEventBool id e V1 V2) (at level 50).
  (*cannot use paranthesis, {, ; i do not even know what to use anymore...*)
  (*cannot use ~ either, used for negation, want to avoid using that*)
  (*define scope to be able to use more notation? not much of the difference, still cannot use a lot og signs*)
  (*aaaagh, i give up, maybe it is better to just not use any notation*)

  Definition test_expr1 : symExprBool :=
    (b(2) == true)%symexpr.
  Definition test_expr2 : symExprBool :=
    ( true && b(5) )%symexpr. (*error if paranthesis next to each other because of notation*)
  Check test_expr1.

  Check (SymEventBool 0 test_expr1 V1 V2). (*one event-no notation*)
  Definition event1 : symEvent := 0 ((test_expr1 -- V1 -- V2)).
  Definition event2 : symEvent := 1 ((test_expr2 -- V2 -- [AVar "X"%string; AVar "Y"%string; AVar "Z"%string])).
  Check event1.
  Check event2.

  Check [event1 ; event2; event1]. (*a lot better*)


  (*substitution -> this needs to be a recursive function*)
  (*in the Coq implementation we have both aexpr and bexpr so we need 2 versions of vars*)
  Fixpoint vars_aexpr (a : aexpr) : set aexpr :=
    match a with
    | ANum n => []
    | AVar s => [AVar s]
    | APlus a1 a2 => (vars_aexpr a1) ++ (vars_aexpr a2) (*set union*)
    | AMult a1 a2 => (vars_aexpr a1) ++ (vars_aexpr a2)
    end.

  Fixpoint vars_bexpr (b : bexpr) : set aexpr :=
    match b with
    | BTrue => []
    | BFalse => []
    (*| BVar s => [BVar s] *have not changed it yet*)
    | BNot b1 => [] (*cannot use b as it is a constructor*)
    | BAnd b1 b2 => []
    | BEq a1 a2 => (vars_aexpr a1) ++ (vars_aexpr a2)
    | BLessThan a1 a2 => (vars_aexpr a1) ++ (vars_aexpr a2) 
    end.
    

End SymPaths.
