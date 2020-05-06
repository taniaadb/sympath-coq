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
Import ListNotations.

(*We need maps for variables. We try to import the library from Coq*)

(** * Arithmetic and Boolean Expressions *)

Module Expr. (*NOT Module Type! just module*)

  (*We use int instead of nat taken from ZArith library -> do we need to import more stuff?*)
  (*Do we need int? -> used int in Maude interpretation, but the values in the paper are nat*)

  (*We want ints, booleans and vars to be the basic expressions that we use to build other expressions on.  I diferentiate between boolean and arithmetic expressions and include variables with the arithmetic expressions*)
  (*OBS: we assume that all variables are global and that they only hold numbers. We use strings to represent variables*)

   (*overflow problemer -> hvordan håndterer Coq det?; hvordan kan man representere det i Coq?*)
  
Inductive aexpr : Type := (*arithmetic expressions based on Integers*)
  | ANum (n : nat)
  | AVar (x : string)
  | APlus (a1 a2 : aexpr)
  | AMult (a1 a2 : aexpr).

Inductive bexpr : Type := (*boolean expressions*)
  | BTrue
  | BFalse
  | BVar (x : string)
  | BNot (b : bexpr)
  | BAnd (b1 b2 : bexpr)
  | BEq (a1 a2 : aexpr)
  | BLessThan (a1 a2 : aexpr).


(*Add Notation!*)

Coercion ANum : nat >-> aexpr. (*to avoid writing Anum everytime*)
Coercion AVar : string >-> aexpr.
Coercion BVar : string >-> bexpr. (*look here!*)
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


(*Connection between var and ints: each
    variable stores an int, we can represent the state as a
    mapping from strings to [Z], and will use [0] as default value
    in the store. --> do we neet this?*)

Check (1 * "X"%string)%expr. (*-> with notation*)
Check (true && "X"%string)%expr. 
Check (APlus 1  3). (*-> without notation*)
Check (APlus (ANum 1) (ANum 3)). (* -> without coercion*)
   
End Expr. 
  
    
Module SymExpr.

  (*Not sure what LInt and LBool are? so I am not defining them*)
  (*we have no variables defined her, we have to add them!*)

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


End SymExpr.

(*Module Type Statement(E:Expr). -> this is a module functor, Module that takes one or more Module s of some Module Type s as parameters - > not what we want*)
Module Statement.
  Import Expr. 

  Check (1 + 2)%expr.
  Check (1 + "x"%string)%expr.

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
Definition W : string := "W".
Definition X : string := "X".
Definition Y: string := "Y".
Definition Z : string := "Z".

Check (Z ::= 1)%stm.
Check (Z ::= X)%stm.
Check (WHILE ~(Z = 0) DO Y ::= Y * Z END)%stm. 

Definition test_statement : statements :=
  (Z ::= X;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z + 1
  END)%stm. 
  
End Statement. 
  
(*One more type: program that kan have more proc and each proc has a S: statement*)

Module Program.
  Import Statement.

  Inductive procedure : Type :=  
  | Proc (s : statements).

  (***Inductive program : Set :=
  | SProg (p: procedure)
  | Prog (p1 p2: procedure).***)

  Inductive program : Set := Prog (p : list procedure).
  (*Type : supertype/ what is the diff between Prop and Set really?*)
  (*If your type could have two or more distinguishable objects, put it in Set otherwise put it in Prop*)

  Check Prog(Proc(test_statement) :: Proc(test_statement) :: nil). (*var 1*)
  Check Prog[].
  Check Prog[Proc(test_statement) ; Proc(test_statement)].
  Check Prog[Proc(test_statement)].

  (*Do the procedures need to be different? Lists is a multiset here*)
End Program.
  

    
  
       
           
            
            
            
    
    



  
