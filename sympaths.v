Add LoadPath "/Users/tania-adelinabulz/Documents/Forskerlinja/Coq".

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

(*We need maps for variables. We try to import the library from Coq*)

(** * Arithmetic and Boolean Expressions *)

Module Type Expr.

  (*We use int instead of nat taken from ZArith library -> do we need to import more stuff?*)
  (*Do we need int? -> used int in Maude interpretation, but the values in the paper are nat*)

  (*We want ints, booleans and vars to be the basic expressions that we use to build other expressions on.  I diferentiate between boolean and arithmetic expressions and include variables with the arithmetic expressions*)
  (*OBS: we assume that all variables are global and that they only hold numbers. We use strings to represent variables*)

  
Inductive aexpr : Type := (*arithmetic expressions based on Integers*)
  | ANum (n : nat)
  | AVar (x : string)
  | APlus (a1 a2 : aexpr)
  | AMult (a1 a2 : aexpr).

Inductive bexpr : Type := (*boolean expressions*)
  | BTrue
  | BFalse
  | BNot (b : bexpr)
  | BAnd (b1 b2 : bexpr)
  | BEq (a1 a2 : aexpr)
  | BLessThan (a1 a2 : aexpr).


(*Add Notation!*)

Coercion ANum : nat >-> aexpr. (*to avoid writing Anum everytime*)
Coercion AVar : string >-> aexpr.
Definition bool_to_bexpr (b : bool) : bexpr :=
  if b then BTrue else BFalse.
Coercion bool_to_bexpr : bool >-> bexpr.

(*Not sure what these do... *)
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

(*Check (1 + 3)%expr. -> with notation*)
(*Check (Aplus 1  3). -> without notation*)
(*Check (Aplus (ANum 1) (ANum 3)). -> without coercion*)
   
End Expr. 
  
    
Module Type SymExpr.

  (*Not sure what LInt and LBool are? so I am not defining them*)

  Inductive symExprInt : Type :=
  | SymInt (n : nat)
  | SymPlus (a1 a2 : symExprInt)
  | SymMult (a1 a2 : symExprInt).

  Inductive symExprBool : Type :=
  | SymBool (b : bool)
  | SymNot (b : symExprBool)
  | SymAnd (b1 b2 : symExprBool)
  | SymEqInt (a1 a2 : symExprInt)
  | SymEqBool (b1 b2 : symExprBool). (*can i define SymEq for both bool and int?*)

Coercion SymInt : nat >-> symExprInt. 
Coercion SymBool : bool >-> symExprBool.

(*Not sure what these do... *)
Bind Scope symexpr_scope with symExprInt.
Bind Scope symexpr_scope with symExprBool.
Delimit Scope symexpr_scope with symexpr.

(*Print Grammar Tactic. *)

Notation "x + y" := (SymPlus x y) (at level 50, left associativity) : symexpr_scope.
Notation "x * y" := (SymMult x y) (at level 40, left associativity) : symexpr_scope.
Notation "x = y" := (SymEqInt x y) (at level 70, no associativity) : symexpr_scope.
Notation "x == y" := (SymEqBool x y) (at level 70, no associativity) : symexpr_scope.
Notation "x && y" := (SymAnd x y) (at level 40, left associativity) : symexpr_scope.
Notation "'~' b" := (SymNot b) (at level 75, right associativity) : symexpr_scope.

Check (1 + 2)%symexpr.
Check (1 = 2)%symexpr.
Check (true == true)%symexpr.

End SymExpr.

Module Statement (E : Expr).
  Import E. 

  Check (1 + 2)%expr. (*works!*)

  Inductive statements : Type :=
  | SAss (x : string) (a : aexpr) (*Cannot use AVar, maybe better to just define it here?
                                   No connection between var here and var in expr which 
                                   is a bit unfortunate*)
  | SSkip
  | SIf (b : bexpr) (s1 s2 : statements)
  | SWhile (b : bexpr) (s : statements)
  | SNWhile (b : bexpr) (n : nat) (s : statements) (*more correct to use aexpr?*)
  | SSeq (s1 s2 : statements).
  
      
Bind Scope expr_scope with statements.
Notation "'skip'" :=
   SSkip : expr_scope.
Notation "x '::=' a" := (*cannot use :=*)
  (SAss x a) (at level 60) : expr_scope.
Notation "s1 ;; s2" := (*cannot use ;*)
  (SSeq s1 s2) (at level 80, right associativity) : expr_scope.
Notation "'WHILE' b 'DO' s 'END'" := (*cannot use byilt in syntax from Coq, that is why it needs to be written like this*)
  (SWhile b s) (at level 80, right associativity) : expr_scope.
Notation "'WHILE' b 'FOR' n 'DO' s 'END'" := (*need to separate args*)
  (SWhile b n s) (at level 80, right associativity) : expr_scope.
Notation "'IF' b 'THEN' s1 'ELSE' s2" :=
  (SIf b s1 s2) (at level 80, right associativity) : expr_scope.

(*Definition test : statements :=*)

(*Variables we are working with*)
Definition W : string := "W".
Definition X : string := "X".
Definition Y: string := "Y".
Definition Z : string := "Z".

Check (Z ::= 1)%expr.
Check (Z ::= X)%expr.
Check (WHILE ~(Z = 0) DO Y ::= Y * Z END)%expr. 

Definition test_statement : statements :=
  (Z ::= X;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z + 1
  END)%expr.
  
End Statement. 
  
  
           
            
            
            
    
    



  
