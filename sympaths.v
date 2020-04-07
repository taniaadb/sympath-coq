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
  
    
Module Type SymExpr.

  (*Not sure what LInt and LBool are? so I am not defining them*)
  (*we have no variables defined her, we have to add them!*)

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

Module Type Statement (E : Expr).
  Import E. 

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
  
(*One more typw: program that kan have more proc and each proc has a S: statement*)

(*Module Type Program (S : Statement). (*dif between Module and Module Type ?*)
  Import S.

  Inductive program : Type :=  
  | Proc (s : statements).
  | Prog (p1 p2 : Proc). -> we come back to this*)

  
    
  
       
           
            
            
            
    
    



  
