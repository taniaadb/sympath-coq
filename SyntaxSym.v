Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

Module Syntax.

  (*PART 1: Syntax of basic programming language PL *)

  (*** Arithmetic and Boolean Expressions 
   We want nats, booleans and vars to be the basic expressions that we use to build other
   expressions on.  I diferentiate between boolean and arithmetic expressions and include
   variables with the arithmetic expressions*)

  (*arithmetic expressions*)
  Inductive aexpr : Type := 
  | ANum (n : nat)
  | APlus (a1 a2 : aexpr)
  | AVar (s : string) 
  | AMult (a1 a2 : aexpr).

  (*boolean expressions*)
  Inductive bexpr : Type := 
  | BTrue
  | BFalse
  | BNot (b1 : bexpr)
  | BAnd (b1 b2 : bexpr)
  | BEq (a1 a2 : aexpr)
  | BLessThan (a1 a2 : aexpr).

  (*OBS: we assume that all variables are global and that they only hold numbers. We use 
  strings to represent variables*) 
  (*Variables we are working with - simplify notation*)
  Definition X : string := "X".
  Definition Y : string := "Y".
  Definition Z : string := "Z".
  Definition W : string := "W".

  (*Adding notation expressions*)
  Coercion ANum : nat >-> aexpr. (*to avoid writing Anum everytime*)
  Coercion AVar : string >-> aexpr.
  Definition bool_to_bexpr (b : bool) : bexpr :=
    if b then BTrue else BFalse.
  Coercion bool_to_bexpr : bool >-> bexpr. 

  (*scope expressions*)
  Bind Scope expr_scope with aexpr.
  Bind Scope expr_scope with bexpr.
  Delimit Scope expr_scope with expr.
  Check (0)%expr.

  Notation "x + y" := (APlus x y) (at level 50, left associativity) : expr_scope.

  Notation "x * y" := (AMult x y) (at level 40, left associativity) : expr_scope.
  Notation "x < y" := (BLessThan x y) (at level 70, no associativity) : expr_scope.
  Notation "x = y" := (BEq x y) (at level 70, no associativity) : expr_scope.
  Notation "x && y" := (BAnd x y) (at level 40, left associativity) : expr_scope.
  Notation "'~' b" := (BNot b) (at level 75, right associativity) : expr_scope.

  Check (1 + X)%expr. (*-> with notation*)
  Check (APlus 1  3). (*-> without notation*)
  Check (APlus (ANum 1) (ANum 3)). (* -> without coercion*)

  (*Statements existing in PL*)
  Inductive statement : Type :=
  | SAss (x : string) (a : aexpr) 
  | SSkip
  | SIf (b : bexpr) (s1 s2 : statement)
  | SWhile (b : bexpr) (s : statement) 
  | SNWhile (b : bexpr) (n : nat) (s : statement) (*limits the loop*)
  | SSeq (s1 s2 : statement).

  (*Notation statements*)
  Bind Scope stm_scope with statement.
  Delimit Scope stm_scope with stm.

  Notation "'SKIP'" :=
    (SSkip) (at level 60) : stm_scope.
  Notation "x '::=' a" := 
    (SAss x a) (at level 60) : stm_scope.
  Notation "s1 ;; s2" := 
    (SSeq s1 s2) (at level 80, right associativity) : stm_scope.
  Notation "'WHILE' b 'DO' s 'END'" := 
    (SWhile b s) (at level 80, right associativity) : stm_scope. 
  Notation "'WHILE' b 'FOR' n 'DO' s 'END'" := 
    (SNWhile b n s) (at level 80, right associativity) : stm_scope.
  (*If because of COQ built-in notaion*)
  Notation "'If' b 'THEN' s1 'ELSE' s2" :=
    (SIf b s1 s2) (at level 80, right associativity) : stm_scope.

  (*Examples statements*)
  Check (Z ::= 1)%stm.
  Check (Z ::= X)%stm.
  Check (WHILE ~(W = 0) DO Y ::= Y * Z END)%stm.

  (*We save these statements as we will refer to them later*)
  Definition stm_if : statement :=
    (X ::= 1 ;;
     If (X < 1)
        THEN Y ::= 3
                     ELSE Z ::= 5)%stm.
  Print stm_if.
  Check stm_if.

  Definition stm_while : statement :=
    X ::= 0 ;;
    WHILE (X < 1) DO
       X ::= X + 1
                   END.
  
  Definition stm_n_while : statement :=
    WHILE ~(X = 4) FOR 2 DO
       X ::= X + 1
                   END.

  (*Adding the threads -> these are wrappend in a thread id*)
   Inductive tid : Type := id (n : nat). 

   Inductive threadPool : Type :=
   | Thread (i : tid) (s : statement)
   | TPar (tp1 tp2: threadPool).

   Notation "'<<' i '|' s '>>'" := (Thread i s).
    (** Notation " t1 '//' t2 " := (TPar t1 t2) (at level 40, left associativity).
     This seems to be a bit too heavy *)
    (*OBS: level 80 is right associative, level 40 is left associative *)

      
   Check << id 0 | SKIP >>. 
   Check (TPar << id 0 | SKIP >> << id 1 | stm_if >>).
   Check (TPar (TPar << id 0 | SKIP >> << id 1 | stm_if >>) << id 2 | stm_n_while >>).

   
(*Example of statement with threads*)
 Definition stm_thread : threadPool :=
  (TPar
     (TPar
        << id 0 | Y ::= 1 >>
        << id 1 | (WHILE Y = 0 DO
                     X ::= X + 1
                     END) >> )
     << id 2 | Z ::= 5 >>).


 Definition example_article : threadPool :=
   (TPar
      << id 1 | X ::= 0 ;;
                X ::= Y + 1 >>
      << id 2 | If X = 0 THEN
                   Y ::= 0
                ELSE
                   Y ::= 1 >>).

  (*Ekstra: procedures and programs*)
  Inductive procedure : Type :=
  | Proc (s : statement).
  Inductive program : Set := Prog (p : list procedure).

  Check Prog(Proc(stm_if) :: Proc(stm_while) :: nil). 
  Check Prog[].
  Check Prog[Proc(stm_if) ; Proc(stm_if)].
  Check Prog[Proc(stm_while)].

  (*PART 2: Syntax of symbolic language used for evaluation*)
  
  (*Symbolic variables we are working with*)
  Inductive LNat :=
  | x (n: nat)
  | y (n: nat)
  | z (n: nat).
  Print LNat.

  Fixpoint comp_LNat (l1 l2: LNat) : bool :=
    match l1 with
    | x n =>
      match l2 with
      | x n' =>
        if beq_nat n n' then true else false
      | y n' => false
      | z n' => false
      end
        
    | y n =>
      match l2 with
      | x n' => false       
      | y n' => 
        if beq_nat n n' then true else false
      | z n' => false
      end
        
    | z n =>
      match l2 with
      | x n' => false
      | y n' => false
      | z n' =>
        if beq_nat n n' then true else false
      end
    end .
  
  Check x(0). 
  Compute (comp_LNat (x(0)) (x(0))).      
  Compute comp_LNat (x(0)) (x(1)).
  Compute comp_LNat (x(0)) (y(0)).

  Check x(0).
  Check y(8).

  (*Symbolic arithmetical expressions*)
  Inductive symExprArit : Type :=
  | SymLNat (x : LNat)
  | SymNat (n : nat)
  | SymPlus (a1 a2 : symExprArit)
  | SymMult (a1 a2 : symExprArit).

  (*Symbolic boolean expressions*)
  Inductive symExprBool : Type :=
  | SymBool (b : bool)
  | SymNot (b : symExprBool)
  | SymAnd (b1 b2 : symExprBool)
  | SymEq (a1 a2 : symExprArit)
  | SymLessThan (a1 a2 : symExprArit). 

  (*Notation*)
  Coercion SymNat : nat >-> symExprArit.
  Coercion SymLNat : LNat >-> symExprArit.
  Coercion SymBool : bool >-> symExprBool.

  Bind Scope symexpr_scope with symExprArit.
  Bind Scope symexpr_scope with symExprBool.
  Delimit Scope symexpr_scope with symexpr.

  Notation "x + y" := (SymPlus x y) (at level 50, left associativity) : symexpr_scope.
  Notation "x * y" := (SymMult x y) (at level 40, left associativity) : symexpr_scope.
  Notation "x = y" := (SymEq x y) (at level 70, no associativity) : symexpr_scope.
  Notation "x < y" := (SymLessThan x y) (at level 70, no associativity) : symexpr_scope.
  Notation "x && y" := (SymAnd x y) (at level 40, left associativity) : symexpr_scope.
  Notation "'~' b" := (SymNot b) (at level 75, right associativity) : symexpr_scope.

  (*Examples*)
  Check (0)%symexpr.
  Check (x(2))%symexpr.
  Check (1 + x(2))%symexpr. 
  Check (1 = 2)%symexpr.
  Check (1 + 2 + x(0))%symexpr.

  Check (1 + 2)%expr.
  Check (1 + AVar "x")%expr.

End Syntax.
