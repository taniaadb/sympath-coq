From SYMPATH Require Export PLSyntax.
From Coq Require Import Lists.ListSet. (*light implementation of finitite sets*)
From Coq Require Import Lists.List.
Import ListNotations.
Require Import Coq.Sets.Ensembles.
From Coq Require Import Strings.String.
  

Module Thread.
  Import Statement.

  (*Inductive threadId : Type := id (n: nat).*)
  
  Inductive thread : Type :=
  | TIdle
  | Thread (id : nat) (s : statements) . (*Should we just use a nat instead of threadId? NO*) 

  (*Do we need to define a new scope here? Not doing it for now*)


  Notation "'idle'" := TIdle.
  Notation "'<<' i '|' s '>>'" := (Thread i s).

  Check idle.
  Check Thread(0)(test_statement). (*Without taking notation in consideration*)
  Check (<< 0 | test_statement >>).

End Thread.

Module Var.
  (*Better to declare it as list?*)
  (*Do we use the same vars as from Expr?*)
  (*I define new ones here*)

  Inductive vars : Type :=
  | Var (x:string)
  | VarUnion (V1 V2 : vars).

  Coercion Var : string >-> vars.
  Notation "{ x }" := (Var x).
  Notation "V1 ; V2" := (VarUnion V1 V2) (at level 20) : var_scope.

  Bind Scope var_scope with vars.
  Delimit Scope var_scope with var. 

  Check {"x"%string}.
  Check (VarUnion {"x"%string} {"y"%string}).
  Check (Var("x"%string) ;  Var("x"%string))%var. (*why it does not work with {x} ???*)
  (*do we need a separate module for this?*)
  
End Var.
  
Module Sympath.
  Import Expr.
  Import SymExpr.
  Import Thread.
  Import Var.

  (*what about event?*)
  Inductive symPath :=
  | SymEpsilon
  | SymSeq (s1 s2 : symPath)
  | SymEventInt (id : nat) (e : symExprInt) (V1 V2 : vars)
  | SymEventBool (id : nat) (e : symExprBool) (V1 V2 : vars).

  Notation "'epsilon'" := SymEpsilon .
  Check epsilon.

  Notation "s1 . s2" := (SymSeq s1 s2) (at level 50).
  Notation " id ( e ~ V1 ~ V2 )" := (SymEventInt id e V1 V2) (at level 50). (*does not work yet!*)
  (*Check (1 + x(2))%symexpr. -> does not work! *)
  Check (1 = 2)%symexpr.


  (*Definition test_ev : symExprInt :=
    (1 + x(2))%symexpr.*)
    

 (* Check (2 ( (1 + x(2))%symexpr ~ {x%string}  ~ {y%string})). *)
  
                

  
  

  (*Inductive Vars : Set := *)




  
