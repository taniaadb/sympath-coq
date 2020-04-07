From SYMPATH Require Export PLSyntax.
From Coq Require Import Lists.ListSet. (*light implementation of finitite sets*)
From Coq Require Import Lists.List.
Import ListNotations.
Require Import Coq.Sets.Ensembles.
  

Module Thread.
  Import Statement.

  Inductive threadId : Type := id (n: nat).
  
  Inductive thread : Type :=
  | TIdle
  | Thread (i : threadId) (s : statements) . (*Should we just use a nat instead of threadId?*)

  (*Do we need to define a new scope here? Not doing it for now*)


  Notation "'idle'" := TIdle.
  Notation "'<<' i '|' s '>>'" := (Thread i s).

  Check idle.
  Check Thread(id(0))(test_statement). (*Without taking notation in consideration*)
  Check (<<id(0) | test_statement >>).

End Thread.

Module Sympath.
  Import Expr.
  Import SymExpr.
  Import Thread.

  Check empty_set.
  

  (*Inductive Vars : Set := *)




  
