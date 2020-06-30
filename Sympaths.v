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

Module SymPaths. 

  (*We want ints, booleans and vars to be the basic expressions that we use to build other expressions on.  I diferentiate between boolean and arithmetic expressions and include variables with the arithmetic expressions*)
  (*OBS: we assume that all variables are global and that they only hold numbers. We use strings to represent variables*)


  Inductive aexpr : Type := 
  | ANum (n : nat)
  | APlus (a1 a2 : aexpr)
  | AVar (s : string) 
  | AMult (a1 a2 : aexpr).

  Inductive bexpr : Type := (*boolean expressions*)
  | BTrue
  | BFalse
  | BNot (b1 : bexpr)
  | BAnd (b1 b2 : bexpr)
  | BEq (a1 a2 : aexpr)
  | BLessThan (a1 a2 : aexpr).

  (*Add Notation!*)

  Coercion ANum : nat >-> aexpr. (*to avoid writing Anum everytime*)
  Coercion AVar : string >-> aexpr.
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

  (*We need to decide how the while works*)
  Inductive statements : Type :=
  | SAss (x : string) (a : aexpr) 
  | SSkip
  | SIf (b : bexpr) (s1 s2 : statements)
  | SWhile (b : bexpr) (s : statements) 
  (*| SNWhile (b : bexpr) (n : nat) (s : statements) *)
  | SSeq (s1 s2 : statements).

  Bind Scope stm_scope with statements.
  Delimit Scope stm_scope with stm.

  Notation "'skip'" :=
    (SSkip) (at level 60) : stm_scope.
  Notation "x '::=' a" := 
    (SAss x a) (at level 60) : stm_scope.
  Notation "s1 ;; s2" := 
    (SSeq s1 s2) (at level 80, right associativity) : stm_scope.
  Notation "'WHILE' b 'DO' s 'END'" := 
    (SWhile b s) (at level 80, right associativity) : stm_scope. 
 (* Notation "'WHILE' b 'FOR' n 'DO' s 'END'" := 
    (SNWhile b n s) (at level 80, right associativity) : stm_scope.  *)
  Notation "'If' b 'THEN' s1 'ELSE' s2" :=
    (SIf b s1 s2) (at level 80, right associativity) : stm_scope.

  (*Variables we are working with*)
  Definition X : string := "X".
  Definition Y : string := "Y".
  Definition Z : string := "Z".
  Definition W : string := "W". 


  Check (Z ::= 1)%stm.
  Check (Z ::= X)%stm.
  Check (WHILE ~(W = 0) DO Y ::= Y * Z END)%stm.

  Definition test_statement : statements :=
    (Z ::= X;;
     Y ::= 1;;
     WHILE ~(Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z + 1
                   END)%stm.

 (* Definition test_nwhile : statements := 
    (Z ::= X;;
    WHILE ~(Z = 0) FOR 4 DO
       Y ::= Y * Z;;
       Z ::= Z + 1
                   END)%stm. *)
    

  Definition test_if : statements :=
    (If ~(Z = 0) THEN Y ::= 1 ELSE Y ::= 2)%stm.
  Check test_if. 


  Inductive procedure : Type :=
  | Proc (s : statements).
  Inductive program : Set := Prog (p : list procedure).

  Check Prog(Proc(test_statement) :: Proc(test_statement) :: nil). 
  Check Prog[].
  Check Prog[Proc(test_statement) ; Proc(test_statement)].
  Check Prog[Proc(test_statement)].


  Definition state := total_map nat.
  Definition empty_st := (_ !-> 0).

(** Now we can add a notation for a "singleton state" with just one
    variable bound to a value. *)
  Notation "a '!->' x" := (t_update empty_st a x) (at level 100).
  Compute empty_st .
  Compute empty_st "x"%string .
  Compute (X !-> 3 ; X !-> 2 ; empty_st) X .

(*Can be done with relations as well as an alternative*)
  Fixpoint aeval (st : state) (a : aexpr) : nat :=
  match a with
  | ANum n => n
  | AVar v => st v                                
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

  Fixpoint beval (st : state) (b : bexpr) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BNot b1 => negb (beval st b1)
    | BAnd b1 b2 => andb (beval st b1) (beval st b2)
    | BEq a1 a2 => (aeval st a1) =? (aeval st a2) 
    | BLessThan a1 a2 => (aeval st a1) <? (aeval st a2)
    end.
  

  Check 3 = 4.
  Check aeval empty_st (1 + "X"%string)%expr.
  Compute aeval empty_st (1 + "X"%string)%expr.

  Compute beval empty_st (1 = 2)%expr.
  Compute beval ( X !-> 1 ; empty_st)  (X = 1)%expr.
  Compute aeval ( X !-> 2 ; Y !-> 3 ; empty_st) (X + Y)%expr.
  Compute beval ( X !-> 2 ; Y !-> 5 ; empty_st) (X < Y)%expr.
  
  Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).

  (**This version has the normal while *)
  Inductive ceval_relation : statements -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Ass  : forall st a1 n l,
      aeval st a1 = n ->
      st =[ l ::= a1 ]=> (l !-> n ; st)
  | E_Seq : forall s1 s2 st st' st'',
      st  =[ s1 ]=> st'  ->
      st' =[ s2 ]=> st'' ->
      st  =[ s1 ;; s2 ]=> st''                                          
  | E_IfTrue : forall st st' cond s1 s2,
      beval st cond = true ->
      st =[ s1 ]=> st' ->
      st =[ If cond THEN s1 ELSE s2 ]=> st'
  | E_IfFalse : forall st st' cond s1 s2,
      beval st cond = false ->
      st =[ s2 ]=> st' ->
      st =[ If cond THEN s1 ELSE s2 ]=> st'
  | E_WhileFalse : forall cond st s,
      beval st cond = false ->
      st =[ WHILE cond DO s END ]=> st
  | E_WhileTrue : forall st st' st'' cond s,
      beval st cond = true ->
      st  =[ s ]=> st' ->
      st' =[ WHILE cond DO s END ]=> st'' ->
      st  =[ WHILE cond DO s END ]=> st''
                                                                        
  where "st =[ s ]=> st'" := (ceval_relation s st st').

  Check empty_st =[ (X ::= 1) ]=> (X !-> 1).
  Example ceval_relation_ex1:
    empty_st =[ (X ::= 1) ]=> (X !-> 1).
  Proof.
    apply E_Ass. simpl. reflexivity.
  Qed.

  Example ceval_relation_ex2:
    (X !-> 1) =[ (Y ::= 3) ]=> ( Y !-> 3; X !-> 1).
  Proof.
    apply E_Ass. reflexivity. Qed. 

  Example ceval_relation_ex3:
    empty_st =[ (X ::= 1 ) ;; (Y ::= 3) ]=> ( Y !-> 3; X !-> 1).
  Proof.
    apply E_Seq with ( X !-> 1 ). apply E_Ass. reflexivity.
    -apply E_Ass. reflexivity. Qed. 

  Example ceval_relation_ex4:
    empty_st =[
      X ::= 1 ;;
      If X < 1
         THEN Y ::= 3
         ELSE Z ::= 5
    ]=> ( Z !->5 ;  X !-> 1  ).
  Proof.
    apply E_Seq with (X !-> 1).
    - apply E_Ass. reflexivity.
    - apply E_IfFalse. reflexivity.
      apply E_Ass. reflexivity. Qed.

  Example ceval_relation_ex5:
    empty_st =[
      X ::= 0 ;;
      WHILE (X < 1) DO
            X ::= X + 1
                        END ]=> (X !-> 1 ; X !-> 0 ).
  Proof.
    apply E_Seq with (X !-> 0). apply E_Ass. reflexivity.
    -apply E_WhileTrue with (X !-> 1 ; X !-> 0). reflexivity.
     *apply E_Ass. simpl. reflexivity.
     *apply E_WhileFalse. simpl. reflexivity. Qed.

  Theorem cevalR_deterministic : forall s st st1 st2,
      st =[ s ]=> st1 ->
      st =[ s ]=> st2 ->
      st1 = st2. 
  Proof.
    intros. generalize dependent st2. induction H.
    -intros. inversion H0.  (* what do we need for thisto be true *) reflexivity.
    - intros. inversion H0. assert (n0 = n). rewrite H in H5. symmetry in H5. assumption.
      rewrite H6 . reflexivity.
    - intros. inversion H1. assert (st' = st'0). apply IHceval_relation1 in H4. assumption. rewrite <- H8 in H7. apply IHceval_relation2 in H7. assumption.
    - intros. inversion H1. apply IHceval_relation in H8. assumption. rewrite H in H7. discriminate H7.
    - intros. inversion H1. rewrite H in H7. discriminate H7. apply IHceval_relation in H8. assumption.
    - intros. inversion H0. reflexivity. rewrite H in H3. discriminate H3.
    - intros. inversion H2. rewrite <- H6 in H7. rewrite H in H7. discriminate H7.
      assert (st'0 = st'). apply IHceval_relation1 in H6. symmetry in H6. assumption.  rewrite H10 in H9. apply IHceval_relation2 in H9. assumption. Qed.  
 
      
  (*Evaluation as a function - step-indexed While but here we count down for all*)
  (*do we want the optional param or do we know how long the while will run *)
  Open Scope stm_scope. 
  Fixpoint ceval_function (st : state) (s : statements) (n : nat) : state :=
    match n with
    | 0 => st (* here is the issue - what do we return -> pb is it counts down for everything*)
    | S n' =>
      match s with
      | skip => st
      | l ::= a =>
              (l !-> aeval st a ; st)
      | s1 ;; s2 =>
              let st' := ceval_function st s1 n' in
                ceval_function st' s2 n'
      | If cond THEN s1 ELSE s2 =>
              if (beval st cond)
                then ceval_function st s1 n'
                else ceval_function st s2 n'
      | WHILE cond DO s1 END =>
              if (beval st cond)
                then let st' := ceval_function st s1 n' in
                   ceval_function st' s n'
                else st
      end
    end.
  Close Scope stm_scope. 
  
  Definition stm_while : statements :=
    X ::= 0 ;;
    WHILE (X < 3) DO
       X ::= X + 1
    END.

  (*OBS: as here we are dealing with a function, these are a lot easier to prove *)
  Example ceval_function_ex1 :
    ceval_function empty_st stm_while 4 = (X !-> 2 ; X !-> 1 ; X !-> 0).
  Proof. simpl. reflexivity. Qed.

  (* these evaluations are equivalent, can include a proof of equivalence:*)
  (**
Theorem cevalR_equiv_cevalR : forall c st st',
st =[ stm ]=> st' 
<-> exists i, ceval_function st stm i = st' .
   *)       

  Theorem cevalF_deterministic : forall s st st1 st2 i,
      ceval_function st s i = st1 ->
      ceval_function st s i = st2 ->
      st1 = st2 .
  Proof.
    intros. rewrite <- H.  rewrite <- H0. reflexivity. Qed. 
     
End SymPaths.
