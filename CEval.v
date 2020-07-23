From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
Require Import Maps.

(*Importing Syntax file*)
Require Import SyntaxSym.
Import Syntax.

Module CEvalStep.

  (*Map that helps us access the value of variables*)
  Definition state := total_map nat.
  Definition empty_st := (_ !-> 0). (*default value in the map*)

  (* notation for a "singleton state" -> one variable bound to a value *)
  Notation "a '!->' x" := (t_update empty_st a x) (at level 100).
  (*Examples of how the map works*)
  Compute empty_st .
  Compute empty_st "x"%string .
  Compute (X !-> 3 ; X !-> 2 ; empty_st) X .

  (*As we have 2 different type of expressions, we need 2 different evaluations*)
  (*Can be done with relations as well as an alternative*)
  Fixpoint aeval (st : state) (a : aexpr) : nat :=
  match a with
  | ANum n => n
  | AVar v => st v                                
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

  (*Examples*)
  Compute (aeval (X !-> 1) (X + 1 + (3 * X))).
  Compute (aeval empty_st 2). 

  Fixpoint beval (st : state) (b : bexpr) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BNot b1 => negb (beval st b1)
    | BAnd b1 b2 => andb (beval st b1) (beval st b2)
    | BEq a1 a2 => (aeval st a1) =? (aeval st a2) 
    | BLessThan a1 a2 => (aeval st a1) <? (aeval st a2)
    end.

  (*Examples*)
  Check 3 = 4.
  Check aeval empty_st (1 + X)%expr.
  Compute aeval empty_st (1 + X).
  Compute beval empty_st (1 = 2).
  Compute beval ( X !-> 1 ; empty_st)  (X = 1)%expr.
  Compute aeval ( X !-> 2 ; Y !-> 3 ; empty_st) (X + Y)%expr.
  Compute beval ( X !-> 2 ; Y !-> 5 ; empty_st) (X < Y)%expr.
 
  (*For the evaluation of statements we will use SKIP to know when we reach the end of the
  execution aka have reached normal form -> we can also use idle as per the paper *)
  (*The while statement is the most interesting one, we use If stm , transform the while 
  into a conditional followed by the same WHILE *)
   
   Open Scope stm_scope. (*to avoid writing %stm after each statement*)
  
   Reserved Notation " t '/' st '-->' t' '/' st' " (at level 40, st at level 39, t' at level 39).
   (*CEval -> we have a small step evaluation here represented by a relation*)
    Inductive cstep : (statement * state) -> (statement * state) -> Prop :=
    | CS_Ass : forall st i a,
        (i ::= a) / st --> (SKIP) / (i !-> (aeval st a) ; st) 
    | CS_SeqStep : forall st s1 s1' s2 st',
        s1 / st --> s1' / st' ->
        (s1 ;; s2) / st --> (s1' ;; s2) / st'
    | CS_SeqFinish : forall st s2,
        (SKIP ;; s2) / st --> s2 / st 
    | CS_IfTrue : forall st s1 s2 b,
        (beval st b) = true ->
        (If b THEN s1 ELSE s2) / st --> s1 / st
    | CS_IfFalse : forall st s1 s2 b,
        (beval st b) = false ->
        (If b THEN s1 ELSE s2) / st --> s2 / st
    | CS_While : forall st b s,
        (WHILE b DO s END) / st -->
                           (If b THEN (s ;; (WHILE b DO s END)) ELSE SKIP) / st
    | CS_N0While : forall st b n s,
        n = 0 ->
        (WHILE b FOR n DO s END) / st -->
                           (SKIP) / st
     | CS_NWhile : forall st b n s,
        (WHILE b FOR n DO s END) / st -->
                           (If b THEN (s ;; (WHILE b FOR n-1 DO s END)) ELSE SKIP) / st
    where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).  

(*The hints are simplifying the proofs for wach statement*)
Hint Constructors cstep.

(*multi-step closure of a relation*)
Definition relation (X : Type) := X -> X -> Prop.
    
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
Hint Constructors multi.

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
     (at level 40, st at level 39, t' at level 39).

(*Examples illustrating how evaluation works*)
Example cstep_ex_skip :
  forall st,
    (SKIP) / st -->* (SKIP) / st .
Proof.
  auto. Qed. (*with Hint Constructors*) 
  (*intros st.
    apply multi_refl. Qed. -without hint constructors *)

Example cstep_ex_asgn :
    (Y ::= 3) / (X !-> 1) -->* (SKIP) / ( Y !-> 3 ; X !-> 1).
Proof.
  eauto. Qed. (*with hint constructors*) 
  (*eapply multi_step. {apply CS_Ass. }
                     apply multi_refl. Qed. (*without hint Constructors*) *)

Example cstep_ex2_asgn :
    (Y ::= 3) / (X !-> 1) --> (SKIP) / ( Y !-> 3 ; X !-> 1).
Proof.
  apply CS_Ass. Qed.

Example cstep_ex3_seq:
  (X ::= 1  ;; Y ::= 3) / empty_st -->* (SKIP) / ( Y !-> 3; X !-> 1) .

Proof.
  eauto. Qed. (*with hint constructors*)
  (*eapply multi_step.
  - eapply CS_SeqStep. apply CS_Ass.
  - eapply multi_step.
    + eapply CS_SeqFinish.
    + eapply multi_step. apply CS_Ass.
  apply multi_refl. Qed. *) (*without*)

Example cstep_ex4_if:
  stm_if / empty_st -->* (SKIP) / ( Z !-> 5 ;  X !-> 1 ).
Proof.
  unfold stm_if.
  eapply multi_step. eapply CS_SeqStep. apply CS_Ass. simpl.
  eapply multi_step. eapply CS_SeqFinish.
  eapply multi_step. apply CS_IfFalse. simpl. reflexivity. eapply multi_step. apply CS_Ass.
  apply multi_refl. Qed.

Example cstep_ex5_while:
  stm_while / empty_st -->* (SKIP) / (X !-> 1 ; X !-> 0).
Proof.
  unfold stm_while.
  eapply multi_step. eapply CS_SeqStep. apply CS_Ass.
  eapply multi_step. eapply CS_SeqFinish.
  eapply multi_step. apply CS_While.
  eapply multi_step. apply CS_IfTrue. reflexivity.  eapply multi_step. eapply CS_SeqStep.
         apply CS_Ass. simpl. 
  eapply multi_step. eapply CS_SeqFinish.
  eapply multi_step. eapply CS_While.
  eapply multi_step. eapply CS_IfFalse. reflexivity.
  apply multi_refl. Qed.

Example cstep_ex6_n_while:
  stm_n_while / (X !-> 0) -->* (SKIP) / (X !-> 2 ; X !-> 1 ; X !-> 0).
Proof.
  unfold stm_n_while.
  eapply multi_step. eapply CS_NWhile.
  eapply multi_step. apply CS_IfTrue. reflexivity. eapply multi_step. eapply CS_SeqStep.
         apply CS_Ass. eapply multi_step. apply CS_SeqFinish.
  eapply multi_step. eapply CS_NWhile.
  eapply multi_step. apply CS_IfTrue. reflexivity. eapply multi_step. eapply CS_SeqStep.
         apply CS_Ass.
  eapply multi_step. apply CS_SeqFinish.
  eapply multi_step. apply CS_N0While. reflexivity.
  eapply multi_refl. Qed.
   

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
    
    Reserved Notation " t '/' st '-->t' t' '/' st' "
             (at level 40, st at level 39, t' at level 39).

    (*Non-deterministic evaluation when threads are involved*)
    (*Also a small step evaluation as a relation*)
    Inductive tpstep : (threadPool * state) -> (threadPool * state) -> Prop :=
    | TS_T1 : forall st t1 t1' t2 st',
        t1 / st -->t t1' / st' ->
        (TPar t1 t2) / st -->t (TPar t1' t2) / st'
    | TS_T2 : forall st t1 t2 t2' st',
        t2 / st -->t t2' / st' ->
        (TPar t1  t2) / st -->t (TPar t1 t2') / st'
    | TS_ST1 : forall st s1 s1' st' n t2, (*when we arrive to statements*)
        s1 / st --> s1' / st' ->
        (TPar << id n | s1 >> t2) / st -->t (TPar << id n | s1' >> t2) / st'        
    | TS_ST2 : forall st s2 s2' st' t1 n, 
        s2 / st --> s2' / st' ->
        (TPar t1 << id n | s2 >>) / st -->t (TPar t1 << id n | s2' >>) / st'
    | TS_STDone : forall st n n',
        (TPar << id n | SKIP >> << id n' | SKIP >>) / st -->t
                                                    << id n | SKIP >> / st 
        
          where " t '/' st '-->t' t' '/' st' " := (tpstep (t, st) (t', st')).

Notation " t '/' st '-->t*' t' '/' st' " :=
   (multi tpstep  (t,st) (t',st'))
     (at level 40, st at level 39, t' at level 39).

(*Example of statement with threads*)
Definition stm_thread : threadPool :=
  (TPar
     (TPar
        << id 0 | Y ::= 1 >>
        << id 1 | (WHILE Y = 0 DO
                     X ::= X + 1
                     END) >> )
        << id 2 | Z ::= 5 >>).

(*Used in proof*)
Print ex_intro.

(*Examples illustrating how the evaluation of threads works*)
Example tpstep_ex1:
  exists st',
       stm_thread / empty_st  -->t* << id 0 | SKIP >> / st'
       /\ st' X = 0.
Proof.
  eapply ex_intro. split.
  unfold stm_thread.
  (*thread 1 first*)
  eapply multi_step. apply TS_T1.
  (*thread 1 in thread 1*)
  apply TS_ST1. apply CS_Ass.

  (*then thread 1 again*)
  eapply multi_step. apply TS_T1.
  (*and thread 2 in thread 1*)
  apply TS_ST2. apply CS_While.
  eapply multi_step. apply TS_T1. apply TS_ST2. apply CS_IfFalse. reflexivity. 
  eapply multi_step. apply TS_T1. apply TS_STDone.

  (*finally we look at thread 2*)
  eapply multi_step. apply TS_ST2. apply CS_Ass.
  eapply multi_step. apply TS_STDone. 
  eapply multi_refl.
  reflexivity. Qed. 

Example tpstep_ex2:
  exists st',
    stm_thread / empty_st -->t* Thread (id 0) (SKIP) /  st'
    /\ st' X = 1.
Proof.
  eapply ex_intro. split. unfold stm_thread. 
  (*thread 2 first*)
  eapply multi_step. apply TS_ST2. apply CS_Ass.

  (*then tread 1*)  
  eapply multi_step. apply TS_T1.
  (*thread 2 in thread 1 first*)
  apply TS_ST2. apply CS_While. 
  eapply multi_step. apply TS_T1. apply TS_ST2. apply CS_IfTrue. reflexivity.
  eapply multi_step. apply TS_T1. apply TS_ST2. apply CS_SeqStep. apply CS_Ass. simpl. 
  eapply multi_step. apply TS_T1. apply TS_ST2. apply CS_SeqFinish.

  (*then thread 1 in thread 1*)
  eapply multi_step. apply TS_T1. apply TS_ST1. apply CS_Ass.

  (*finally thread 2 in thread 1 again*)
  eapply multi_step. apply TS_T1. apply TS_ST2. apply CS_While. 
  eapply multi_step. apply TS_T1. apply TS_ST2. apply CS_IfFalse. reflexivity.
  eapply multi_step. apply TS_T1. apply TS_STDone.
  eapply multi_step. apply TS_STDone.
  apply multi_refl.
  reflexivity. Qed.   
  
Close Scope stm_scope.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2: X,
    R x y1 -> R x y2 -> y1 = y2.

(*should be attempted one more time*)
Theorem cstep_deterministic :
  deterministic cstep.
Proof. Admitted.

End CEvalStep.
