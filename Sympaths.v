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

  
  Inductive LNat : Type := x (n: nat).
  (*technically if we do not have boolean variables, we should not need this*)
  Inductive LBool : Type := bB (n: nat).

  Check x(1).
  Check bB(101).

  Inductive symExprArit : Type :=
  | SymLNat (x : LNat)
  | SymNat (n : nat)
  | SymPlus (a1 a2 : symExprArit)
  | SymMult (a1 a2 : symExprArit).

  Inductive symExprBool : Type :=
  | SymLBool (b : LBool)
  | SymBool (b : bool)
  | SymNot (b : symExprBool)
  | SymAnd (b1 b2 : symExprBool)
  | SymEq (a1 a2 : symExprArit)
  | SymLessThan (a1 a2 : symExprArit). (*added to match bexpr*)

  Coercion SymNat : nat >-> symExprArit.
  Coercion SymLNat : LNat >-> symExprArit.
  Coercion SymBool : bool >-> symExprBool.
  Coercion SymLBool : LBool >-> symExprBool.

  Bind Scope symexpr_scope with symExprArit.
  Bind Scope symexpr_scope with symExprBool.
  Delimit Scope symexpr_scope with symexpr.


  Notation "x + y" := (SymPlus x y) (at level 50, left associativity) : symexpr_scope.
  Notation "x * y" := (SymMult x y) (at level 40, left associativity) : symexpr_scope.
  Notation "x = y" := (SymEq x y) (at level 70, no associativity) : symexpr_scope.
  Notation "x < y" := (SymLessThan x y) (at level 70, no associativity) : symexpr_scope.
  Notation "x && y" := (SymAnd x y) (at level 40, left associativity) : symexpr_scope.
  Notation "'~' b" := (SymNot b) (at level 75, right associativity) : symexpr_scope.

  Check (0)%symexpr.
  Check (x(2))%symexpr.
  Check (bB(2))%symexpr.
  Check (1 + x(2))%symexpr.
  Check (1 = 2)%symexpr.


  Check (1 + 2)%expr.
  Check (1 + AVar "x")%expr.

  (*We need to decide how the while works*)
  (*If we change aeval and beval, will this be affected?*)
  Inductive statement : Type :=
  | SAss (x : string) (a : aexpr) 
  | SSkip
  | SIf (b : bexpr) (s1 s2 : statement)
  | SWhile (b : bexpr) (s : statement) 
  | SNWhile (b : bexpr) (n : nat) (s : statement) 
  | SSeq (s1 s2 : statement).

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
    

  Inductive procedure : Type :=
  | Proc (s : statement).
  Inductive program : Set := Prog (p : list procedure).

  Check Prog(Proc(stm_if) :: Proc(stm_while) :: nil). 
  Check Prog[].
  Check Prog[Proc(stm_if) ; Proc(stm_if)].
  Check Prog[Proc(stm_while)].


  Definition state := total_map nat.
  Definition empty_st := (_ !-> 0).

(** Now we can add a notation for a "singleton state" with just one
    variable bound to a value. *)
  Notation "a '!->' x" := (t_update empty_st a x) (at level 100).
  Compute empty_st .
  Compute empty_st "x"%string .
  Compute (X !-> 3 ; X !-> 2 ; empty_st) X .
  

  (*Can be done with relations as well as an alternative*)
  (*We can add that*)
  Fixpoint aeval (st : state) (a : aexpr) : nat :=
  match a with
  | ANum n => n
  | AVar v => st v                                
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.
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
   

  Check 3 = 4.
  Check aeval empty_st (1 + "X"%string)%expr.
  Compute aeval empty_st (1 + "X"%string)%expr.

  Compute beval empty_st (1 = 2)%expr.
  Compute beval ( X !-> 1 ; empty_st)  (X = 1)%expr.
  Compute aeval ( X !-> 2 ; Y !-> 3 ; empty_st) (X + Y)%expr.
  Compute beval ( X !-> 2 ; Y !-> 5 ; empty_st) (X < Y)%expr.

  (*Single-step (can add multi-step) evaluation -> what we need for Threads!*)
  (*symbolic evaluation -> this needs to be changed*)
  (*what are the values if we have symbolic evaluation?*)
  Inductive aval : aexpr -> Prop :=
  | av_num : forall n, aval (ANum n).
  
  (*For the evaluation of statements we will use SKIP to know when we reach the end of the execution aka
 have reached normal form -> we can also use idle as per the paper *)
  (*The while statement is the most interesting one, we use If stm , transform the while into a 
  conditional followed by the same WHILE *)
  (*cstep should not change as it is aeval and beval that is different*)

   Open Scope stm_scope.
    Reserved Notation " t '/' st '-->' t' '/' st' " (at level 40, st at level 39, t' at level 39).
    Inductive cstep : (statement * state) -> (statement * state) -> Prop :=
    | CS_AssStep : forall st i a,
        (i ::= a ) / st --> (i ::= (aeval st a)) / st
    | CS_Ass : forall st i n,
        (i ::= (ANum n)) / st --> (SKIP) / (i !-> n ; st) 
    | CS_SeqStep : forall st s1 s1' s2 st',
        s1 / st --> s1' / st' ->
        (s1 ;; s2) / st --> (s1' ;; s2) / st'
    | CS_SeqFinish : forall st s2,
        (SKIP ;; s2) / st --> s2 / st 
    | CS_IfStep : forall st b s1 s2,
        (If b THEN s1 ELSE s2) / st --> (If (beval st b) THEN s1 ELSE s2) / st
    | CS_IfTrue : forall st s1 s2,
        (If BTrue THEN s1 ELSE s2) / st --> s1 / st
    | CS_IfFalse : forall st s1 s2,
        (If BFalse THEN s1 ELSE s2) / st --> s2 / st
    | CS_While : forall st b s,
        (WHILE b DO s END) / st -->
                           (If b THEN (s ;; (WHILE b DO s END)) ELSE SKIP) / st
    (*this could be a good place to reduce n*)
    | CS_N0While : forall st b n s,
        n = 0 ->
        (WHILE b FOR n DO s END) / st -->
                           (SKIP) / st
     | CS_NWhile : forall st b n s,
        (WHILE b FOR n DO s END) / st -->
                           (If b THEN (s ;; (WHILE b FOR n-1 DO s END)) ELSE SKIP) / st
    where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).  

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

Definition cmultistep := multi cstep.

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
                     apply multi_refl. Qed. without hint Constructors*)

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
  eapply multi_step. eapply CS_SeqStep. apply CS_Ass.
  eapply multi_step. eapply CS_SeqFinish.
  eapply multi_step. apply CS_IfStep. simpl. 
  eapply multi_step. apply CS_IfFalse. eapply multi_step. apply CS_Ass.
  apply multi_refl. Qed.

Example cstep_ex5_while:
  stm_while / empty_st -->* (SKIP) / (X !-> 1 ; X !-> 0).
Proof.
  (*eauto.- does not work, i assume becuase of simpl in the proof *)
  unfold stm_while.
  eapply multi_step. eapply CS_SeqStep. apply CS_Ass.
  eapply multi_step. eapply CS_SeqFinish.
  eapply multi_step. apply CS_While.
  eapply multi_step. apply CS_IfStep. simpl.
  eapply multi_step. apply CS_IfTrue. eapply multi_step. eapply CS_SeqStep.
         apply CS_AssStep. simpl. 
  eapply multi_step. eapply CS_SeqStep. apply CS_Ass.
  eapply multi_step. eapply CS_SeqFinish.
  eapply multi_step. eapply CS_While.
  eapply multi_step. eapply CS_IfStep. simpl.  
  eapply multi_step. eapply CS_IfFalse.
  apply multi_refl. Qed.

Example cstep_ex6_n_while:
  stm_n_while / (X !-> 0) -->* (SKIP) / (X !-> 2 ; X !-> 1 ; X !-> 0).
Proof.
  unfold stm_n_while.
  eapply multi_step. eapply CS_NWhile.
  eapply multi_step. apply CS_IfStep. simpl.
  eapply multi_step. apply CS_IfTrue. eapply multi_step. eapply CS_SeqStep.
     apply CS_AssStep. simpl. eapply multi_step. apply CS_SeqStep. apply CS_Ass.
     eapply multi_step. apply CS_SeqFinish.
  eapply multi_step. eapply CS_NWhile.
  eapply multi_step. apply CS_IfStep. simpl.
  eapply multi_step. apply CS_IfTrue. eapply multi_step. eapply CS_SeqStep.
     apply CS_AssStep. simpl. eapply multi_step. apply CS_SeqStep. apply CS_Ass.
     eapply multi_step. apply CS_SeqFinish.
     eapply multi_step. apply CS_N0While. reflexivity.
     eapply multi_refl. Qed.
     
     
 (*Adding the threads*)

    Inductive threadPool : Type :=
    | Thread (s : statement)
    | TPar (tp1 tp2: threadPool).

    Coercion Thread : statement >-> threadPool.
    Check Thread(SKIP).
    Check (TPar (SKIP) (stm_if)).
    Check (TPar (TPar (SKIP) (stm_if)) (stm_n_while)). 
    
    Reserved Notation " t '/' st '-->t' t' '/' st' " (at level 40, st at level 39, t' at level 39).
    Open Scope stm_scope. 
    Inductive tpstep : (threadPool * state) -> (threadPool * state) -> Prop :=
    | TS_T1 : forall st t1 t1' t2 st',
        t1 / st -->t t1' / st' ->
        (TPar t1 t2) / st -->t (TPar t1' t2) / st'
    | TS_T2 : forall st t1 t2 t2' st',
        t2 / st -->t t2' / st' ->
        (TPar t1 t2) / st -->t (TPar t1 t2') / st'
    | TS_ST1 : forall st s1 s1' s2 st', (*when we arrive to statements*)
        s1 / st --> s1' / st' ->
        (TPar s1 s2) / st -->t (TPar s1' s2) / st'        
    | TS_ST2 : forall st s1 s2 s2' st',
        s2 / st --> s2' / st' ->
        (TPar s1 s2) / st -->t (TPar s1 s2') / st'
    | TS_STDone : forall st,
        (TPar (SKIP) (SKIP)) / st -->t Thread(SKIP) / st
        
          where " t '/' st '-->t' t' '/' st' " := (tpstep (t,st) (t', st')).

Definition tmultistep := multi tpstep.

Notation " t '/' st '-->t*' t' '/' st' " :=
   (multi tpstep  (t,st) (t',st'))
     (at level 40, st at level 39, t' at level 39).
  
Definition stm_thread : threadPool :=
  (TPar
    (TPar
      (Y ::= 1)
      (WHILE Y = 0 DO
          X ::= X + 1
                      END) )
    (Z ::= 5)).

Check ex_intro.

Example tpstep_ex1:
  exists st',
       stm_thread / empty_st  -->t* Thread(SKIP) / st'
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
  eapply multi_step. apply TS_T1. apply TS_ST2. 
      apply CS_IfStep. simpl. 
  eapply multi_step. apply TS_T1. apply TS_ST2. apply CS_IfFalse.
  eapply multi_step. apply TS_T1. apply TS_STDone.

  (*finally we look at thread 2*)
  eapply multi_step. apply TS_ST2. apply CS_Ass.
  eapply multi_step. apply TS_STDone. 
  eapply multi_refl.
  reflexivity. Qed. 

Example tpstep_ex2:
  exists st',
    stm_thread / empty_st -->t* Thread(SKIP) /  st'
    /\ st' X = 1.
Proof.
  eapply ex_intro. split. unfold stm_thread. 
  (*thread 2 first*)
  eapply multi_step. apply TS_ST2. apply CS_Ass.

  (*then tread 1*)  
  eapply multi_step. apply TS_T1.
  (*thread 2 in thread 1 first*)
  apply TS_ST2. apply CS_While. 
  eapply multi_step. apply TS_T1. apply TS_ST2. apply CS_IfStep. simpl.  
  eapply multi_step. apply TS_T1. apply TS_ST2. apply CS_IfTrue.
  eapply multi_step. apply TS_T1. apply TS_ST2. apply CS_SeqStep. apply CS_AssStep. simpl.
  eapply multi_step. apply TS_T1. apply TS_ST2. apply CS_SeqStep. apply CS_Ass.
  eapply multi_step. apply TS_T1. apply TS_ST2. apply CS_SeqFinish.

  (*then thread 1 in thread 1*)
  eapply multi_step. apply TS_T1. apply TS_ST1. apply CS_Ass.

  (*finally thread 2 in thread 1 again*)
  eapply multi_step. apply TS_T1. apply TS_ST2. apply CS_While. 
  eapply multi_step. apply TS_T1. apply TS_ST2. apply CS_IfStep. simpl.
  eapply multi_step. apply TS_T1. apply TS_ST2. apply CS_IfFalse.
  eapply multi_step. apply TS_T1. apply TS_STDone.
  eapply multi_step. apply TS_STDone.
  apply multi_refl.
  reflexivity. Qed.   
  
Close Scope stm_scope.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2: X,
    R x y1 -> R x y2 -> y1 = y2.

Theorem cstep_deterministic :
  deterministic cstep.
Proof. Admitted.

(*Symbolical evaluation*)
(*Step 1 : Defining substitution -> function? *)
(*I think we want to have 2 subst, one for bool and one for arithmetics instead of beval and aeval*)

(*what about states??*)
(*we only define maping for SymArit, will that be a problem on the way?*)
Open Scope symexpr. 
Definition sym_state := total_map symExprArit.
Definition empty_sym_st := (_ !-> SymNat(0)).
Check empty_sym_st.

  Notation "a '!->' x" := (t_update empty_sym_st a x) (at level 100).
  Compute empty_sym_st .
  Compute empty_sym_st "x"%string .
  Compute (X !-> x(0) + 3 ; X !-> x(0); empty_sym_st) X .
  
(*How is this connected to normal subst, see down...*)
(*Do we not need states tho...*)
Fixpoint sym_aeval(st : sym_state) (t : aexpr) : symExprArit :=
  match t with
    (*possible aexpr*)
  | ANum n =>
      SymNat n
  | AVar v => st v
  | APlus a1 a2 => (sym_aeval st a1) + (sym_aeval st a2)
  | AMult a1 a2 => (sym_aeval st a1) * (sym_aeval st a2)
  end.

(*OBS: I updated sym expr and have equality only for ints*)
Fixpoint sym_beval(st : sym_state) (t : bexpr) : symExprBool :=
  match t with
  (*possible bexpr*)
  (*we use the notation from the symexpr module*)
  | BTrue  => SymBool true
  | BFalse => SymBool false 
  | BNot b => SymNot(sym_beval st b)
  | BAnd b1 b2 => (sym_beval st b1) && (sym_beval st b2)
  | BEq a1 a2 => (sym_aeval st a1) = (sym_aeval st a2) 
  | BLessThan a1 a2 => (sym_aeval st a1) < (sym_aeval st a2)
  end.

Compute (sym_beval (X !-> x(5)) (3 = X + 5)).
Close Scope symexpr. 
                           
          
(*Example of substitution from book:
Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var x' =>
      if eqb_string x x' then s else t
  | abs x' T t1 =>
      abs x' T (if eqb_string x x' then t1 else ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | tru =>
      tru
  | fls =>
      fls
  | test t1 t2 t3 =>
      test ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).*)

End SymPaths.
