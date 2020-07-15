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
   (*Notation "'WHILE' b 'FOR' n 'DO' s 'END'" := 
    (SNWhile b n s) (at level 80, right associativity) : stm_scope.   *)
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

  Definition stm_if : statements :=
    (X ::= 1 ;;
     If (X < 1)
        THEN Y ::= 3
        ELSE Z ::= 5)%stm.
  Check stm_if.

  Definition stm_while : statements :=
    X ::= 0 ;;
    WHILE (X < 1) DO
       X ::= X + 1
    END.

  Inductive procedure : Type :=
  | Proc (s : statements).
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

  (*
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
  (*| E_WhilenFalse : forall cond st s n,
      beval st cond = false ->
      st =[ WHILE cond FOR n DO s END ]=> st
  | E_Whilen0 : forall cond st s n,
      n = 0 ->
      st =[ WHILE cond FOR n DO s END ]=> st                                      
  | E_WhilenTrue : forall st st' st'' cond s n,
      beval st cond = true ->
      st  =[ s ]=> st' ->
      st' =[ WHILE cond FOR n DO s END ]=> st'' -> (*where can we decrement n???*)
      st  =[ WHILE cond FOR n-1 DO s END ]=> st'' *)
                                                                        
  where "st =[ s ]=> st'" := (ceval_relation s st st').

  (* Definition test_nwhile : statements := 
     (WHILE ~(Z = 0) FOR 2 DO
       Z ::= Z + 1
                   END)%stm. *)
   
  (* Example ceval_rel_while:
     (Z !-> 1) =[ test_nwhile ]=> (Z !->3; Z !-> 2; Z !-> 1).
   Proof.
     unfold test_nwhile. apply E_WhilenTrue. -> fails here *)

  
  Check empty_st =[ (X ::= 1) ]=> (X !-> 1).

  Example ceval_skip :
    empty_st =[ skip ]=> empty_st.
  Proof.
    apply E_Skip. Qed. 

    
  Example ceval_relation_ex1:
    empty_st =[ (X ::= 1) ]=> (X !-> 1).
  Proof.
    apply E_Ass. simpl. reflexivity.
  Qed.

  Example ceval_relation_ex2:
    (X !-> 1) =[ (Y ::= 3) ]=> ( Y !-> 3 ; X !-> 1).
  Proof.
    apply E_Ass. reflexivity. Qed. 

  Example ceval_relation_ex3:
    empty_st =[ (X ::= 1 ) ;; (Y ::= 3) ]=> ( Y !-> 3; X !-> 1).
  Proof.
    eapply E_Seq. apply E_Ass. reflexivity.
    -apply E_Ass. reflexivity. Qed. 

  Example ceval_relation_ex4:
    empty_st =[
      X ::= 1 ;;
      If X < 1
         THEN Y ::= 3
         ELSE Z ::= 5
    ]=> ( Z !->5 ;  X !-> 1  ).
  Proof.
    eapply E_Seq.
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
    eapply E_Seq. apply E_Ass. reflexivity.
    -eapply E_WhileTrue. reflexivity.
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
      assert (st'0 = st'). apply IHceval_relation1 in H6. symmetry in H6. assumption.  rewrite H10 in H9. apply IHceval_relation2 in H9. assumption. Qed. *)


  (*Single-step (can add multi-step) evaluation -> what we need for Threads!*)
  Inductive aval : aexpr -> Prop :=
  | av_num : forall n, aval (ANum n).
  
  Reserved Notation " t '/' st '-->a' t' " (at level 40, st at level 39).
  Inductive astep : state -> aexpr -> aexpr -> Prop :=
  | AS_Var : forall st i,
      AVar i / st -->a ANum (st i)
  | AS_Plus1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (APlus a1 a2) / st -->a (APlus a1' a2)
  | AS_Plus2 : forall st v a2 a2',
      aval v ->
      a2 / st -->a a2' ->
      (APlus v a2) / st -->a (APlus v a2')
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st -->a ANum (n1 + n2)
  | AS_Mult1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (APlus a1 a2) / st -->a (APlus a1' a2)
  | AS_Mult2 : forall st v a2 a2',
      aval v ->
      a2 / st -->a a2' ->
      (APlus v a2) / st -->a (APlus v a2')
  | A_Mult : forall st n1 n2,
      AMult (ANum n1) (ANum n2) / st -->a ANum (n1 * n2)
  where " t '/' st '-->a' t' " := (astep st t t').

  Reserved Notation " t '/' st '-->b' t' " (at level 40, st at level 39).
  Inductive bstep : state -> bexpr -> bexpr -> Prop :=
  | BS_NotStep : forall st b1 b1',
      b1 / st -->b b1' ->
      (BNot b1) /st -->b (BNot b1')
  | BS_NotTrue : forall st,
      (BNot BTrue) / st -->b BFalse
  | BS_NotFalse : forall st,
      (BNot BFalse) / st -->b BTrue
  | BS_AndStep : forall st b1 b1' b2,
      b1 / st -->b b1' ->
      (BAnd b1 b2) / st -->b (BAnd b1' b2)
  | BS_AndTrueStep : forall st b2 b2',
      b2 / st -->b b2' ->
      (BAnd BTrue b2) / st -->b (BAnd BTrue b2')
  | BS_AndTrueTrue : forall st,
      (BAnd BTrue BTrue) / st -->b BTrue
  | BS_AndTrueFalse : forall st,
      (BAnd BTrue BFalse) / st -->b BFalse
  | BS_AndFalse : forall st b2,
      (BAnd BFalse b2) / st -->b BFalse
  | BS_Eq1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (BEq a1 a2) / st -->b (BEq a1' a2)
  | BS_Eq2 : forall st v a2 a2',
      aval v ->
      a2 / st -->a a2' ->
      (BEq v a2) / st -->b (BEq v a2')
  | BS_Eq : forall st n1 n2,
      (BEq (ANum n1) (ANum n2)) / st -->b
                                (if (n1 =? n2) then BTrue else BFalse)
  | BS_Lt1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (BLessThan a1 a2) / st -->b (BLessThan a1' a2)
  | BS_Lt2 : forall st v a2 a2',
      aval v ->
      a2 / st -->a a2' ->
      (BLessThan v a2) / st -->b (BLessThan v a2')
  | BS_Lt : forall st n1 n2,
      (BLessThan (ANum n1) (ANum n2)) / st -->b
                                      (if (n1 <? n2) then BTrue else BFalse)
  where " t '/' st '-->b' t' " := (bstep st t t').

  (*For the evaluation of statements we will use SKIP to know when we reach the end of the executiom aka
 have reached normal form *)
  (*The while statement is the most interesting one, we use If stm , transform the while into a 
  conditional followed by the same WHILE *)

   Open Scope stm_scope.
    Reserved Notation " t '/' st '-->' t' '/' st' " (at level 40, st at level 39, t' at level 39).
    Inductive cstep : (statements * state) -> (statements * state) -> Prop :=
    | CS_AssStep : forall st i a a',
        a / st -->a a' ->
        (i ::= a ) / st --> (i ::= a') / st
    | CS_Ass : forall st i n,
        (i ::= (ANum n)) / st --> (skip) / (i !-> n ; st) 
    | CS_SeqStep : forall st s1 s1' s2 st',
        s1 / st --> s1' / st' ->
        (s1 ;; s2) / st --> (s1' ;; s2) / st'
    | CS_SeqFinish : forall st s2,
        (skip ;; s2) / st --> s2 / st 
    | CS_IfStep : forall st b b' s1 s2,
        b / st -->b b' ->
        (If b THEN s1 ELSE s2) / st --> (If b' THEN s1 ELSE s2) / st
    | CS_IfTrue : forall st s1 s2,
        (If BTrue THEN s1 ELSE s2) / st --> s1 / st
    | CS_IfFalse : forall st s1 s2,
        (If BFalse THEN s1 ELSE s2) / st --> s2 / st
    | CS_While : forall st b s,
        (WHILE b DO s END) / st -->
                           (If b THEN (s ;; (WHILE b DO s END)) ELSE skip) / st
                           (*this could be a good place to reduce n*) 
    where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).  

    Inductive threadPool : Type :=
    | Thread (s : statements)
    | TPar (tp1 tp2: threadPool).

    Coercion Thread : statements >-> threadPool.
    Check Thread(skip).
    Check (TPar (skip) (skip)).
    Check (TPar (TPar (skip) (skip)) (skip)). 
    
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
        (TPar (skip) (skip)) / st -->t Thread(skip) / st
        
          where " t '/' st '-->t' t' '/' st' " := (tpstep (t,st) (t', st')).
        
   
Definition relation (X : Type) := X -> X -> Prop.
    
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Definition cmultistep := multi cstep.

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

(*Examples taken from the book*)


Example cstep_ex_skip :
  forall st,
    (skip) / st -->* (skip) / st .
Proof.
    intros st.
    apply multi_refl. Qed.

Example cstep_ex_asgn :
    (Y ::= 3) / (X !-> 1) -->* (skip) / ( Y !-> 3 ; X !-> 1).
Proof.
  eapply multi_step. {apply CS_Ass. }
                     apply multi_refl. Qed.

Example cstep_ex2_asgn :
    (Y ::= 3) / (X !-> 1) --> (skip) / ( Y !-> 3 ; X !-> 1).
Proof.
  apply CS_Ass. Qed.

Example cstep_ex3_seq:
  (X ::= 1  ;; Y ::= 3) / empty_st -->* (skip) / ( Y !-> 3; X !-> 1) .

Proof.
  eapply multi_step.
  - eapply CS_SeqStep. apply CS_Ass.
  - eapply multi_step.
    + eapply CS_SeqFinish.
    + eapply multi_step. apply CS_Ass.
  apply multi_refl. Qed.

Example cstep_ex4_if:
    stm_if / empty_st -->* (skip) / ( Z !-> 5 ;  X !-> 1 ).
  Proof.
    eapply E_Seq.
    - apply E_Ass. reflexivity.
    - apply E_IfFalse. reflexivity.
      apply E_Ass. reflexivity. Qed.


    
    
        

Definition par_loop : com :=
  PAR
    Y ::= 1
  WITH
    WHILE Y = 0 DO
      X ::= X + 1
    END
    END.

Example par_loop_example_0:
  exists st',
       par_loop / empty_st  -->* SKIP / st'
    /\ st' X = 0.
Proof.
Remember eapply ex_intro. 
  Admitted. *)
                                                

                       
    
  
  
  
                                
                        
                   
    
  
Close Scope stm_scope.    
End SymPaths.
