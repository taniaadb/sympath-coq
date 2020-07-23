Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
Require Import Maps.

Require Import SyntaxSym.
Require Import CEval.
Import Syntax.
Import CEvalStep.

Module SymEvalStep. 
(*defining the mapping that keeps the symbolic evaluation of variables*)
(*as variables are defines only for arithmetical expressions we use
symExprArit as type*)

Open Scope symexpr. 
Definition sym_state := total_map symExprArit.
(*default value*)
Definition empty_sym_st := (_ !-> SymNat(0)).
Check empty_sym_st.

(*Classic notation for maps*)
Notation "a '!->' x" := (t_update empty_sym_st a x) (at level 100).
Compute empty_sym_st .
Compute empty_sym_st "x"%string .
Compute (X !-> x(0) + 3 ; X !-> x(0); empty_sym_st) X .
  
(*symbolic evaluation of arithmetic expressions*)
Fixpoint sym_aeval(st : sym_state) (t : aexpr) : symExprArit :=
  match t with
  | ANum n =>
      SymNat n
  | AVar v => st v
  | APlus a1 a2 => (sym_aeval st a1) + (sym_aeval st a2)
  | AMult a1 a2 => (sym_aeval st a1) * (sym_aeval st a2)
  end.

Compute sym_aeval (X !-> x(0) ; Y !-> y(0)) ((X + 1 + Y) * X ).
(*adding constant folding would be nice*)
Compute sym_aeval (X !-> (x(0) + 2 + 3)) X.

(*symbolic evaluation of boolean expressions*)
Fixpoint sym_beval(st : sym_state) (t : bexpr) : symExprBool :=
  match t with
  | BTrue  => SymBool true
  | BFalse => SymBool false 
  | BNot b => SymNot(sym_beval st b)
  | BAnd b1 b2 => (sym_beval st b1) && (sym_beval st b2)
  | BEq a1 a2 => (sym_aeval st a1) = (sym_aeval st a2) 
  | BLessThan a1 a2 => (sym_aeval st a1) < (sym_aeval st a2)
  end.

(*Fixpoint sym_beval' (st : sym_state) (b : bexpr) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BNot b1 => negb (sym_beval' st b1)
    | BAnd b1 b2 => andb (sym_beval' st b1) (sym_beval' st b2)
    | BEq a1 a2 => (sym_aeval st a1) =? (sym_aeval st a2)  (*a1 a2 are symExprArit so no go*)
    | BLessThan a1 a2 => (sym_aeval st a1) <? (sym_aeval st a2)
    end.
Compute sym_beval'  (X !-> x(0)) (BNot X). *)

Compute (sym_beval (X !-> x(5)) (3 = X + 5)).

(*I need to get the conditions!*)
(*Inductive symPath : Type :=
  | Not sure I need this since the conditions can be taken from stm*)
(*we need to keep conditions*)


Open Scope stm_scope.
(*symbolic evaluation of statements -> we need to add sympaths here*)
(*if rule is for the moment non-deterministic*)
(*I think sym_step might be the sympath*)
Reserved Notation "  t '/' e '/' st '--[' l ']-->s' t' '/' e' '/' st' "
         (at level 40, st at level 39, t' at level 39).
(*I need an extra predicate here*)
(*the predicate can be illustrated by a symExprBool*)
(*if this does not work one could change the type of statements??*)
Inductive sym_step : tid -> (statement * symExprBool * sym_state) ->
                     (statement * symExprBool * sym_state) -> Prop :=
    | S_Ass : forall st i a l,        
         sym_step (l) ((i ::= a),(SymBool true), st) ((SKIP), (SymBool true), (i !-> (sym_aeval st a) ; st))
    (*| S_SeqStep : forall st s1 s1' s2 st' l,
        s1 / st --[l]-->s s1' / st' ->
        (s1 ;; s2) / st --[l]-->s (s1' ;; s2) / st'
    | S_SeqFinish : forall st s2 l,
        (SKIP ;; s2) / st --[l]-->s s2 / st 
   (* | S_IfStep : forall st b s1 s2,
        (If b THEN s1 ELSE s2) / st --> (If (beval st b) THEN s1 ELSE s2) / st *)
    | S_IfTrue : forall st s1 s2 b l,
        (*(sym_beval st b) = SymBool true -> *)
        (If b THEN s1 ELSE s2) / st --[l]-->s s1 / st
    | S_IfFalse : forall st s1 s2 b l,
        (*(sym_beval st b) = SymBool false -> *)
        (If b THEN s1 ELSE s2) / st --[l]-->s s2 / st
    | S_While : forall st b s l,
        (WHILE b DO s END) / st --[l]-->s
                           (If b THEN (s ;; (WHILE b DO s END)) ELSE SKIP) / st
    | S_N0While : forall st b n s l,
        n = 0 ->
        (WHILE b FOR n DO s END) / st --[l]-->s
                           (SKIP) / st
     | S_NWhile : forall st b n s l,
        (WHILE b FOR n DO s END) / st --[l]-->s
                           (If b THEN (s ;; (WHILE b FOR n-1 DO s END)) ELSE SKIP) / st*) .
(*where " t '/' e '/' st '--[' l ']-->s' t' '/' e' '/' st' " := (sym_step (l) (t,e,st) (t',e',st')). *)
                                                                                                    
    
Notation " t '/' st '--[' l ']-->s*' t' '/' st' " :=
   (multi (sym_step (l)) (t,st) (t',st'))
     (at level 40, st at level 39, t' at level 39).
    
Example sym_step__if:
  stm_if / (X !-> x(0) ; Y !-> x(1) ; Z !-> x(2)) --[id 0]-->s*
  (SKIP) / (Y !-> (SymNat 3) ; X !-> (SymNat 1)  ; X !-> x(0) ; Y !-> x(1) ; Z !-> x(2)).
Proof. 
  unfold stm_if.
  eapply multi_step. apply S_SeqStep. apply S_Ass. simpl.
  eapply multi_step. apply S_SeqFinish.
  eapply multi_step. apply S_IfTrue. eapply multi_step.  apply S_Ass. simpl.
  eapply multi_refl. Qed.

(*symbolic evaluation of threads -> non-deterministc*)
(*OBS: we always reduce to the first thread*)
Reserved Notation " t '/' st '-->ts' t' '/' st' "
         (at level 40, st at level 39, t' at level 39).
Inductive tp_sym_step : (threadPool * sym_state) -> (threadPool * sym_state) -> Prop :=
    | S_T1 : forall st t1 t1' t2 st',
        t1 / st -->ts t1' / st' ->
        (TPar t1 t2) / st -->ts (TPar t1' t2) / st'
    | S_T2 : forall st t1 t2 t2' st',
        t2 / st -->ts t2' / st' ->
        (TPar t1 t2) / st -->ts (TPar t1 t2') / st'
    | S_ST1 : forall st s1 s1' st' n t2, 
        s1 / st --[id n]-->s s1' / st' ->
        (TPar << id n | s1 >> t2) / st -->ts (TPar << id n | s1' >> t2) / st'        
    | S_ST2 : forall st s2 s2' st' t1 n, 
        s2 / st --[id n]-->s s2' / st' ->
        (TPar t1 << id n | s2 >>) / st -->ts (TPar t1 << id n | s2' >>) / st'
    | S_STDone : forall st n n',
        (TPar << id n | SKIP >> << id n' | SKIP >>) / st -->ts << id n | SKIP >> / st
        
          where " t '/' st '-->ts' t' '/' st' " := (tp_sym_step (t,st) (t', st')). 

Notation " t '/' st '-->ts*' t' '/' st' " :=
   (multi tp_sym_step  (t,st) (t',st'))
     (at level 40, st at level 39, t' at level 39).

Example tp_sym_step_ex:
  exists st',
    stm_thread / (X !-> x(0) ; Y !-> x(1) ; X !-> x(2)) -->ts*
    << id 0 | SKIP  >> / st' /\ st' X = x(0) .
Proof.
  eapply ex_intro. split.
  unfold stm_thread.
  (*thread 1 first*)
  eapply multi_step. apply S_T1.
  (*thread 1 in thread 1*)
  apply S_ST1. apply S_Ass. simpl.

  (*then thread 1 again*)
  eapply multi_step. apply S_T1.
  (*and thread 2 in thread 1*)
  apply S_ST2. apply S_While.
  eapply multi_step. apply S_T1. apply S_ST2. apply S_IfFalse.  
  eapply multi_step. apply S_T1. apply S_STDone.

  (*finally we look at thread 2*)
  eapply multi_step. apply S_ST2. apply S_Ass. simpl.
  eapply multi_step. apply S_STDone. 
  eapply multi_refl.
  reflexivity. Qed. 
       
Close Scope symexpr. 
Close Scope stm_scope.                           


End SymEvalStep.
