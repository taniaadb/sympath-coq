Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
Import ListNotations.
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

Fixpoint vars_arit (t : aexpr) : list string :=
  match t with
  | ANum n => []
  | AVar v => [v]
  | APlus a1 a2 => (vars_arit a1) ++ (vars_arit a2)
  | AMult a1 a2 => (vars_arit a1) ++ (vars_arit a2)
  end.
Compute vars_arit ((X + 1 + Y) * X).
(*Compute In X (vars_arit ((X + 1 + Y) * X)). *)

Fixpoint vars_bool (t : bexpr) : list string :=
  match t with
  | BTrue  => []
  | BFalse => []
  | BNot b => vars_bool b
  | BAnd b1 b2 => (vars_bool b1) ++ (vars_bool b2)
  | BEq a1 a2 => (vars_arit a1) ++ (vars_arit a2) 
  | BLessThan a1 a2 => (vars_arit a1) ++ (vars_arit a2)
  end.
Compute vars_bool ( ((X + 1 + Y) * X) = 2).

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
Check [1].
Check [X ; Y ; Z ; W].
(**)
Inductive event : Type :=
| Event (i : tid) (e : symExprBool) (r : list string) (w : list string).
Definition symPath := list event. 

Check [Event (id 0) (SymBool true) [X ; Y] [X ; Y] ; Event (id 1) (SymBool true) [X ; Y] [X ; Y]].

(*we need to keep conditions*)
Open Scope stm_scope.
(*symbolic evaluation of statements -> we need to add sympaths here*)
(*if rule is for the moment non-deterministic*)
(*I think sym_step might be the sympath if we add path conditions*)

(*Issue: how to go from SymExprBool to bool - What is true???*)
(*Reserved Notation "  t 'WITH' e '/' st '--[' l ']-->s' t' 'WITH' e' '/' st' "
         (at level 40, e at level 39, st at level 39, t' at level 39). I think there is an issue here*)
(*I need an extra predicate here*)
(*the predicate can be illustrated by a symExprBool*)
(*if this does not work one could change the type of statements??*)

(*maybe use SymBool True as automatic value*)
(*I think we actually need to gather the boolean conditions?*)
Check forall x y, x = y /\ x <> y.

Reserved Notation "  t 'WITH' e '/' st '--[' l ']-->s' t' 'WITH' e' '/' st' "
         (at level 40, e at level 39, st at level 39, t' at level 39). 

Inductive sym_step : tid -> (statement * symPath * sym_state) ->
                            (statement * symPath * sym_state) -> Prop :=

    | S_Ass : forall st i a l sp,        
        sym_step (l) (i ::= a, sp, st)
                     (SKIP,
                      sp ++ [ Event l (SymBool true) [i] (vars_arit a)],
                      (i !-> sym_aeval st a ; st)) 

    | S_SeqStep : forall st s1 s1' s2 l sp sp' st',
        sym_step (l) (s1, sp, st) (s1', sp', st') ->
        sym_step (l) (s1 ;; s2, sp, st)
                     (s1' ;; s2, sp', st')

    | S_SeqFinish : forall st s2 l sp,
        sym_step (l) (SKIP ;; s2, sp, st)
                     (s2, sp, st)

    | S_IfTrue : forall st b s1 s2 l sp,
        sym_step (l) (If b THEN s1 ELSE s2, sp, st)
                     (s1,
                      sp ++ [Event l (sym_beval st b) [] (vars_bool b)],
                      st) 
    | S_IfFalse : forall st b s1 s2 l sp,
        sym_step (l) (If b THEN s1 ELSE s2, sp, st)
                     (s2,
                      sp ++ [Event l (SymNot (sym_beval st b)) [] (vars_bool b)],
                      st)

    | S_WhileTrue : forall st b s l sp,
        sym_step (l) (WHILE b DO s END, sp, st)
                     (WHILE b DO s END,
                     sp ++ [Event l (sym_beval st b) [] (vars_bool b)],
                     st)
    | S_WhileFalse : forall st b s l sp,
        sym_step (l) (WHILE b DO s END, sp, st)
                     (SKIP,
                      sp ++ [Event l (SymNot (sym_beval st b)) [] (vars_bool b)],
                      st)

    | S_N0While : forall st b n s l sp,
        n = 0 ->
        sym_step (l) (WHILE b FOR n DO s END, sp, st)
                     (SKIP, sp, st)
       
    | S_NWhileTrue : forall st b n s l sp,
        sym_step (l) (WHILE b FOR n DO s END, sp, st)
                     (WHILE b FOR (n-1) DO s END,
                     sp ++ [Event l (sym_beval st b) [] (vars_bool b)],
                     st)
                     
    | S_NWhileFalse : forall st b n s l sp,
        sym_step (l) (WHILE b FOR n DO s END, sp, st)
                     (SKIP,
                      sp ++ [Event l (SymNot (sym_beval st b)) [] (vars_bool b)],
                      st).
                                 
(*where " t '/' e '/' st '--[' l ']-->s' t' '/' e' '/' st' " := (sym_step (l) (t,e,st) (t',e',st')). *)

(* Print Coercions.  *)
(* Print Classes. *)
(* Print Graph.  *)
(*Parameter Graph : Type. *)
    
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
