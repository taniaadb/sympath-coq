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
Compute (sym_beval (X !-> x(5)) (3 = X + 5)).

(*I need to get the conditions!*)
Check [1].
Check [X ; Y ; Z ; W].
(*Can also add the empty path and put paths together is that is to be prefered, maybe easier to
access the variables and compare them like that?*)

Inductive event : Type :=
(*| ε  *)
| Event (i : tid) (e : symExprBool) (w : list string) (r : list string).
(*| Path (p1 p2 : symPath).*)

Definition symPath := list event. (*Alternative is to have only a list of events!*)
Notation "i '⟨' e ',' w ',' r '⟩'" := (Event i e w r) (at level 80).
(*Notation "p1 '·' p2" := (Path p1 p2) (at level 80). *)

Check [Event (id 0) (SymBool true) [X ; Y] [X ; Y] ; Event (id 1) (SymBool true) [X ; Y] [X ; Y]]. 
Check [id 0⟨SymBool true, [X;Y], [X;Y]⟩ ; (id 1⟨SymBool true, [X;Y], [X;Y]⟩)].

Open Scope stm_scope.

(*Issue: how to go from SymExprBool to bool - What is true???*)

Reserved Notation "'(||' t ',' sp ',' st '||)' '--[' l ']-->s' '(||' t' ',' sp' ',' st' '||)'"
         (at level 40, st at level 39, t' at level 39). 

Inductive sym_step : tid -> (statement  * symPath * sym_state) ->
                            (statement * symPath * sym_state) -> Prop :=
    | S_Ass : forall st i a l sp,
        (|| i::= a, sp, st ||) --[l]-->s
        (|| SKIP, sp ++ [l⟨SymBool true, [i], vars_arit a⟩], (i !-> sym_aeval st a ; st) ||)

    | S_SeqStep : forall st s1 s1' s2 l sp sp' st',
        (|| s1, sp, st ||) --[l]-->s (|| s1', sp', st' ||) ->
        (|| s1 ;; s2, sp, st ||) --[l]-->s
        (|| s1' ;; s2 , sp', st' ||)

    | S_SeqFinish : forall st s2 l sp,
        (|| SKIP ;; s2, sp, st ||) --[l]-->s
        (|| s2, sp, st ||)

    | S_IfTrue : forall st b s1 s2 l sp,
        (|| If b THEN s1 ELSE s2, sp, st ||) --[l]-->s
        (|| s1, sp ++ [l⟨sym_beval st b, [], vars_bool b⟩], st ||)
        
    | S_IfFalse : forall st b s1 s2 l sp,
        (|| If b THEN s1 ELSE s2, sp, st ||) --[l]-->s
        (|| s2, sp ++  [l⟨SymNot (sym_beval st b), [], vars_bool b⟩], st ||)

    | S_WhileTrue : forall st b s l sp,
        (|| WHILE b DO s END, sp, st ||) --[l]-->s
        (|| WHILE b DO s END, sp ++ [l⟨sym_beval st b, [], vars_bool b⟩], st ||)
        
    | S_WhileFalse : forall st b s l sp,
        (|| WHILE b DO s END, sp, st ||) --[l]-->s
        (|| SKIP, sp ++ [l⟨SymNot (sym_beval st b), [], vars_bool b⟩], st ||)                               

    | S_N0While : forall st b n s l sp,
        n = 0 ->
        (|| WHILE b FOR n DO s END, sp, st ||) --[l]-->s
        (|| SKIP, sp, st ||)
       
    | S_NWhileTrue : forall st b n s l sp,
        (|| WHILE b FOR n DO s END, sp, st ||) --[l]-->s
        (|| WHILE b FOR (n-1) DO s END, sp ++ [l⟨sym_beval st b, [], vars_bool b⟩], st ||)
                     
    | S_NWhileFalse : forall st b n s l sp,
        (|| WHILE b FOR n DO s END, sp, st ||) --[l]-->s
        (|| WHILE b FOR n DO s END, sp ++ [l⟨SymNot (sym_beval st b), [], vars_bool b⟩], st ||)

where " '(||' t ',' sp ',' st '||)' '--[' l ']-->s' '(||' t' ',' sp' ',' st' '||)'" :=
        (sym_step (l) (t,sp,st) (t',sp',st')) . 

(*Example - one event*)
Example sym_step_ex1 :
  (|| X ::= 1, [] , (X !-> x(0)) ||) --[id 0]-->s
  (|| SKIP, [id 0⟨SymBool true, [X], []⟩], (X !-> 1; X !-> x(0))||).
Proof.
  apply S_Ass. Qed.
 
Notation "'(||' t ',' sp ',' st '||)' '--[' l ']-->s*' '(||' t' ',' sp' ',' st' '||)'" :=
   (multi (sym_step (l)) (t,sp, st) (t',sp',st'))
     (at level 40, st at level 39, t' at level 39).

(*We do not care about the truth value of the events in the sympath, this is relevant when conncecting
concrete and symbolic evaluation*)

(*Example - Choosing the false branch*)
Example sym_step_if_false:
  (|| stm_if, [] , (X !-> x(0); Y !-> y(0); Z !-> z(0)) ||) --[id 0]-->s*
  (|| SKIP, [id 0⟨SymBool true, [X], []⟩ ;
             id 0⟨SymNot (1 < 1), [], [X]⟩;
             id 0⟨SymBool true, [Z], []⟩],
   (Z !-> 5; X !-> 1; X !-> x(0); Y !-> y(0); Z !-> z(0)) ||).
Proof.
  unfold stm_if.
  eapply multi_step. apply S_SeqStep. apply S_Ass. simpl.
  eapply multi_step. apply S_SeqFinish.
  eapply multi_step. apply S_IfFalse. simpl. eapply multi_step. apply S_Ass. simpl.
  eapply multi_refl. Qed.

(*Choosing the true branch*)
Check (1 < 1). (*=> symExprBool*)
Example sym_step_if_true:
  (|| stm_if , [],  (X !-> x(0); Y !-> y(0); Z !-> z(0)) ||) --[id 0]-->s*
  (|| SKIP, [id 0⟨SymBool true, [X], []⟩;
             (*next we go on a different branch*)
             id 0⟨(1 < 1), [], [X]⟩;
             id 0⟨SymBool true, [Y], []⟩],
   (Y !-> 3; X !-> 1; X !-> x(0); Y !-> y(0); Z !-> z(0)) ||).

Proof.
  unfold stm_if.
  eapply multi_step. apply S_SeqStep. apply S_Ass. simpl.
  eapply multi_step. apply S_SeqFinish.
  eapply multi_step. apply S_IfTrue. (*choosing the branch*) simpl. eapply multi_step. apply S_Ass. simpl.
  eapply multi_refl. Qed. 

(*symbolic evaluation of threads -> non-deterministc*)
(*OBS: we always reduce to the first thread*)
(*OBS:Where do we create the sym_paths?*)
Reserved Notation "'(|' t ',' sp ',' st '|)' '-->ts' '(|' t' ',' sp' ',' st' '|)'"
         (at level 40, st at level 39, t' at level 39).

Inductive tp_sym_step : (threadPool * symPath * sym_state) -> (threadPool * symPath * sym_state) -> Prop :=
| S_T1 : forall st t1 t1' t2 st' sp sp',
    (| t1, sp, st |) -->ts (| t1', sp', st' |) ->
    (| (TPar t1 t2), sp, st |) -->ts
    (| (TPar t1' t2), sp', st' |)
    
| S_T2 : forall st t1 t2 t2' st' sp sp',
    (| t2, sp, st |) -->ts (| t2', sp', st' |) ->
    (| (TPar t1 t2), sp, st |) -->ts
    (| (TPar t1 t2'), sp', st' |)
   
    | S_ST1 : forall st s1 s1' st' n t2 sp sp', (*maybe i can use l instead of id n*)
        (*We need to initialise sym_paths*)
        (|| s1, sp, st ||) --[id n]-->s (|| s1', sp', st' ||) ->
        (| (TPar << id n | s1 >> t2), sp, st |)  -->ts
        (| (TPar << id n | s1' >> t2), sp', st' |)
        
    | S_ST2 : forall st s2 s2' st' t1 n sp sp',
        (|| s2, sp, st ||) --[id n]-->s (|| s2', sp', st' ||) ->
        (| (TPar t1 << id n | s2 >>), sp, st |)  -->ts
        (| (TPar t1 << id n | s2' >>), sp', st' |)
     
    | S_STDone : forall st n n' sp,
        (| TPar << id n | SKIP >> << id n' | SKIP >>, sp, st |) -->ts
        (| << id n | SKIP >>, sp, st |)                                                       
        
where "'(|' t ',' sp ',' st '|)' '-->ts' '(|' t' ',' sp' ',' st' '|)'" :=
        (tp_sym_step (t, sp, st) (t', sp', st')). 

Notation " '(|' t ',' sp ',' st '|)' '-->ts*' '(|' t' ',' sp' ',' st' '|)'" :=
   (multi tp_sym_step  (t,sp,st) (t',sp',st'))
     (at level 40, st at level 39, t' at level 39).

(*We use the example on the article, generating sym_states and reducing sym_states 
only on the true branches of the conditionals*)
(*We do not have to take the computation untill the end but choose to do so here*)
Example tpsym_article_true_brances :
  (| example_article , [],  (X !-> x(0); Y !-> y(0)) |) -->ts*
  (| << id 1 | SKIP >> ,
               [id 1⟨SymBool true, [X], []⟩;
                id 2⟨(0 = 0), [], [X]⟩;
                id 2⟨SymBool true, [Y], []⟩;
                id 1⟨SymBool true, [X], [Y]⟩],
               (X !-> 0 + 1 ; Y !-> 0 ; X !-> 0 ; X !-> x(0) ; Y !-> y(0)) |).
Proof.
  unfold example_article.
  eapply multi_step. apply S_ST1. apply S_SeqStep. apply S_Ass. simpl.
  eapply multi_step. apply S_ST1. apply S_SeqFinish.

  eapply multi_step. apply S_ST2. apply S_IfTrue. simpl. 
  eapply multi_step. apply S_ST2. apply S_Ass.

  eapply multi_step. apply S_ST1. apply S_Ass. simpl.
  eapply multi_step. eapply S_STDone.
  eapply multi_refl. Qed. 

       
Close Scope symexpr. 
Close Scope stm_scope.                           


End SymEvalStep.
