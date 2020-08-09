Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List. 
From Coq Require Import Program.Basics. (*for function composition*)
From Coq Require Import Logic.FunctionalExtensionality. (*for equal maos*)
Import ListNotations.
Require Import Maps.

Require Import SyntaxSym.
Require Import CEval. (*always need to compile this if i compile SyntaxSym*)
Import Syntax.
Import CEvalStep.

Module SymEvalStep. 
(*defining the mapping that keeps the symbolic evaluation of variables*)
(*as variables are defines only for arithmetical expressions we use
symExprArit as type*)

Open Scope symexpr.
(*Need to update the notation for the map for the symbolic execution*)
Definition tsym_map (A : Type) := string -> A.
Definition ts_empty {A : Type} (v : A) : tsym_map A :=
  (fun _ => v).
Definition ts_update {A : Type} (m : tsym_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.
(*empty*)
Notation "'_' '|->' v" := (ts_empty v)
                            (at level 100, right associativity).
(*update*)
Notation "x '|->' v ';' m" := (ts_update m x v)
                              (at level 100, v at next level, right associativity).

(*The map we are working with*)
Definition sym_state := tsym_map symExprArit.
Definition empty_sym_st := (_ |-> SymNat(0)).
(*singleton*)
Notation "a '|->' x" := (t_update empty_sym_st a x) (at level 100).

Check (X |-> x 0).
Check (X !-> 1). (*we notice the difference between concrete and symbolic states*)
Compute empty_sym_st .
Compute (X |-> x(0) + 3 ; X |-> x(0); empty_sym_st) X .
  
(*symbolic evaluation of arithmetic expressions*)
(*we need this for conretization function*)
Fixpoint sym_aeval(st : sym_state) (t : aexpr) : symExprArit :=
  match t with
  | ANum n =>
      SymNat n
  | AVar v => st v
  | APlus a1 a2 => (sym_aeval st a1) + (sym_aeval st a2)
  | AMult a1 a2 => (sym_aeval st a1) * (sym_aeval st a2)
  end.

Compute sym_aeval (X |-> x(0) ; Y |-> y(0)) ((X + 1 + Y) * X ).

(*adding constant folding would be nice*)
Compute sym_aeval (X |-> (x(0) + 2 + 3)) X.

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
Compute (sym_beval (X |-> x(5)) (3 = X + 5)).

(*I need to get the conditions!*)
Check [1].
Check [X ; Y ; Z ; W].

Inductive event : Type :=
| Event (i : tid) (e : symExprBool) (w : list string) (r : list string).

Definition symPath := list event.
(*Attempting to bring it closer to the notation in the article*)
Notation "i '⟨' e ',' w ',' r '⟩'" := (Event i e w r) (at level 80).

Check [Event (id 0) (SymBool true) [X ; Y] [X ; Y] ; Event (id 1) (SymBool true) [X ; Y] [X ; Y]]. 
Check [id 0⟨SymBool true, [X;Y], [X;Y]⟩ ; (id 1⟨SymBool true, [X;Y], [X;Y]⟩)].

Open Scope stm_scope.

Reserved Notation "'(||' st ',' sp ',' t '||)' '--[' l ']-->s' '(||' st' ',' sp' ',' t' '||)'"
         (at level 40, st at level 39, t' at level 39). 

Inductive sym_step : tid -> (sym_state  * symPath * statement) ->
                            (sym_state * symPath * statement) -> Prop :=
    | S_Ass : forall st i a l sp,
        (|| st, sp, i ::= a ||) --[l]-->s
        (|| (i |-> sym_aeval st a ; st), sp ++ [l⟨SymBool true, [i], vars_arit a⟩], SKIP ||)

    | S_SeqStep : forall st s1 s1' s2 l sp sp' st',
        (|| st, sp, s1 ||) --[l]-->s (|| st', sp', s1' ||) ->
        (|| st, sp, s1 ;; s2 ||) --[l]-->s
        (|| st', sp', s1' ;; s2 ||)

    | S_SeqFinish : forall st s2 l sp,
        (|| st, sp, SKIP ;; s2 ||) --[l]-->s
        (|| st, sp, s2 ||)

    | S_IfTrue : forall st b s1 s2 l sp,
        (|| st, sp, If b THEN s1 ELSE s2 ||) --[l]-->s
        (|| st, sp ++ [l⟨sym_beval st b, [], vars_bool b⟩], s1 ||)
        
    | S_IfFalse : forall st b s1 s2 l sp,
        (|| st, sp, If b THEN s1 ELSE s2 ||) --[l]-->s
        (|| st, sp ++  [l⟨SymNot (sym_beval st b), [], vars_bool b⟩], s2 ||)

     | S_WhileTrue : forall st b s l sp,
        (|| st, sp, WHILE b DO s END ||) --[l]-->s
        (|| st, sp ++ [l⟨sym_beval st b, [], vars_bool b⟩], WHILE b DO s END ||)
        
    | S_WhileFalse : forall st b s l sp,
        (|| st, sp, WHILE b DO s END ||) --[l]-->s
        (|| st, sp ++ [l⟨SymNot (sym_beval st b), [], vars_bool b⟩],  SKIP ||)                               

    | S_N0While : forall st b n s l sp,
        n = 0 ->
        (|| st, sp, WHILE b FOR n DO s END ||) --[l]-->s
        (|| st, sp,  SKIP ||)
       
    | S_NWhileTrue : forall st b n s l sp,
        (|| st, sp, WHILE b FOR n DO s END ||) --[l]-->s
        (|| st, sp ++ [l⟨sym_beval st b, [], vars_bool b⟩], WHILE b FOR (n-1) DO s END ||)
                     
    | S_NWhileFalse : forall st b n s l sp,
        (|| st, sp, WHILE b FOR n DO s END ||) --[l]-->s
        (|| st, sp ++ [l⟨SymNot (sym_beval st b), [], vars_bool b⟩], WHILE b FOR n DO s END ||)

where " '(||' st ',' sp ',' t '||)' '--[' l ']-->s' '(||' st' ',' sp' ',' t' '||)'" :=
        (sym_step (l) (st,sp,t) (st',sp',t')) . 

(*Example - one event*)
(*We use a syntetic id in order to make this work as our evaluation is based on threads*)
Example sym_step_ex1 :
  (|| (X |-> x(0)) , [] ,  X ::= 1 ||) --[id 0]-->s
  (|| (X |-> 1; X |-> x(0)), [id 0⟨SymBool true, [X], []⟩], SKIP ||).
Proof.
  apply S_Ass. Qed.
 
Notation "'(||' st ',' sp ',' t '||)' '--[' l ']-->s*' '(||' st' ',' sp' ',' t' '||)'" :=
   (multi (sym_step (l)) (st,sp, t) (st',sp',t'))
     (at level 40, st at level 39, t' at level 39).


(*Example - Choosing the false branch*)
Example sym_step_if_false:
  (|| (X |-> x(0); Y |-> y(0); Z |-> z(0)), [] ,stm_if ||) --[id 0]-->s*
  (|| (Z |-> 5; X |-> 1; X |-> x(0); Y |-> y(0); Z |-> z(0)),
             [id 0⟨SymBool true, [X], []⟩ ;
             id 0⟨SymNot (1 < 1), [], [X]⟩;
             id 0⟨SymBool true, [Z], []⟩], SKIP ||).
Proof.
  unfold stm_if.
  eapply multi_step. apply S_SeqStep. apply S_Ass. simpl.
  eapply multi_step. apply S_SeqFinish.
  eapply multi_step. apply S_IfFalse. simpl. eapply multi_step. apply S_Ass. simpl.
  eapply multi_refl. Qed.

(*Choosing the true branch*)
Example sym_step_if_true:
  (|| (X |-> x(0); Y |-> y(0); Z |-> z(0)), [],  stm_if ||) --[id 0]-->s*
  (|| (Y |-> 3; X |-> 1; X |-> x(0); Y |-> y(0); Z |-> z(0)),
             [id 0⟨SymBool true, [X], []⟩;
             (*next we go on a different branch*)
             id 0⟨(1 < 1), [], [X]⟩;
             id 0⟨SymBool true, [Y], []⟩], SKIP ||).
Proof.
  unfold stm_if.
  eapply multi_step. apply S_SeqStep. apply S_Ass. simpl.
  eapply multi_step. apply S_SeqFinish.
  eapply multi_step. apply S_IfTrue. (*choosing the branch*) simpl. eapply multi_step. apply S_Ass. simpl.
  eapply multi_refl. Qed. 

(*symbolic evaluation of threads -> non-deterministc*)
(*OBS: we always reduce to the first thread*)

(*Reserved Notation "'(||' st ',' sp ',' t '||)' '--[' l ']-->s' '(||' st' ',' sp' ',' t' '||)'"
  (at level 40, st at level 39, t' at level 39). *)

Reserved Notation "'(|' st ',' sp ',' t '|)' '-->ts' '(|' st' ',' sp' ',' t' '|)'"
         (at level 40, st at level 39, t' at level 39).

Inductive tp_sym_step : (sym_state * symPath * threadPool ) -> (sym_state * symPath * threadPool ) -> Prop :=
(*new rule that we require -> what happens when we only have 1 thread?*)
    | S_T0 : forall st st' l stm stm' sp sp',
        (|| st, sp, stm ||) --[l]-->s (|| st', sp', stm' ||) ->
        (| st, sp, << l | stm >> |) -->ts (| st', sp', << l | stm' >> |)

    | S_T1 : forall st t1 t1' t2 st' sp sp',
        (| st, sp, t1 |) -->ts (| st', sp', t1' |) ->
        (| st, sp, (TPar t1 t2) |) -->ts
        (| st', sp', (TPar t1' t2) |)
    
    | S_T2 : forall st t1 t2 t2' st' sp sp',
        (| st, sp, t2 |) -->ts (| st', sp', t2' |) ->
        (| st, sp, (TPar t1 t2) |) -->ts
        (| st', sp', (TPar t1 t2') |)
   
    | S_ST1 : forall st s1 s1' st' l t2 sp sp',
        (*We need to initialise sym_paths*)
        (|| st, sp, s1 ||) --[l]-->s (|| st', sp', s1' ||) ->
        (| st, sp, (TPar << l | s1 >> t2) |)  -->ts
        (| st', sp', (TPar << l | s1' >> t2) |)
        
    | S_ST2 : forall st s2 s2' st' t1 l sp sp',
        (|| st, sp, s2 ||) --[l]-->s (|| st', sp', s2' ||) ->
        (| st, sp, (TPar t1 << l | s2 >>) |)  -->ts
        (| st', sp', (TPar t1 << l | s2' >>) |)
     
    | S_STDone : forall st l l' sp,
        (| st, sp, (TPar << l | SKIP >> << l' | SKIP >>) |) -->ts
        (| st, sp,  << l | SKIP >> |)                                                       
        
where "'(|' st ',' sp ',' t '|)' '-->ts' '(|' st' ',' sp' ',' t' '|)'" :=
        (tp_sym_step (st, sp, t) (st', sp', t')). 

Notation " '(|' st ',' sp ',' t '|)' '-->ts*' '(|' st' ',' sp' ',' t' '|)'" :=
   (multi tp_sym_step  (st,sp,t) (st',sp',t'))
     (at level 40, st at level 39, t' at level 39).

(*We use the example on the article, generating sym_states and reducing sym_states 
only on the true branches of the conditionals*)
Example tpsym_article_true_brances :
  (| (X |-> x(0); Y |-> y(0)), [], example_article |) -->ts*
  (| (X |-> 0 + 1 ; Y |-> 0 ; X |-> 0 ; X |-> x(0) ; Y |-> y(0)),
               [id 1⟨SymBool true, [X], []⟩;
                id 2⟨(0 = 0), [], [X]⟩;
                id 2⟨SymBool true, [Y], []⟩;
                id 1⟨SymBool true, [X], [Y]⟩], << id 1 | SKIP >>|).
Proof.
  unfold example_article.
  eapply multi_step. apply S_ST1. apply S_SeqStep. apply S_Ass. simpl.
  eapply multi_step. apply S_ST1. apply S_SeqFinish.

  eapply multi_step. apply S_ST2. apply S_IfTrue. simpl. 
  eapply multi_step. apply S_ST2. apply S_Ass.

  eapply multi_step. apply S_ST1. apply S_Ass. simpl.
  eapply multi_step. eapply S_STDone.
  eapply multi_refl. Qed. 

(*Trying to combine symbolic with concrete evaluation*)
(*We need to collect the conditions*)

Fixpoint sym_cond (s: list event) : (list symExprBool) :=
  match s with
| [] => []
| (i⟨e, wr, re⟩) :: t => [e] ++ sym_cond t
  end.

Compute (sym_cond  [id 0⟨SymBool true, [X], []⟩ ;
             id 0⟨SymNot (x(0) < 1), [], [X]⟩;
             id 0⟨SymBool true, [Z], []⟩]).

(*Creating the map for the conretization*)
Definition total_subst_map (A : Type) := symExprArit -> A.
Definition s_empty {A : Type} (v : A) : total_subst_map A :=
  (fun _ => v).
Definition s_update {A : Type} (m : total_subst_map A)
                    (x : symExprArit) (v : A) :=
  fun x' => if comp_symExprArit x x' then v else m x'.
Notation "'_' '||->' v" := (s_empty v)
                             (at level 100, right associativity).
Notation "x '||->' v ';' m" := (s_update m x v)
                              (at level 100, v at next level, right associativity).

Definition subst_state := total_subst_map aexpr. 
(*Our map*)
Definition empty_subst_st := (_ ||-> ANum 0). (*the same as for state!*)
Notation "a '||->' x" := (s_update empty_subst_st a x) (at level 100).

(*Checking if the program recognizes the difference between the 3 maps*)
Check (X |-> x 0). (*string -> symExprArit*)
Check (X !-> 1). (*string -> nat*)
Check ((x 0) ||-> 1; y 0 + 2 ||-> X).

(*Evaluate expressions with a subst state*)
Fixpoint subst_symExprArit (s : subst_state) (a : symExprArit) : aexpr :=
  match a with 
  | SymLNat x' => s x'
  | SymNat n => n
  | SymPlus a1 a2 => (subst_symExprArit s a1) + (subst_symExprArit s a2)
  | SymMult a1 a2 => (subst_symExprArit s a1) * (subst_symExprArit s a2)
  end.

Definition init_state := (x 0 ||-> 1; y 0 ||-> 2).
Print init_state.
Check (x 0 + 1 + y 0).
Compute subst_symExprArit init_state (x 0 + 1 * y 0). (*WORKS, but it could have constant folding!*)
(*Checks for boolean functions*)
Compute (negb true).
Compute (andb true false).
Compute (eqb 1 2).
Compute (leb 2 1).

(*should i maybe have a separate function for bool vs list bool *)
(*Fixpoint subst_symExprBool (s : subst_state) (b : symExprBool)  : bool :=
  match b with
  | SymBool b' => b'
  | SymNot b' => negb (subst_symExprBool s b')
  | SymAnd b1 b2 => andb (subst_symExprBool s b1) (subst_symExprBool s b2)
  | SymEq a1 a2 => (subst_symExprArit s a1) =? (subst_symExprArit s a2)
  | SymLessThan a1 a2 => (subst_symExprArit s a1) <? (subst_symExprArit s a2)
  end.

Check (x 0 + 1 = y 0).
Compute subst_symExprBool (x 0 + 1 = y 0) init_state.  


Fixpoint subst_sym_cond (c : list symExprBool) (s : subst_state) : list bool :=
  match c with 
  | [] => []
  | e :: t => subst_symExprBool e s :: subst_sym_cond t s
  end.

Definition ex_path := [SymBool true; SymNot (x 0 < 5); (y 0 = x 0)].
Check ex_path.
Compute subst_sym_cond ex_path (x 0 ||-> 1 ; y 0 ||-> 1).
Example cond_ex :
  subst_sym_cond ex_path (x 0 ||-> 1 ; y 0 ||-> 1) = [true; false; true]. 
Proof.     
  simpl. reflexivity. Qed.

(*can use count occurances, find, existsb -> only figgured out existsb/forallb*)
Print forallb.
Compute forallb (andb true) [false; true].
Example cond_false :
  forallb (andb true) (subst_sym_cond ex_path (x 0 ||-> 1 ; y 0 ||-> 1)) = false.
Proof. simpl. reflexivity. Qed.
Example cond_true :
  forallb (andb true) (subst_sym_cond ex_path (x 0 ||-> 7 ; y 0 ||-> 7)) = true.
Proof. simpl. reflexivity. Qed.
 *)

(*Testing built-in function composition*)
Compute (compose (x 0 ||-> 1) (X |-> x 0 )) X .
Check (compose (x 0 ||-> 1) (X |-> x 0 )). (*string -> aexpr*)

(*Function for concretization that helps us connect states and sym_states*)
Inductive concretization : subst_state -> sym_state -> state -> Prop :=
| Con_empty : forall sub,
    concretization sub empty_sym_st empty_st
| Con_update : forall sub sym_st st X sym_X n,
    concretization sub sym_st st ->
    aeval st (subst_symExprArit sub sym_X) = n ->
    concretization sub (X |-> sym_X; sym_st) (X !-> n; st). 

(*Examples of how concretization works*)
Example conc_1:
  concretization (x 0 ||-> 1) empty_sym_st empty_st.
Proof. apply Con_empty. Qed.

Example conc_2:
  concretization (x 0 ||-> 1) (X |-> x 0 + 1) (X !-> 2).
(*need to prove the conditions that makes this true, we have 2 conditions*)
Proof. apply Con_update. apply Con_empty. simpl. reflexivity. Qed.

Example conc_3:
  ~ concretization (x 0 ||-> 1) (X |-> x 0 + 1) (X !-> 3).
Proof.
  (*this would be easy to show with a partial function, more difficult here as 
the empty state always contains something*)
  (*Here we have not defined what it means that 2 maps are different!*)
  intuition. (*unfold not. intros. *) inversion H.  
  assert (~ empty_st = (X !-> 3)).
  - unfold not.  unfold t_update. unfold empty_st. unfold t_empty.
(*cannot do anything else from here*) Abort.

(*I can add the definition that I need but with no proof*)

Theorem equiv_subst: forall st f st_s a,
    aeval st (subst_symExprArit f (sym_aeval st_s a)) = aeval st a.
Proof. Admitted.  (*if admitted then i can use it for other things *)
 (* (*induction on a *) 
  intros. induction a; 
  try reflexivity;
  try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  - simpl. (*could the problem be that it does not kno (st_s s) is an LNat?*)
    assert (subst_symExprArit f (st_s s) = s).  Abort.  *)
  (*I think this is the issue, the program cannot figure out that it is an LNat*)
  (*the problem could come because our concretization is not explicit enough*)
 (* Var 2
  intros. assert (subst_symExprArit f (sym_aeval st_s a) = a). 
  - induction a;
    try reflexivity;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity). *)
  
  
(*Proof of competeness for the -->c relation*)
Theorem complete:
    forall st st' stm l f st_s sp,
    (*there are 2 valuations for which if i reach the end of the eval *)
      (|| st , stm ||) -->c (|| st' , SKIP ||) 
      /\ concretization f st_s st ->
    exists st_s' sp', 
    (*I can find a symbolic evaluation for them*)  
      (|| st_s, sp, stm ||) --[l]-->s (|| st_s', sp', SKIP ||)
      /\ concretization f st_s' st'.  
Proof.
  intros. inversion H. inversion H0; subst.
  (*assignment -> CS_Ass*) 
  - exists (i |-> sym_aeval st_s a; st_s).
    exists (sp ++ [l⟨SymBool true, [i], vars_arit a⟩]).
    split.
    + constructor. 
    + apply Con_update. assumption. simpl.
      apply equiv_subst.  (*we need equiv_subst here*)
  (*CS_SeqFinish*)
  - exists st_s. exists sp.
    split.
    + constructor.
    + assumption.
  (*CS_IfTrue*)
  - exists st_s. exists (sp ++ [l⟨sym_beval st_s b, [], vars_bool b⟩]).
    split.
    + constructor.
    + assumption.
  (*CS_IfFalse*)
  - exists st_s. exists (sp ++ [l⟨SymNot (sym_beval st_s b), [], vars_bool b⟩]).
    split.
    + constructor.
    + assumption.
  (*CS_N0While*)
  - exists st_s. exists sp.
    split.
    + constructor. reflexivity.
    + assumption. 
Qed. 

(*Proof of completeness for -->tc *)
Theorem complete2:
    forall st st' f st_s sp TP TP', 
    (*there are 2 valuations for which if i reach the end of the eval *)
      (| st , TP |) -->tc (| st' , TP' |) 
      /\ concretization f st_s st ->
    exists st_s' sp', 
    (*I can find a symbolic evaluation for them*)  
      (| st_s, sp, TP |) -->ts (| st_s', sp', TP'|) 
      /\ concretization f st_s' st'.
Proof.
  (*intros. inversion H. induction TP.
  - inversion H0. subst. apply *)

(*Theorem exists_concrete_finish:
    forall st_s sp,
    (*there are 2 valuations for which if i reach the end of the eval *)
      (| (X |-> x 0; Y |-> y 0), [], example_article |) -->ts* (| st_s, sp,  << id 1 | SKIP >> |) ->
    exists st_init st', 
    (*I can find a symbolic evaluation for them*)  
      (| compose st_init (X |-> x 0; Y |-> y 0), example_article |) -->tc* (| st', << id 1 | SKIP >>|).
Proof. *)
  

Close Scope symexpr. 
Close Scope stm_scope.                           


End SymEvalStep.
