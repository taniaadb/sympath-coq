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
Notation "'_' '|->' v" := (t_empty v) (at level 100, right associativity).
Notation "x '|->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition empty_sym_st := (_ |-> SymNat(0)).
Check empty_sym_st. 

(*Classic notation for maps*)
Notation "a '|->' x" := (t_update empty_sym_st a x) (at level 100).
Compute empty_sym_st .
Compute empty_sym_st "x"%string .
Compute (X |-> x(0) + 3 ; X |-> x(0); empty_sym_st) X .
Check ( X !-> 0). (*string -> nat, but it goes through the notation defined here...*)
  
(*symbolic evaluation of arithmetic expressions*)
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
Compute (sym_beval (X |-> x(5)) (3 = X + 5)).

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
Example sym_step_ex1 :
  (|| (X |-> x(0)) , [] ,  X ::= 1 ||) --[id 0]-->s
  (|| (X |-> 1; X |-> x(0)), [id 0⟨SymBool true, [X], []⟩], SKIP ||).
Proof.
  apply S_Ass. Qed.
 
Notation "'(||' st ',' sp ',' t '||)' '--[' l ']-->s*' '(||' st' ',' sp' ',' t' '||)'" :=
   (multi (sym_step (l)) (st,sp, t) (st',sp',t'))
     (at level 40, st at level 39, t' at level 39).

(*We do not care about the truth value of the events in the sympath, this is relevant when conncecting
concrete and symbolic evaluation*)

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
Check (1 < 1). (*=> symExprBool*)
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
  (*OBS:Where do we create the sym_paths?*)

(*Reserved Notation "'(||' st ',' sp ',' t '||)' '--[' l ']-->s' '(||' st' ',' sp' ',' t' '||)'"
  (at level 40, st at level 39, t' at level 39). *)

Reserved Notation "'(|' st ',' sp ',' t '|)' '-->ts' '(|' st' ',' sp' ',' t' '|)'"
         (at level 40, st at level 39, t' at level 39).

Inductive tp_sym_step : (sym_state * symPath * threadPool ) -> (sym_state * symPath * threadPool ) -> Prop :=
     | S_T1 : forall st t1 t1' t2 st' sp sp',
        (| st, sp, t1 |) -->ts (| st', sp', t1' |) ->
        (| st, sp, (TPar t1 t2) |) -->ts
        (| st', sp', (TPar t1' t2) |)
    
    | S_T2 : forall st t1 t2 t2' st' sp sp',
        (| st, sp, t2 |) -->ts (| st', sp', t2' |) ->
        (| st, sp, (TPar t1 t2) |) -->ts
        (| st', sp', (TPar t1 t2') |)
   
    | S_ST1 : forall st s1 s1' st' n t2 sp sp', (*maybe i can use l instead of id n*)
        (*We need to initialise sym_paths*)
        (|| st, sp, s1 ||) --[id n]-->s (|| st', sp', s1' ||) ->
        (| st, sp, (TPar << id n | s1 >> t2) |)  -->ts
        (| st', sp', (TPar << id n | s1' >> t2) |)
        
    | S_ST2 : forall st s2 s2' st' t1 n sp sp',
        (|| st, sp, s2 ||) --[id n]-->s (|| st', sp', s2' ||) ->
        (| st, sp, (TPar t1 << id n | s2 >>) |)  -->ts
        (| st', sp', (TPar t1 << id n | s2' >>) |)
     
    | S_STDone : forall st n n' sp,
        (| st, sp, (TPar << id n | SKIP >> << id n' | SKIP >>) |) -->ts
        (| st, sp,  << id n | SKIP >> |)                                                       
        
where "'(|' st ',' sp ',' t '|)' '-->ts' '(|' st' ',' sp' ',' t' '|)'" :=
        (tp_sym_step (st, sp, t) (st', sp', t')). 

Notation " '(|' st ',' sp ',' t '|)' '-->ts*' '(|' st' ',' sp' ',' t' '|)'" :=
   (multi tp_sym_step  (st,sp,t) (st',sp',t'))
     (at level 40, st at level 39, t' at level 39).

(*We use the example on the article, generating sym_states and reducing sym_states 
only on the true branches of the conditionals*)
(*We do not have to take the computation untill the end but choose to do so here*)
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

(*we show "completeness" on a concrete example, the one in the article*)

Check  (X !-> 1; Y !-> 0 ; X !-> 0). (*does not know we talk about concrete states*)
Check (X |-> x(0) ; Y |-> y(0)).

(*we could have a t' instead of << id 1 | SKIP >>. We might need inversion then*)
(*Yes, we need inversion or induction on the t'*)

(*Theorem exists_symbolic:
    forall st st' t',
    (*there are 2 valuations for which if i reach the end of the eval *)
      (| st , example_article |) -->tc* (| st' , t' |) ->
    exists st_s st_s' sp, 
    (*I can find a symbolic evaluation for them*)  
      (| st_s, [], example_article |) -->ts* (| st_s', sp, t' |).
(*this is pretty independent from the concrete eval*)
Proof.
  (*inversion H usses multi and gives 2 cases, reflexivity and transitivity*)
  unfold example_article. intros. induction t'. (*rewrite -> H3. *) *)
  
Theorem exists_symbolic_finish:
    forall st st',
    (*there are 2 valuations for which if i reach the end of the eval *)
      (| st , example_article |) -->tc* (| st' , << id 1 | SKIP >> |) ->
    exists st_s st_s' sp, 
    (*I can find a symbolic evaluation for them*)  
      (| st_s, [], example_article |) -->ts* (| st_s', sp, << id 1 | SKIP >>|).  
  exists (X |-> x(0) ; Y |-> y(0)).
  exists (X |-> 0 + 1 ; Y |-> 0 ; X |-> 0 ; X |-> x(0) ; Y |-> y(0)).
  (*remember*) exists [id 1⟨SymBool true, [X], []⟩;
                id 2⟨(0 = 0), [], [X]⟩;
                id 2⟨SymBool true, [Y], []⟩;
                id 1⟨SymBool true, [X], [Y]⟩].
  eapply multi_step. apply S_ST1. apply S_SeqStep. apply S_Ass. simpl.
  eapply multi_step. apply S_ST1. apply S_SeqFinish.

  eapply multi_step. apply S_ST2. apply S_IfTrue. simpl. 
  eapply multi_step. apply S_ST2. apply S_Ass.

  eapply multi_step. apply S_ST1. apply S_Ass. simpl.
  eapply multi_step. eapply S_STDone.
  eapply multi_refl. Qed.

(*Completenes??, do we want something specific as the end*)
(*This will be hard to prove, I need someone that knows Coq*)
Theorem completeness:
    forall st st' t t',
    (*there are 2 valuations for which if i reach the end of the eval *)
      (| st , t |) -->tc* (| st' , t' |) ->
    exists st_s st_s' sp, 
    (*I can find a symbolic evaluation for them*)  
      (| st_s, [], t |) -->ts* (| st_s', sp, t' |).
Proof. Admitted.

(*On the other way, from symbolic to concrete*)
(*We need to collect the conditions*)

Check id 1⟨SymBool true, [X], []⟩.
Check (id 0⟨SymBool true, [], []⟩) :: []. 

Fixpoint sym_cond (s: list event) : (list symExprBool) :=
  match s with
| [] => []
| (i⟨e, wr, re⟩) :: t => [e] ++ sym_cond t
  end.

Compute (sym_cond  [id 0⟨SymBool true, [X], []⟩ ;
             id 0⟨SymNot (x(0) < 1), [], [X]⟩;
             id 0⟨SymBool true, [Z], []⟩]).

(*the variables are in symaritt , we have to replace there *)
Compute comp_LNat (x(0)) (x(0)).


Reserved Notation "'[' x '::=' s ']' t" (at level 20).
(*what should the result be*)
(*cannot say for sure it is an aexpr, needs to be symExprArit*)
(*we can make everything symExprArit and use constant folding*)
(*another alternative is to assume that what we want to substitute is going to be there *)

Fixpoint subst (x : SymLNat) (n : nat) (c : symExprArit) : aexpr := (*nat or SymAexpr*)
  match c with
  | SymLNat x' =>
    if comp_LNat x x' then n else c
  | SymNot b => negb (subst x n b)
  | Sy
                       
  | var x' ⇒
      if eqb_string x x' then s else t
  | abs x' T t1 ⇒
      abs x' T (if eqb_string x x' then t1 else ([x:=s] t1))
  | app t1 t2 ⇒
      app ([x:=s] t1) ([x:=s] t2)
  | tru ⇒
      tru
  | fls ⇒
      fls
  | test t1 t2 t3 ⇒
      test ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Close Scope symexpr. 
Close Scope stm_scope.                           


End SymEvalStep.
