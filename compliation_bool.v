Require Import String.
Require Import List.
Import ListNotations.

Definition Var := string.
Open Scope string_scope.

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bvar : string -> BExp
| bor : BExp -> BExp ->BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp.

Fixpoint interpretB (e : BExp) (env : Var -> bool) : bool :=
  match e with
  | btrue => true
  | bfalse => false
  | bvar a => env a
  | bor e1 e2 => orb (interpretB e1 env)  (interpretB e2 env )
  | bnot e1 => negb (interpretB e1 env)
  | band e1 e2 => andb (interpretB e1 env ) (interpretB e2 env)
  end.

Definition env1 := fun x => if string_dec x "n" then true else false.
Check env1.

Compute (interpretB (bor (bnot (bvar "x")) bfalse) env1).

Inductive Instructionb :=
| push_con : bool -> Instructionb
| push_bvar : Var -> Instructionb
| or' : Instructionb
| not' : Instructionb
| and' :Instructionb.

Definition Stackb := list bool.
Fixpoint run_instructionb (i : Instructionb)
         (env : Var -> bool) (stack : Stackb) : Stackb :=
  match i with
  | push_con c => (c :: stack)
  | push_bvar x => ((env x) :: stack)
  | or' => match stack with
           | n1 :: n2 :: stack' => (orb n1  n2) :: stack'
           | _ => stack
           end
  | not' => match stack with
           | n1 :: stack' => (negb n1) :: stack'
           | _ => stack
           end
  | and'  => match stack with
           | n1 :: n2 :: stack' => (andb n1 n2) :: stack'
           | _ => stack
           end
  end.

Compute (run_instructionb (push_con true) env1 []).
Compute (run_instructionb (push_bvar "x") env1 []).
Compute (run_instructionb or' env1 [ true ; false ; true]).
Compute (run_instructionb and' env1 [ false ; true ; true]).

Fixpoint run_instructionsb (is' : list Instructionb)
         (env : Var -> bool) (stack : Stackb) : Stackb :=
  match is' with
  | [] => stack
  | i :: is'' => run_instructionsb is'' env (run_instructionb i env stack)
  end.

Definition pgm1b := [
                    push_con true ;
                    push_bvar "x"
                  ].
Compute run_instructionsb pgm1b env1 [].


Fixpoint compileb (e : BExp) : list Instructionb :=
  match e with
  | btrue => [push_con true]
  | bfalse => [push_con false]
  | bvar x => [push_bvar x]
  | bor e1 e2 => (compileb e1) ++ (compileb e2) ++ [or']
  | band e1 e2 => (compileb e1) ++ (compileb e2) ++ [and']
  | bnot e1 => (compileb e1) ++ [not']
  end.


Compute compileb (btrue).
Compute compileb (band (bvar "x") btrue).
Compute compileb (band (bnot (band btrue (bor btrue bfalse)))(band (bvar "x") btrue)).

Compute interpretB (band (bnot (band btrue (bor btrue bfalse)))(band (bvar "x") btrue)) env1.
Compute run_instructionsb
        (compileb (band (bnot (band btrue (bor btrue bfalse)))(band (bvar "x") btrue)))
        env1
        [].

Lemma orb_comm : forall b1 b2:bool, orb b1 b2 = orb b2 b1.
Proof.
 intros. induction b1. - unfold orb. induction b2. eauto. eauto.
-unfold orb. induction b2. eauto. eauto.
Qed.

Lemma andb_comm : forall b1 b2:bool, andb b1 b2 =andb b2 b1.
Proof.
 intros. induction b1. - unfold andb. induction b2. eauto. eauto.
-unfold orb. induction b2. eauto. eauto.
Qed.

 Lemma soundness_helper :
  forall e env stack is',
    run_instructionsb (compileb e ++ is') env stack =
    run_instructionsb is' env ((interpretB e env) :: stack).

Proof.
  induction e; intros; simpl; trivial.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    eauto. trivial. rewrite orb_comm. reflexivity.
  - rewrite <- app_assoc. induction e.
    rewrite IHe. simpl. eauto. rewrite IHe. simpl. eauto.
    rewrite IHe. simpl. eauto. rewrite IHe. simpl. eauto.
rewrite IHe. simpl. eauto. rewrite IHe. simpl. eauto.
  -rewrite <- app_assoc. rewrite <- app_assoc. 
rewrite IHe1. rewrite IHe2. simpl. rewrite andb_comm. reflexivity. 
Qed.


