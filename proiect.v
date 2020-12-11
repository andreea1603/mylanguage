Require Import String.
Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Strings.String.
Open Scope list_scope.
Require Setoid.
Require Import PeanoNat Le Gt Minus Bool Lt.
Local Open Scope string_scope.
Scheme Equality for string.
Require Import Logic.FunctionalExtensionality.
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Inductive AExp :=
| anum : nat -> AExp
| avar : string -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp.

Coercion anum : nat >-> AExp.
Coercion avar : string >-> AExp.

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| bgrthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp.

Inductive Stmt :=
| assignment : string -> AExp -> Stmt
| assignment1 : string -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifelse : BExp -> Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| for' :  Stmt -> BExp -> Stmt -> Stmt -> Stmt.

Definition lista:=nat->nat.

Definition total_map := string -> nat.

Definition l_empty (v:nat) : lista :=
  (fun _=> v).

Section Lists.

Inductive stiva: Type :=
| nil: stiva
| st: nat -> stiva -> stiva.

Check nil.
Check (st 1 (st 2 (st 3 nil))).

Notation "x --> y" := (st x y) (at level 60).
Check ( 2 --> (3 --> (4 --> nil))) .

Inductive coada: Type :=
| nil1 : coada
| cd : nat -> coada -> coada.

Check nil1.
Check (cd 2 (cd 3( cd 4 nil1))).
Notation " x +> y " := (cd x y ) ( at level 60).

Check ( 2 +> (3 +> (4 +> nil1))). 


