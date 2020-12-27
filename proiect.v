Require Import String.
Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Strings.String.
Open Scope list_scope.
Require Import List.
Import ListNotations.
Local Open Scope string_scope.

Scheme Equality for string.
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
  
(* Instructiuni adaugate in plus fata de laborator : 
   -switch +~        -xor, xnor, nand nor +   -comentarii +        -do-while +
   -coada +          -break +                 -functii  ~          -referinte +
   -stiva +          -tipuri de variabile +   -variabile locale/globale~ *) 

Inductive Expr1 :=
| anum : nat -> Expr1
| avar : string -> Expr1 
| aplus : Expr1 -> Expr1 -> Expr1
| amul : Expr1 -> Expr1 -> Expr1
| adiv : Expr1 -> Expr1 -> Expr1
| amod : Expr1 -> Expr1 -> Expr1
| aminus : Expr1 -> Expr1 -> Expr1
| btrue : Expr1
| bfalse : Expr1
| berror
| blessthan : Expr1 -> Expr1 -> Expr1
| bgrthan : Expr1 -> Expr1 -> Expr1
| bor : Expr1 -> Expr1 ->Expr1
| bnot : Expr1 -> Expr1
| band : Expr1 -> Expr1 -> Expr1
| bxor : Expr1 -> Expr1 -> Expr1
| bnand: Expr1 -> Expr1 -> Expr1
| bnor: Expr1 -> Expr1 -> Expr1
| nxnor : Expr1 -> Expr1 -> Expr1
.

Coercion anum : nat >-> Expr1.
Coercion avar : string >-> Expr1.
Notation "A +' B" := (aplus A B) (at level 48).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A -' B" := (aminus A B) (at level 48).
Notation "A %' B" := (amod A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 46).

Notation "A <=' B" := (blessthan A B) (at level 53).
Notation "A >=' B" := (bgrthan A B) (at level 53).
Notation "A '\x/' B" := (bxor A B) (at level 53).
Notation "A '\o/' B" := (bor A B) (at level 53).
Notation "A '\n/' B" := (bnor A B) (at level 53).
Notation "A '/a\' B" := (band A B) (at level 53).
Notation "A '/n\' B" := (bnand A B) (at level 53).

Check ( ( 10<='2) /a\ (btrue) ) \o/ ( ( bfalse) \x/ ( 22 >=' 2)) .
(* switch
Inductive case :=
| case1 : nat -> Stmt -> case.
*)
Inductive case:=
| case1: nat->Type-> case.

Inductive Stmt :=
| assignment : string -> Expr1 -> Stmt
| assignment1 : string -> Stmt
| assignmentb : string -> Expr1 -> Stmt
| referinta : string -> string -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : Expr1 -> Stmt -> Stmt
| ifelse : Expr1 -> Stmt -> Stmt -> Stmt
| ifthen : Expr1 -> Stmt -> Stmt
| dowhile : Stmt -> Expr1 -> Stmt
| breakwhile : Expr1 -> Stmt -> string -> Stmt
| breakwhile1 : Expr1 -> Stmt -> string -> Stmt -> Stmt 
| breakif : Expr1 -> string -> Stmt
| breakif1: Expr1 -> Stmt -> string -> Stmt
| comment : string -> Stmt
| apelfct: string -> list string -> Stmt
| switchdef : string -> list Stmt -> Stmt.
Check switchdef.

(*Definition switch1:=(switchdef "var" (4  ("s"::=3) ) ) .*)

Notation " 'if1' '(' A ')'  'then1' B" :=(ifthen A B) (at level 96).
Notation " 'if2' '(' A ')' 'then2' B 'else2' C" := (ifelse A B C)(at level 96).
Notation " 'ifb' '(' A ')' 'thenb' B ':' C " := (breakif A B C)(at level 96).
Notation " 'do1' '{' A '}' 'while1' B " := (dowhile A B) (at level 96).
Notation " X ::= A" :=(assignment X A )(at level 50).
Notation " X ::b= A" :=(assignmentb X A )(at level 50).
Notation " X ::" := (assignment1 X) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 50).
Notation " 'For1' '(' s0 ';' b ';' s1 ')' '{' s2 '}' " :=( s0 ;; while b ( s2;; s1))(at level 96).
Notation " 'do' '{' s1 '}' 'while1' '(' b ')'":= ( s1;; while b s1 ) (at level 96).
Notation " x ::=& y" :=(referinta x y)(at level 49).
Notation " '/*' C '*/' " := (comment C )(at level 96).


Definition switch1:=(switchdef "var"   [ "m"::=8 ; "n"::=9 ] ) .

Check "x"::=& "y".
Check if1 ( btrue ) then1 ("x"::=3). 
Check For1 ( "x"::=13 ; "x" <=' 20 ; "x"::="x"+'1 ) { ("s"::="s"+'4) } .
Check /* "am adaugat un comentariu" */.
Check breakif btrue "break".
Check (
  "j"::=20 ;;
  if2 ( "i" <=' "j")
      then2 ("s"::=18 )
  else2 
      ("s"::=10 ) ;;
  /*"am adaugat un comentariu"*/;;
  "z" ::=& "m";;
  For1 ( "x"::=13 ; "x" <=' 20 ; "x"::="x"+'1 )
     { ("s"::="s"+'4) ;;
       ( breakif ( btrue ) "break" )}
 ).


Definition stiva:= list nat.

Inductive VNat :=
| v_nat : VNat
| num : nat -> VNat.


Inductive VBool :=
| v_bool : VBool
| boolean : bool -> VBool. 

Coercion num: nat >-> VNat.
Coercion boolean: bool >-> VBool.
Check (boolean true).
Check v_bool.
Inductive result :=
| nedecl : result
| neatr : result 
| c_nat : VNat -> result
| c_bool : VBool ->result
| default : result
| code : Stmt-> result.


Inductive lista: Type := 
| nil: lista
| li: result -> lista -> lista.

Check c_nat(2).
Definition Env := string -> result.
Definition env : Env:= fun x => nedecl.

(* stiva*) 
Inductive opstiva:=
| push_nr : nat ->opstiva
| pop : opstiva
| push_var : result -> opstiva.

Check (push_var (c_bool true) ).

(*coada *)
Inductive coada: Type :=
| nil1 : coada
| cd : nat -> coada -> coada
| add : coada -> nat -> coada
| rm : coada.

Check nil1.
Notation " x c> y " := (cd x y ) ( at level 60).
Check ( 2 c> (3 c> (4 c> nil1))). 
Check add (2 c> (3 c> (4 c> nil1))) 4.
Inductive Mem :=
  | mem_default : Mem
  | offset : nat -> Mem.

Scheme Equality for Mem.

(* Environment *)
Definition Env1 := string -> Mem.

(* Memory Layer *)
Definition MemLayer := Mem -> result.

(* Stack *)
Definition Stack := list Env.

(* Configuration *)
Inductive Config :=
  | config : nat -> Env -> MemLayer -> Stack -> Config.

Inductive program :=
| main : Stmt -> program
| decl_fun : string -> list string -> Stmt -> result -> program -> program
| decl_var_glob : string -> result -> program. 


Check  ([ 2 ]).
Notation " 'var_gl' x ':g=' y " := (decl_var_glob x y)(at level 40). 
Check var_gl "x" :g= (c_bool (boolean true)).
Check main ("x"::=10).
Check "n"::=10.

Check decl_fun ("prim") ( ["m" ; "n"] ) ("n"::=10)(c_bool (boolean true))

(main ("x"::=10)).
