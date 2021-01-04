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

Inductive AExp :=
| anum : nat -> AExp
| avar : string -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp
| asub : AExp -> AExp -> AExp.

Coercion anum : nat >-> AExp.
Coercion avar : string >-> AExp.
Notation "A +' B" := (aplus A B) (at level 48).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A -' B" := (asub A B) (at level 48).
Notation "A %' B" := (amod A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 46).
Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| berror
| blessthan : AExp -> AExp -> BExp
| bvar : string -> BExp
| bgrthan : AExp -> AExp -> BExp
| bor : BExp -> BExp ->BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bxor : BExp -> BExp -> BExp
| bnand: BExp -> BExp -> BExp
| bnor: BExp -> BExp -> BExp.

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
| assignment : string -> AExp -> Stmt
| assignment1 : string -> Stmt
| assignmentb : string -> BExp -> Stmt
| referinta : string -> string -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifelse : BExp -> Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| dowhile : Stmt -> BExp -> Stmt
| breakwhile : BExp -> Stmt -> string -> Stmt
| breakwhile1 : BExp -> Stmt -> string -> Stmt -> Stmt 
| breakif : BExp -> string -> Stmt
| breakif1: BExp -> Stmt -> string -> Stmt
| comment : string -> Stmt
| apelfct: string -> list string -> Stmt
| switchdef : string -> list Stmt -> Stmt.
Check switchdef.
Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Coercion num: nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.

Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_nat : ErrorNat -> Result
  | res_bool : ErrorBool -> Result.

Scheme Equality for Result.
Definition Env := string -> Result.

(* Initial environment *)
Definition env : Env := fun x => err_undecl.
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


(*
Definition switch1:=(switchdef "var"   [ "m"::=8 ; "n"::=9 ] ) .
*)
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

Check (boolean true).


Inductive lista: Type := 
| nil: lista
| li: Result -> lista -> lista.


(* stiva*) 
Inductive opstiva:=
| push_nr : nat ->opstiva
| pop : opstiva
| push_var : Result -> opstiva.

Check (push_var (res_bool (boolean true)) ).

(*coada *)
Inductive coada: Type :=
| nil1 : coada
| cd : nat -> coada -> coada
| addc : coada -> nat -> coada
| rm : coada.

Check nil1.
Notation " x c> y " := (cd x y ) ( at level 60).
Check ( 2 c> (3 c> (4 c> nil1))). 
Check addc (2 c> (3 c> (4 c> nil1))) 4.
Inductive Mem :=
  | mem_default : Mem
  | offset : nat -> Mem.

Scheme Equality for Mem.

(* Environment *)
Definition Env1 := string -> Mem.

(* Memory Layer *)
Definition MemLayer := Mem -> Result.

(* Stack *)
Definition Stack := list Env.

(* Configuration *)
Inductive Config :=
  | config : nat -> Env -> MemLayer -> Stack -> Config.


(* operatii cu stringuri *)
Inductive stringop :=
| sstring : string -> stringop
| sconc : string -> string -> stringop
| scmp : string -> string -> stringop
| strcpy : string -> string -> stringop.
Fixpoint length (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => S (length s')
  end.
Compute length "salut".
Check "x"::b= btrue.
Check "x"::=10.



(*semantica*)

Definition check_eq_over_types (t1 : Result)(t2 : Result) : bool :=
  match t1 with
  | err_assign => match t2 with 
                   | err_assign => true
                   | _ => false
                   end
  | err_undecl => match t2 with 
                   | err_undecl => true
                   | _ => false
                   end
| res_nat _x => match t2 with 
                   | res_nat _y=> true
                   | _ => false
                   end
| res_bool _b => match t2 with 
                   | res_bool _c => true
                   | _ => false
                   end
| default => match t2 with 
                   | default => true
                   | _ => false
                   end

end.

Compute (check_eq_over_types (res_nat 1000) (res_nat 100)). (* true *)
Compute (check_eq_over_types err_undecl (res_nat 100)). (* false *)

Definition update (env: Env) (x: string) (v:Result) :Env :=
 fun y => 
    if ( eqb y x )
    then   
      if( andb (check_eq_over_types err_undecl (env y)) (negb (check_eq_over_types default v)))
      then err_undecl
      else
        if (andb (check_eq_over_types err_undecl (env y)) (check_eq_over_types v (env y)) )
        then v
        else err_undecl
    else (env y).
Definition env2 : Env := fun x => err_undecl.
Compute (update (update env2 "y" (default))).
Definition Env3 := string -> Mem.
Definition env4 : Env3 := fun x => mem_default.
Definition update_env (env: Env3) (x: string) (n: Mem) : Env3 :=
  fun y =>
      (* If the variable has assigned a default memory zone, 
         then it will be updated with the current memory offset *)
      if (andb (string_beq x y ) (Mem_beq (env4 y) mem_default))
      then
        n
      else
        (env y).

Compute( update_env env4  "x"  mem_default).
Compute( update_env env4  "x" (offset 5) ).
Compute ( update_env env4  "x" (offset 5)) "x".
Compute (env4 "z"). 


Definition update_mem (mem :MemLayer) (env4 :Env3) (x: string) (type : Mem) (v:Result) : MemLayer:=
 fun y =>
    if (andb (Mem_beq y type) (Mem_beq (env4 x) type))
    then 
        if(andb (check_eq_over_types err_undecl (mem y)) (check_eq_over_types default v))
        then default
        else
            if(orb (check_eq_over_types default (mem y)) (check_eq_over_types v (mem y)))
            then v
            else err_undecl
    else (mem y).

Definition mem : MemLayer := fun x => err_undecl.
Compute (update_mem mem env4 "sal" (offset 20) (res_nat (num 10))).
Compute update_mem mem env4 "sal" mem_default default.


Definition plus_ErrorNat (n1 n2 :ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 + v2)
    end.

Definition sub_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num n1, num n2 => if Nat.ltb n1 n2
                        then error_nat
                        else num (n1 - n2)
    end.

Definition mul_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 * v2)
    end.

Definition div_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (Nat.div v1 v2)
    end.

Definition mod_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (v1 - v2 * (Nat.div v1 v2))
    end.
Fixpoint aeval_fun (a : AExp) (env : Env) : ErrorNat :=
  match a with
  | avar v => match (env v) with
                | res_nat n => n
                | _ => error_nat
                end
  | anum v => v
  | aplus a1 a2 => (plus_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | amul a1 a2 => (mul_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | asub a1 a2 => (sub_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | adiv a1 a2 => (div_ErrorNat  (aeval_fun a1 env) (aeval_fun a2 env))
  | amod a1 a2 => (mod_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  end.
