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
   -switch++         -xor, xnor, nand nor++     -comentarii ++          
   -break ++         -do-while ++               -expresii lambda ++              
   -stiva ++         -tipuri de variabile ++    -siruri de caractere++    
   
*) 

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

Inductive stiva :=
| nil : stiva 
| cd : nat -> stiva -> stiva .

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

Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Inductive ErrorString :=
| error_string: ErrorString
| string1 : string -> ErrorString.

Coercion num: nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.
Coercion string1 : string >-> ErrorString.

Inductive Pair( S: Type)(T: Type) :=
| pair: S -> T -> Pair S T
| lpair : S -> T -> Pair S T -> Pair S T.
Inductive Strings :=
| null : Strings
| str : string -> Strings.

Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_nat : ErrorNat -> Result
  | res_bool : ErrorBool -> Result
  | res_stiva : stiva ->Result
  | res_string : ErrorString -> Result.

Inductive Stmt :=
| decl_b : string -> Stmt
| decl_n : string -> Stmt
| decl_st : string -> Stmt
| decl_string : string -> Stmt
| assign_n : string -> AExp -> Stmt
| assign_b : string -> BExp -> Stmt
| assign_string : string -> Strings -> Stmt
| push_st : string -> ErrorNat -> Stmt
| pop_st : string -> Stmt
| get_st : string -> Stmt
| empty_st : string -> Stmt
| referinta : string -> string -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifelse : BExp -> Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| dowhile : Stmt -> BExp -> Stmt
| breakwhile : BExp -> Stmt -> string -> Stmt
| while_break_st : BExp -> Stmt -> string -> Stmt -> Stmt 
| comment : string -> Stmt
| apelfct: string -> list string -> Stmt
| switchdef_base : string -> AExp -> Stmt -> Stmt
| switchdef : AExp -> Stmt ->Stmt
| switchtry : string -> Pair AExp Stmt -> Stmt
| strcatd : string -> string -> Stmt
| strcmpd :string -> Result -> Result -> Stmt
| strlenassign : string -> Result -> Stmt
| strcpyd : string -> ErrorString -> Stmt
| lambda : string -> Stmt -> Result -> Stmt.

(*
Inductive stringop :=
| sstring : string -> stringop
| sconc : string -> string -> stringop
| scmp : string -> string -> stringop
| strcpy : string -> string -> stringop.
*)
Notation " 'whileb' '(' B ')' '{' A C D '}'":=(while_break_st B A C D)(at level 96). 
Notation " 'if1' '(' A ')'  'then1' B" :=(ifthen A B) (at level 96).
Notation " 'if2' '(' A ')' 'then2' B 'else2' C" := (ifelse A B C)(at level 96).

Notation " 'do1' '{' A '}' 'while1' B " := (dowhile A B) (at level 96).
Notation " X ::n= A" :=(assign_n X A )(at level 50).
Notation " X ::b= A" :=(assign_b X A )(at level 50).
Notation " 'int1' X " := (decl_n X) (at level 50).
Notation " 'strings1' X " := (decl_string X) (at level 50).
Notation " 'bool1' X " := (decl_b X) (at level 50).
Notation " 'stack' X " := (decl_st X) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 50).
Notation " 'For1' '(' s0 ';' b ';' s1 ')' '{' s2 '}' " :=( s0 ;; while b ( s2;; s1))(at level 96). 
Notation " 'Forb' '(' s0 ';' b ';' s1 ')' '{' s2 '}' " :=( s0 ;; while_break_st b ( s2;; s1))(at level 96). 
Notation " 'do' '{' s1 '}' 'while1' '(' b ')'":= ( s1;; while b s1 ) (at level 96).
Notation " x ::=& y" :=(referinta x y)(at level 49).
Notation " '/*' C '*/' " := (comment C )(at level 96).
Notation " x ::s= 'strlen' y" := (strlenassign x y) (at level 96).


Definition Env := string -> Result.
Definition env : Env := fun x => err_undecl.
Scheme Equality for Result.

(* operatii cu stringuri *)
Fixpoint strlen (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => S (strlen s')
  end.
(*Definition string_dec : forall s1 s2 : string, {s1 = s2} + {s1 <> s2}.*)

Local Open Scope lazy_bool_scope.
Fixpoint strcmp (s1 : string ) (s2 : string) : bool :=
 match s1, s2 with
 | EmptyString, EmptyString => true
 | String c1 s1', String c2 s2' => Ascii.eqb c1 c2 &&& strcmp s1' s2'
 | _,_ => false
 end.
Compute eqb "saluta" "saluta".
Compute strlen "salut".

Reserved Notation "x +=+ y" (right associativity, at level 60).

Fixpoint append (s1 s2 : string) : string :=
  match s1 with
  | EmptyString => s2
  | String c s1' => String c (s1' +=+ s2)
  end
where "s1 +=+ s2" := (append s1 s2) : string_scope.
Compute append "dell" (append "cf" "sal").

(*
Definition switch1:=(switchdef "var"   [ "m"::=8 ; "n"::=9 ] ) .
*)
Check "x"::=& "y".
Check if1 ( btrue ) then1 ("x"::n=3). 
Check For1 ( "x"::n=13 ; "x" <=' 20 ; "x"::n="x"+'1 ) { ("s"::n="s"+'4) } . 
Check /* "am adaugat un comentariu" */.

Check (
  "j"::n=20 ;;
  if2 ( "i" <=' "j")
      then2 ("s"::n=18 )
  else2 
      ("s"::n=10 ) ;;
  /*"am adaugat un comentariu"*/;;
  "z" ::=& "m";;
  For1 ( "x"::n=13 ; "x" <=' 20 ; "x"::n="x"+'1 )
     { ("s"::n="s"+'4) 
      }
 ).

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
| res_stiva _s => match t2 with 
                   | res_stiva _t => true
                   | _=>false
                   end
| res_string _s => match t2 with 
                   | res_string _t => true
                   | _=>false
                   end
end.

Compute (check_eq_over_types (res_nat 1000) (res_nat 100)). 
Compute (check_eq_over_types err_undecl (res_nat 100)). 
Compute (check_eq_over_types (res_nat 100 ) (res_bool true)). 
Compute (check_eq_over_types (res_bool true ) (res_bool false)).

Definition update (env: Env) (x: string) (v:Result) :Env :=
 fun y => 
    if ( eqb y x )
    then   
          (* daca este cu tipul err_undecl => nu a mai fost folosit pana acum si val e diferita default=> nu am declarat-o*)
        if (andb (check_eq_over_types err_undecl (env y)) (negb (check_eq_over_types default v )))
        then err_undecl (* daca este nedeclarat *) 
        else (*daca este nedeclarata si vreau sa o declar*)
        if (andb (check_eq_over_types err_undecl (env y)) (check_eq_over_types default v))
                then v
        else (*daca este declarata, dar neatribuita*)
            if ( andb (check_eq_over_types default (env y)) true)
                                        then v
            else (*daca sunt de acelasi tip*)
            if ( andb (check_eq_over_types (env y) v) true ) then v (* daca sunt acelasi tip*) 
             else err_assign
    else (env y).

Definition env2 : Env := fun x => err_undecl.
Compute (update (update (update env2 "y" (default)) "y" (res_nat 3)) "y" (res_nat 6)) "y".
Compute (update env2 "y" (default)) "y".

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
(*Notation "S [ V /'' X ]" := (update S X V) (at level 0). *)
Reserved Notation "A =[ S ]=> N" (at level 60).
Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive aeval : AExp -> Env -> ErrorNat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=>  match (sigma v) with
                                              | res_nat x => x
                                              | _ => error_nat
                                              end
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (plus_ErrorNat i1 i2) ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mul_ErrorNat i1 i2) ->
    a1 *' a2 =[sigma]=> n
| substract : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (sub_ErrorNat i1 i2) ->
    a1 -' a2 =[sigma]=> n
| division : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (div_ErrorNat  i1 i2) ->
    a1 /' a2 =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mod_ErrorNat i1 i2) ->
    a1 %' a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).



Example ex : 5 -' 10 =[ env ]=> error_nat.
Proof.
eapply substract.
+eapply const.
+eapply const.
+simpl. auto.
Qed.

Example ex2 : 10 /' 0=[ env ]=> error_nat.
Proof.
eapply division.
+eapply const.
+eapply const.
+simpl. auto.
Qed.

Definition lt_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean ( Nat.leb v1 v2) end.
Compute lt_ErrorBool 3 error_nat.

Definition gr_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (negb (Nat.ltb v1 v2) )
    end.

Definition not_ErrorBool (n :ErrorBool) : ErrorBool :=
  match n with
    | error_bool => error_bool
    | boolean v => boolean (negb v)
    end.

Definition and_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.

Definition or_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.
Definition xor_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => match v1, v2 with 
                                | true, true => boolean false
                                | false, false => boolean false
                                | _, _ => boolean true
                                end
    end.
Definition bnand_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean ( negb (andb v1 v2))
    end.
Definition bnor_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean ( negb (orb v1 v2))
    end.
Definition nxnor_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean ( negb (andb v1 v2))
    end.

Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval : BExp -> Env -> ErrorBool -> Prop :=
| b_error: forall sigma, berror  ={ sigma }=> error_bool
| b_true : forall sigma, btrue ={ sigma }=> true
| b_false : forall sigma, bfalse ={ sigma }=> false
| b_var : forall v sigma, bvar v ={ sigma }=>  match (sigma v) with
                                                | res_bool x => x
                                                | _ => error_bool
                                                end
| b_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (lt_ErrorBool i1 i2) ->
    a1 <=' a2 ={ sigma }=> b
|b_grthan : forall a1 a2 i1 i2 sigma b, 
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (gr_ErrorBool i1 i2) ->
    a1 >=' a2 ={ sigma }=> b
| b_not : forall a1 i1 sigma b,
    a1 ={ sigma }=> i1 ->
    b = (not_ErrorBool i1) ->
    bnot a1 ={ sigma }=> b
| b_and : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (and_ErrorBool i1 i2) ->
    (band a1 a2) ={ sigma }=> b 
| b_or : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (or_ErrorBool i1 i2) ->
    (bor a1 a2) ={ sigma }=> b 
| b_xor : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (xor_ErrorBool i1 i2) ->
    (bxor a1 a2) ={ sigma }=> b 
| b_nor : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (bnor_ErrorBool i1 i2) ->
    (bnor a1 a2) ={ sigma }=> b 
| b_nand : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (bnand_ErrorBool i1 i2) ->
    (bnand a1 a2) ={ sigma }=> b 
where "B ={ S }=> B'" := (beval B S B').

(* XOR, OR, NOR, NAND, NXOR*)
Compute xor_ErrorBool true false.
Compute or_ErrorBool true false.
Compute nxnor_ErrorBool (  or_ErrorBool true false) false.
Compute bnand_ErrorBool ( nxnor_ErrorBool (  or_ErrorBool true false) false) true.
Compute and_ErrorBool (bnand_ErrorBool ( nxnor_ErrorBool (  or_ErrorBool true false) false) true) true.
Compute not_ErrorBool (and_ErrorBool (bnand_ErrorBool ( nxnor_ErrorBool (  or_ErrorBool true false) false) true) true).
Example ex5 : 3 <=' 4 ={ env }=> true.
Proof.
eapply b_lessthan.
eapply const.
eapply const.
simpl.
reflexivity.
Qed.
Example exb: 3 <=' ( 9 /' 0) ={ env }=> error_bool.
Proof.
eapply b_lessthan.
+eapply const.
+eapply division.
  ++eapply const. ++eapply const. ++auto. 
+simpl. reflexivity.
Qed.

Example exor : bxor ( 3 <=' 4 ) ( 9<=' 4) ={ env }=>true.
Proof.
 eapply b_xor. eapply b_lessthan. eapply const. eapply const.
auto. eapply b_lessthan. eapply const. eapply const. auto.
simpl. auto.
Qed.
(*OPERATII STIVA*)

 
Definition isEmpty (s : stiva ) : bool :=
  match s with
    | nil => true
    | _     => false
  end.

Definition pop (s : stiva) : stiva :=
  match s with
    | nil => nil 
    | cd _ s' => s'
  end.
Definition get (s : stiva) : nat :=
  match s with
    | nil => 0
    | cd s' _ => s'
  end.
Fixpoint lengthc (s : stiva) : nat :=
  match s with
    | nil => 0
    | cd _ s' => 1 + (lengthc s')
  end.
Check cd 3 nil.
Definition push (s : stiva)(n : nat) : stiva :=
  match s, n with
    | nil , n => (cd n nil)
    | cd s' _ , n => (cd n s)
  end.

Compute push ( cd 2 nil) 4.
Compute lengthc (push ( cd 2 nil) 4).
Check nil.
Check cd 4 (cd 3 nil).
Compute lengthc (cd 9 (cd 4 (cd 3 nil))).
Compute pop (cd 9 (cd 4 (cd 3 nil))).
Compute get(cd 9 (cd 4 (cd 3 nil))).
Notation " x s> y " := (cd x y ) ( at level 60).
Check ( 2 s> (3 s> (4 s> nil))). 
Check push (2 s> (3 s> (4 s> nil))) 4.


Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_nat_decl: forall a sigma sigma',
   sigma' = (update sigma a (default)) ->
   ( int1 a ) -{ sigma }-> sigma'
| e_string_decl : forall a sigma sigma' ,
   sigma' =(update sigma a (default)) ->
  ( strings1 a ) -{ sigma }-> sigma'
| e_comment : forall a sigma , 
    (comment a) -{ sigma }-> sigma
| e_bool_decl: forall a sigma sigma',
   sigma' = (update sigma a (default)) ->
   (bool1 a ) -{ sigma }-> sigma'
| e_strcpy : forall a a1 sigma sigma',
   sigma' = (update sigma a   (res_string a1) ) ->
  ( strcpyd a a1) -{ sigma }-> sigma'
| e_strlen : forall a n sigma sigma',
  sigma' = (update sigma a ( res_nat (strlen n))) ->
  (strlenassign a (res_string n)) -{ sigma }-> sigma'

| e_strcmp : forall a a' b sigma sigma',
  sigma' = (update sigma b ( res_bool (strcmp a a'))) ->
  (strcmpd b (res_string a) (res_string a') ) -{ sigma }-> sigma'

| e_stiva_decl: forall a sigma sigma' sigma'',
   sigma' = (update sigma a (default)) ->
   sigma'' = (update sigma' a (res_stiva nil)) ->
   (decl_st a ) -{ sigma }-> sigma''

| e_stiva_push : forall a n sigma sigma'',
   sigma'' =(update sigma a (res_stiva (push nil n) )) ->
   push_st a n -{ sigma }-> sigma''

| e_stiva_push2 : forall values a n sigma sigma'',
   sigma'' =(update sigma a (res_stiva (push values n) )) ->
   push_st a n -{ sigma }-> sigma''

| e_stiva_pop : forall a values sigma sigma',
   sigma' =(update sigma a (res_stiva ( pop values))) ->
   pop_st a -{ sigma }-> sigma'
| e_nat_assign: forall a i x sigma sigma',
   a =[ sigma ]=> i ->
   sigma' = (update sigma x (res_nat i)) ->
   (x ::n= a) -{ sigma }-> sigma'
| e_bool_assign: forall a i x sigma sigma',
   a ={ sigma }=> i ->
   sigma' = (update sigma x (res_bool i)) ->
   (x ::b= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_if_then : forall b s sigma sigma1,
    b ={ sigma }=> true ->
    s -{ sigma }-> sigma1 ->
    ifthen b s -{ sigma }-> sigma1
| e_if_then_elsetrue : forall b s1 s2 sigma sigma',
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' ->
    ifelse b s1 s2 -{ sigma }-> sigma' 
| e_if_then_elsefalse : forall b s1 s2 sigma sigma',
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma' ->
    ifelse b s1 s2 -{ sigma }-> sigma' 
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
| e_whilebr : forall b s br s2 sigma sigma',
    b ={ sigma }=>true ->
    s -{ sigma }-> sigma' ->
    while_break_st b s br s2 -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').


(*EXPRESII LAMBDA*) 
Inductive lambdaf:=
| lbd : string-> Stmt -> Result -> lambdaf.


Inductive cases:=
| baz: Result -> Stmt -> cases
| lnil.

Definition first(s:cases): Result :=
match s with
| baz a b => a
| lnil => res_nat 0
end.

Definition second(s:cases) : Stmt:=
match s with
| baz a b => b
| lnil => empty_st "err"
end.

Compute first (baz (res_nat 3)("x"::n=4)).
Compute second (baz (res_nat 3)("x"::n=4)).
Definition case2(l : list cases): cases :=
match l with
| [] => lnil
| x :: _ => x
end.
Compute first (case2 [ (baz (res_nat 3) ("x"::n=4) ) ;(baz (res_nat 7) ("x"::n=84) ) ]).

Inductive prglambda :=
| simp: Stmt->prglambda
| lamb: Stmt -> lambdaf -> Stmt -> prglambda
| pr_sw: Stmt -> string -> list cases -> prglambda .
   
Check pr_sw (int1 "x";; ("x"::n=2)) "x" [ (baz (res_nat 3) ("x"::n=4) ) ;(baz (res_nat 3) ("x"::n=4) ) ].
Reserved Notation  "s -+<{ sigma }>+- sigma'"(at level 50).
  Hypothesis eq_dec : forall x y : cases, {x = y}+{x <> y}.

  Fixpoint remove (x : cases) (l : list cases) : list cases :=
    match l with
      | [] => []
      | y::tl => if (eq_dec x y) then remove x tl else y::(remove x tl)
    end.
Definition lista:=[6;4].

Scheme Equality for AExp.
Inductive evlamb : prglambda -> Env -> Env -> Prop :=
| e_simpl : forall s sigma sigma' ,
      eval s sigma sigma' ->
      simp s -+<{ sigma }>+- sigma'
| e_lamb : forall st name st1 res  st2 sigma sigma' sigma'' sigma''' sigma'''' sigma''''', 
      eval st sigma sigma' ->
      eval st1 sigma' sigma'' ->
      sigma'''' = update sigma' "rezultat" default ->
      sigma''''' = update sigma'''' "rezultat" res ->      
      eval st2 sigma' sigma'''->
      lamb st (name st1 res) (st2) -+<{ sigma }>+- sigma'''''
| e_switch_true : forall stm var valoare list_cases val_x b sigma sigma' sigma'',
      eval stm sigma sigma' ->
      valoare = sigma' var ->
      val_x = first (case2 list_cases )->
      b = Result_beq val_x valoare ->
      b = true ->
      eval (second (case2 list_cases )) sigma' sigma'' ->
      pr_sw stm var list_cases -+<{ sigma }>+- sigma''
| e_switch_false : forall stm var valoare list_cases val_x b sigma sigma' list2,
      eval stm sigma sigma' ->
      valoare = sigma' var ->
      val_x = first (case2 list_cases )->
      b = Result_beq val_x valoare ->
      b = false ->
      list2 = remove (case2 list_cases) list_cases ->
      pr_sw stm var list2 -+<{ sigma }>+- sigma
where "s -+<{ sigma }>+- sigma'":= (evlamb s sigma sigma').

Create HintDb my_hints.
Hint Constructors aeval : my_hints.
Hint Constructors beval : my_hints.
Hint Constructors eval : my_hints.
Hint Constructors evlamb : my_hints.

Hint Unfold update : my_hints.
Definition program_switch :=pr_sw (int1 "x";; ("x"::n=2)) "x" [ (baz (res_nat 2) ("x"::n=4) )].
Example ex_sw1: exists state, program_switch -+<{ env }>+- state /\ state "x"=(res_nat 4).
Proof.
eexists. split. unfold program_switch. eapply e_switch_true . eapply e_seq. eapply e_nat_decl. eauto.
eapply e_nat_assign. eapply const. eauto. eauto. eauto. eauto. eauto. eapply e_nat_assign. eapply const.
eauto. simpl. unfold update. eauto. 
Qed.

Definition program_main :=(simp ( int1 "x" ;; ("x"::n=10) ) ).

Example ex_declp1: exists state, program_main -+<{ env }>+- state /\ state "x"=(res_nat 10).
Proof.
eexists. split. eapply e_simpl. eapply e_seq. eapply e_nat_decl. eauto. eapply e_nat_assign.
eapply const. auto. auto.
Qed.
  
Create HintDb my_hints.
Hint Constructors aeval : my_hints.
Hint Constructors beval : my_hints.
Hint Constructors eval : my_hints.
Hint Constructors evlamb : my_hints.
Hint Unfold update : my_hints.

Definition pr_lamb1 :=(lamb 
( 
  int1 "x" ;;
  ("x"::n=10) )  
  (lbd "lambda" 
        (int1 "z") 
        (res_nat 10)) 
  ("z"::n=10)).

Definition pr_lamb :=(lamb 
( 
  int1 "x" ;;
  ("x"::n=10) )  
  (lbd "lambda" 
        (int1 "z") 
        (res_nat 10)) 
  ("z"::n=10)).
Example ex_declp12: exists state, pr_lamb -+<{ env }>+- state /\ state "rezultat"=(res_nat 10).
Proof.
eexists. split. unfold pr_lamb. eapply e_lamb. eapply e_seq. eapply e_nat_decl. eauto. eapply e_nat_assign.
eapply const. auto. eauto 4 with my_hints.
eauto 40 with my_hints. + eauto 50 with my_hints; eauto. + simpl.  eauto 50 with my_hints.
+eauto 50 with my_hints.
Qed.

Example ex_declp13: exists state, pr_lamb -+<{ env }>+- state /\ state "z"=(err_undecl).
Proof.
eexists. split. unfold pr_lamb. eapply e_lamb. eapply e_seq. eapply e_nat_decl. eauto. eapply e_nat_assign.
eapply const. auto. eauto 4 with my_hints.
eauto 40 with my_hints. + eauto 50 with my_hints; eauto. + simpl.  eauto 50 with my_hints.
+eauto 50 with my_hints.
Qed.

(* WHILE BREAK*)
Notation " 'whileb' '(' B ')' '{' A C D '}'":=(while_break_st B A C D)(at level 96). 

Definition ex_decl1 := 
int1 "s";;
strings1 "m";;
("s"::n=0);;
strcpyd "m" (string1 "salut");;
("s" ::s= strlen (res_string "myplg"));;
bool1 "b";;
strcmpd "b" (res_string "veri") (res_string "veri").

Example ex_declp15: exists state, ex_decl1 -{ env }-> state /\ state "b"=(res_bool true).
Proof.
eexists. split. unfold ex_decl1. eapply e_seq. eapply e_nat_decl. auto. eapply e_seq. 
+eapply e_seq. eapply e_seq. eapply e_seq. 
eapply e_string_decl. eauto. eapply e_nat_assign. eauto 3 with my_hints . eauto.
++eapply e_strcpy. auto.
++ eauto 3 with my_hints . +eauto. eapply e_seq. eapply e_bool_decl. auto.
eapply e_strcmp. auto. 
+simpl. eauto.
Qed.

Definition ex_decl := 
int1 "s";;
strings1 "m";;
("s"::n=0);;
strcpyd "m" (string1 "salut").

Example ex_declp: exists state, ex_decl -{ env }-> state /\ state "m"=(res_string "salut").
Proof.
eexists. split. unfold ex_decl. eapply e_seq. eapply e_nat_decl. auto. eapply e_seq. 
+eapply e_seq. eapply e_string_decl. eauto. eapply e_nat_assign. eauto 3 with my_hints . eauto.
+eauto 3 with my_hints . +eauto. 
Qed.

Definition ex_whilebr := 
int1 "i" ;;
int1 "j" ;;
int1 "s";;
strings1 "m";;
("j"::n=1);;
("i"::n=1);; 
("s"::n=0);;
while_break_st ( "i" <=' "j") ("s"::n=18 +' "s") "break" ("i"::n="i"+'1).

Example ex_whilebr1: exists state, ex_whilebr -{ env }-> state /\ state "i"=res_nat 1.
Proof.
eexists. split. unfold ex_whilebr. eapply e_seq. eapply e_nat_decl. auto. eapply e_seq. eapply e_nat_decl. auto.
+eapply e_seq. eapply e_nat_decl. eauto. eapply e_seq. eapply e_seq. eapply e_seq. eapply e_seq. 
++eapply e_string_decl. auto. 
++eapply e_nat_assign. +++eapply const. +++eauto. 
++eapply e_nat_assign. +++eapply const. +++eauto.
++eapply e_nat_assign. +++eapply const. +++eauto.
++eapply e_whilebr. +++eapply b_lessthan. ++++eapply var. ++++eapply var.
 ++++ simpl. reflexivity.
+++ eapply e_nat_assign. eapply add. eapply const. eapply var. auto. eauto.
+eauto. 
Qed.

(* DECLARARE STIVA, STIVA NULA*)
Definition prog:= 
  stack "x";; 
  int1 "y".
Example eval_prog :
  exists state, prog -{ env }-> state /\ state "x" = res_stiva nil .
Proof.
 eexists. split. unfold prog.
 +eapply e_seq. ++eapply e_stiva_decl. auto. eauto.
++eapply e_nat_decl. auto.
+ simpl. eauto.
Qed.


Definition prog2:= 
  stack "x";; 
  int1 "y" ;;
  push_st "x" 3.
Example eval_prog4 :
  exists state, prog2 -{ env }-> state /\ state "x" = res_stiva (cd 3 nil) .
Proof.
 eexists. split. unfold prog2.
 +eapply e_seq. ++eapply e_stiva_decl. auto. auto.
++eapply e_seq. eapply e_nat_decl. auto.
+++ eapply e_stiva_push. +++++eauto.
+eauto.
Qed.

Definition prog23:= 
  stack "x";; 
  int1 "y" ;;
  push_st "x" 3;;
  push_st "x" 4 ;;
  push_st "x" 5 ;;
  pop_st "x".
Example eval_prog4' :
  exists state, prog23 -{ env }-> state /\ state "x" = res_stiva (cd 4 (cd 3 nil)) .
Proof.
 eexists. split. unfold prog2.
 +eapply e_seq. ++eapply e_stiva_decl. auto. auto.
++eapply e_seq. eapply e_seq. eapply e_seq. eapply e_seq. eapply e_nat_decl. auto.
+++ simpl. eauto. eauto. ++++ eauto 3 with my_hints. +++ apply e_stiva_push2 with (push nil 3). eauto. +++apply e_stiva_push2 with (push (cd 3 nil) 4).
 eauto. +++apply e_stiva_pop with (cd 5 (cd 4 (cd 3 nil))). auto.
+eauto.
Qed.


Example eval_prog2 :
  exists state, prog2 -{ env }-> state /\ state "x" =res_stiva ( cd 3 (nil)) .
Proof.
 eexists. split. unfold prog.
 +eapply e_seq. ++eapply e_stiva_decl. auto. auto.
++eapply e_seq. eapply e_nat_decl. auto.
+++ eapply e_stiva_push. simpl. eauto.
+simpl. eauto. 
Qed.

Check prog.

Reserved Notation "s =;{ sigma };= sigma1"(at level 30).

Notation " 'if1' '(' A ')'  'then1' B" :=(ifthen A B) (at level 96).
Notation " 'if2' '(' A ')' 'then2' B 'else2' C" := (ifelse A B C)(at level 96).
Check ( int1 "i").
Definition sum2 :=
  int1 "i" ;;
  int1 "j" ;; 
  if1 ( "i" <=' "j") then1 ("s"::n=18 ).

(*
Inductive aeval_global : program1 -> Env -> Env -> Prop :=
|declarare_variabile : forall a i x sigma sigma',   
   a =[ sigma ]=> i ->
   sigma' = (update sigma x (res_nat i)) ->
   "x" bool =;{ sigma };= sigma'
where "s =;{ sigma };= sigma1" := (aeval_global s sigma sigma1).

Reserved Notation "s -;{ sigma };> sigma1"(at level 30).
*)
(* INSTRUCTIUNEA IF THEN *)
Notation " 'if1' '(' A ')'  'then1' B" :=(ifthen A B) (at level 96).
Definition ex_stmt := 
int1 "i" ;;
int1 "j" ;;
int1 "s";;
("j"::n=1);;
("i"::n=0);; 
if1 ( "i" <=' "j") then1 ("s"::n=18 ).
Example eval_sum4 :
  exists state, ex_stmt -{ env }-> state /\ state "s" =res_nat 18.
Proof.
  eexists. split.
  +unfold ex_stmt. eapply e_seq.
      ++eapply e_nat_decl. eauto. 
      ++eapply e_seq.     
          +++eapply e_nat_decl.   
              ++++eauto.
          +++eapply e_seq. eapply e_seq. 
              ++++eapply e_seq. eapply e_nat_decl. 
                    +++++eauto.
                    +++++eapply e_nat_assign.   
                            +++++++eapply const. +++++++auto.
              ++++eapply e_nat_assign. eapply const. eauto.
              ++++eapply e_if_then.
                    +++++eapply b_lessthan.
                          ++++++eapply var. 
                          ++++++eapply var.
                          ++++++ simpl. reflexivity.
                    +++++eapply e_nat_assign. eapply const. eauto. 
+auto.
Qed.

(*
Inductive aeval_program : final1 -> Env -> Env -> Prop :=
| main_f : forall s sigma1 sigma2,
        s-{ sigma1 }-> sigma2 ->
        (main2 s) -;{ sigma1 };> sigma2  
where "s -;{ sigma };> sigma1" := (aeval_program s sigma sigma1).

*)
(* UPDATE LA ENV*)
Definition ex4:= int1 "x" ;; 
                ("x"::n= 2).
                
Example ex4a: exists state, ex4 -{ env }-> state /\ state "x" =res_nat 2.
Proof.
eexists. split.
unfold ex4. eapply e_seq. eapply e_nat_decl. eauto. eapply e_nat_assign. eapply const.
eauto. eauto.
Qed.

(*EROARE LA DECLARARE *)
Definition ex45:= 
                ("x"::n= 2).
                
Example ex45a: exists state, ex45 -{ env }-> state /\ state "x" =err_undecl.
Proof.
eexists. split.
unfold ex4. eapply e_nat_assign. eapply const.
eauto. eauto. 
Qed.
(*INSTRUCTIUNEA WHILE*)
Definition ex_stmt2 := 
int1 "i" ;;
int1 "j" ;;
int1 "s";;
("j"::n=1);;
("i"::n=0);; 
("s"::n=0);;
while ( "i" <=' "j") (("s"::n=18 +' "s") ;; ("i"::n="i"+'1) ).

Example ex_stm2: exists state, ex_stmt2 -{ env }-> state /\ state "s"=res_nat 36.
Proof.
eexists. split. unfold ex_stmt2. eapply e_seq. eapply e_nat_decl. auto. eapply e_seq. eapply e_nat_decl. auto.
+eapply e_seq. eapply e_seq. eapply e_seq. eapply e_seq. 
++eapply e_nat_decl. auto.
++eapply e_nat_assign. +++eapply const. +++eauto. 
++eapply e_nat_assign. +++eapply const. +++eauto.
++eapply e_nat_assign. +++eapply const. +++eauto.
++eapply e_whiletrue. +++eapply b_lessthan. ++++eapply var. ++++eapply var.
 ++++ simpl. reflexivity.
+++eapply e_seq. eapply e_seq. eapply e_nat_assign. eapply add. eapply const. eapply var. auto. eauto. eapply e_nat_assign. eapply add. eapply var. eapply const.
auto. eauto. eapply e_whiletrue. eapply b_lessthan. eapply var. eapply var. simpl. reflexivity. 
++++eapply e_seq. eapply e_seq. eapply e_nat_assign. eapply add. eapply const. eapply var. auto. eauto. eapply e_nat_assign. eapply add. eapply var. eapply const.
auto. eauto. eapply e_whilefalse. eapply b_lessthan. eapply var. eapply var. simpl. reflexivity. 
+eauto.
Qed.
(*INSTRUCTIUNEA DO WHILE*)
Definition ex_stmt3 := 
int1 "i" ;;
int1 "j" ;;
bool1 "s";;
("j"::n=1);;
("i"::n=1);; 
("s"::b=btrue);;
do { ("s"::b=(bxor btrue bfalse)) ;; /*"comentariu" */ ;; ("i"::n="i"+'1) } while1 ( ( "i" <=' "j") ) .
Example ex_stm23: exists state, ex_stmt3 -{ env }-> state /\ state "s"=res_bool true.
Proof.
eexists. split. unfold ex_stmt3. eapply e_seq. eapply e_nat_decl. auto. eapply e_seq. eapply e_nat_decl. auto.
+eapply e_seq. eapply e_seq. eapply e_seq. eapply e_seq. 
++eapply e_bool_decl. auto.
++eapply e_nat_assign. +++eapply const. +++eauto. 
++eapply e_nat_assign. +++eapply const. +++eauto.
++eapply e_bool_assign. +++eapply b_true. +++eauto.
++eauto. eapply e_seq. eapply e_seq. eapply e_bool_assign. eapply b_xor. eapply b_true. eapply b_false. auto.  eauto. eapply e_seq. eapply e_comment. eapply e_nat_assign. eapply add. eapply var. eapply const. auto.
auto. eapply e_whilefalse. +++eapply b_lessthan. ++++eapply var. ++++eapply var.
 ++++ simpl. reflexivity.
+eauto.
Qed. 

(* INSTRUCTIUNEA FOR *) 
Definition ex_stmt4 := 
int1 "i" ;;
int1 "j" ;;
bool1 "s";;
("j"::n=1);;
("i"::n=1);; 
("s"::b=btrue);;
For1 ( ("i"::n=1) ; ( "i" <=' "j") ;("i"::n="i"+'1) ) { ("s"::b=bfalse ) } .

Example ex_stm234: exists state, ex_stmt4 -{ env }-> state /\ state "s"=res_bool false.
Proof.
eexists. split. unfold ex_stmt4. eapply e_seq. eapply e_nat_decl. auto. eapply e_seq. eapply e_nat_decl. auto.
+eapply e_seq. eapply e_seq. eapply e_seq. eapply e_seq. 
++eapply e_bool_decl. auto.
++eapply e_nat_assign. +++eapply const. +++eauto. 
++eapply e_nat_assign. +++eapply const. +++eauto.
++eapply e_bool_assign. +++eapply b_true. +++eauto.
++eauto. eapply e_seq. eapply e_nat_assign.  eapply const.  auto. eapply e_whiletrue. +++eapply b_lessthan. ++++eapply var. ++++eapply var.
 ++++ simpl. reflexivity. +++ eapply e_seq. eapply e_seq. eapply e_bool_assign. eapply b_false. eauto. eapply e_nat_assign. eapply add. eapply var. eapply const. auto.
auto. eapply e_whilefalse. ++++eapply b_lessthan. +++++eapply var. +++++eapply var.
 +++++ simpl. reflexivity.
+eauto. 
Qed. 


Check (boolean true).


Check "x"::b= btrue.
Check "x"::n=10.


(* Functii incercare  *) 

Inductive program1 :=
| decl_fun1 : string -> list string -> Stmt -> Result -> program1
| decl_var_glob1 : string -> Result -> program1. 

Inductive final1 :=
| main2 : Stmt -> final1
| prgtot : program1 -> final1 -> final1
| prgcomplex : list program1 ->final1 ->final1.



Notation " 'var_gl' x ':g1=' y " := (decl_var_glob1 x y)(at level 40). 
Check var_gl "x" :g1= (res_bool (boolean true)).
Check main2 ("x"::n=10).
Check "n"::n=10.
Check prgtot 
 (decl_fun1 ("prim") ( ["m" ; "n"] )  
      ("n"::n=10) 
       (res_bool (boolean true))) 
(main2 (("x"::n=10);; (apelfct "f" [ "m" ;"n"])) ).

Reserved Notation "S ->{ Sigma }<-> Sigma'" (at level 60).

Inductive eval_program : final1 -> Env -> Env ->Prop :=
| e_main : forall s sigma sigma', 
    eval s sigma sigma' ->
    (main2 s) ->{ sigma }<-> sigma'
    
where "S ->{ Sigma }<-> Sigma'" := (eval_program S Sigma Sigma').

Definition program_main1 :=(main2 ( int1 "x" ;; ("x"::n=10) ) ).

Example ex_sfinal: exists state, program_main1 ->{ env }<-> state /\ state "x"=res_nat 10.
Proof.
eexists. split. eapply e_main. eapply e_seq. eapply e_nat_decl. eauto. eapply e_nat_assign.
eapply const. auto. auto.
Qed.
