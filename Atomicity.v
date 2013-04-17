 Require Import Coq.Arith.EqNat.
 Require Import Coq.Arith.Le.
 Require Import Coq.Arith.Lt.
 Require Import Coq.MSets.MSetList.
 Require Import Coq.FSets.FMapList.
 Require Import Coq.Strings.String.
 Require Import Coq.Logic.Decidable.
 Require Import Omega.
 Require Import SfLib.

Inductive conflict : Type :=
  | None : conflict
  | Race : conflict.

(* Inductive id : Type :=
  | Id : nat -> id. *)

Definition id_eq (a : id) (b : id) := match a, b with
| Id a, Id b => beq_nat a b
end.

Eval simpl in id_eq (Id 5) (Id 6).
Eval simpl in id_eq (Id 5) (Id 5).

Inductive value : Type :=
  | VConst   : nat -> value
  | VSyncLoc : nat -> value
  | VFunction: nat -> list id -> value.

Inductive exp : Type :=
  | EValue : value -> exp
  | EId    : id -> conflict -> exp
  | EAssgn : id -> conflict -> exp -> exp
  | ESeq   : exp -> exp -> exp
  | EPrim  : (list value -> value) -> list exp -> exp
  | ECall  : exp -> list exp -> list exp -> exp
  | EIf    : exp -> exp -> exp -> exp
  | EWhile : exp -> exp -> exp
  | ELet   : id -> exp -> exp -> exp
  | EFork  : exp -> exp
  | EAtomic: exp -> exp
  | EInAtomic : exp -> exp.

Notation "x '%' b '::=' n" := (EAssgn x b n) (at level 60).
Notation "a ';' b" := (ESeq a b) (at level 60).
Notation "'IFE' x 'THEN' a 'ELSE' b" := (EIf x a b) (at level 60).
Notation "'WHILE' a 'DO' b" := (EWhile a b) (at level 60).
Notation "'LET' a '::=' b 'IN' c" := (ELet a b c) (at level 60).
Notation "'FORK' a" := (EFork a) (at level 60).

Definition i := (Id 5).
Definition a := (EId i None).
Definition b := IFE a 
                THEN LET i ::= a IN (i % (None) ::= (EValue (VConst 6)) )
                ELSE WHILE a DO a.
Print b.

Definition heap_state := id -> nat.
Definition sync_state := id -> nat.

Definition empty_heap : heap_state :=
  fun _ => 0.

Definition empty_sync : heap_state :=
  fun _ => 0.

Definition update_heap (st : heap_state) (X:id) (n : nat) : heap_state :=
  fun X' => if beq_id X X' then n else st X'.

Definition update_sync (st : sync_state) (X:id) (n : nat) : sync_state :=
  fun X' => if beq_id X X' then n else st X'.

Inductive thread : Type :=
  | TExpr : exp -> thread
  | Wrong : thread.

Inductive step : heap_state -> sync_state -> list thread -> Prop :=
  | SWhile : forall (e1 e2 : exp) (heap : heap_state) (sync : sync_state) (t t' : list thread), 
              step heap sync (t ++ (TExpr (WHILE e1 DO e2))::t') ->
              step heap sync (t ++ (TExpr (IFE e1 THEN e2; (WHILE e1 DO e2)  ELSE (EValue (VConst 0))))::t')
  | SIf    : forall (e1 e2 : exp) heap sync t t' v,
             v <> (VConst 0) -> 
             step heap sync (t ++ (TExpr (IFE (EValue v) THEN e1 ELSE e2))::t') ->
             step heap sync (t ++ (TExpr e1)::t')
  | SIfZ   : forall (e1 e2 : exp) heap sync t t',
             step heap sync (t ++ (TExpr (IFE (EValue (VConst 0)) THEN e1 ELSE e2))::t') ->
             step heap sync (t ++ (TExpr e2)::t').
