 Require Import Coq.Arith.EqNat.
 Require Import Coq.Arith.Le.
 Require Import Coq.Arith.Lt.
 Require Import Coq.MSets.MSetList.
 Require Import Coq.FSets.FMapList.
 Require Import Coq.Strings.String.
 Require Import Coq.Logic.Decidable.
 Require Import Omega.
 Require Import SfLib.
 Require Import ListExt.

Inductive conflict : Type :=
  | CNone : conflict
  | CRace : conflict.

(* Inductive id : Type :=
  | Id : nat -> id. *)

Definition id_eq (a : id) (b : id) := match a, b with
| Id a, Id b => beq_nat a b
end.

Eval simpl in id_eq (Id 5) (Id 6).
Eval simpl in id_eq (Id 5) (Id 5).

Inductive primitive : Type :=
  | Assert  : primitive
  | Plus    : primitive
  | NewLock : primitive
  | Acquire : primitive
  | Release : primitive.

Inductive exp : Set :=
  | EConst    : nat -> exp
  | ESyncLoc  : id -> exp
  | EFunction : list id -> exp -> exp
  | EValue    : exp -> exp
  | EId       : id -> conflict -> exp
  | EAssgn    : id -> conflict -> exp -> exp
  | ESeq      : exp -> exp -> exp
  | EPrim     : primitive -> list exp -> exp
  | EApp     : exp -> list id -> list exp -> exp
  | EIf       : exp -> exp -> exp -> exp
  | EWhile    : exp -> exp -> exp
  | ELet      : id -> exp -> exp -> exp
  | EFork     : exp -> exp
  | EAtomic   : exp -> exp
  | EInAtomic : exp -> exp.

Inductive value : exp -> Prop :=
  | VConst   : forall n, value (EConst n)
  | VSyncLoc : forall id, value (ESyncLoc id)
  | VFunction: forall lids exp, value (EFunction lids exp).

Notation "x '%' b '::=' n" := (EAssgn x b n) (at level 60).
Notation "x '%%' b" := (EId x b) (at level 60).
Notation "a ';' b" := (ESeq a b) (at level 60).
Notation "a 'p+' b" := (EPrim Plus [a, (EConst b)]) (at level 60).
Notation "'IFE' x 'THEN' a 'ELSE' b" := (EIf x a b) (at level 60).
Notation "'WHILE' a 'DO' b" := (EWhile a b) (at level 60).
Notation "'LET' a '::=' b 'IN' c" := (ELet a b c) (at level 60).
Notation "'FORK' a" := (EFork a) (at level 60).

Inductive C  : Set :=
  | C_hole   : C
  | C_assgn  : id -> conflict -> C -> C
  | C_prim   : primitive -> list (sig value) -> C -> list exp -> C
  | C_app_1  : C -> list id -> list exp -> C
  | C_app_2  : sig value -> list id -> list (sig value) -> C -> list exp -> C
  | C_if     : C -> exp -> exp -> C
  | C_let    : id -> C -> exp -> C
  | C_inatom : C -> C.

Inductive ae : exp -> Prop :=
  | ae_while : forall cond e, value cond -> ae (EWhile cond e)
  | ae_if    : forall cond e1 e2, value cond -> ae (EIf cond e1 e2)
  | ae_let   : forall id v e, value v -> ae (ELet id v e)
  | ae_id    : forall id c, ae (EId id c)
  | ae_assgn : forall id c v, value v -> ae (EAssgn id c v)
  | ae_prim  : forall prim vs, Forall value vs -> ae (EPrim prim vs)
  | ae_app   : forall f F vs, value f -> Forall value vs -> ae (EApp f F vs)
  | ae_atom  : forall e, ae (EAtomic e)
  | ae_inatom: forall v, value v -> ae (EInAtomic v)
  | ae_fork  : forall e, ae (EFork e).

Fixpoint extract_exp (l : list (sig value)) :=
match l with
| [] => []
| hd::tl => match hd with
            | exist e p => e::(extract_exp tl)
            end
end.

Eval simpl in extract_exp [exist value (EConst 5) (VConst 5), exist value (ESyncLoc (Id 6)) (VSyncLoc (Id 6))].


Inductive E  : exp -> C -> exp -> Prop :=
  | E_hole   : forall e,  E e C_hole e
  | E_assgn  : forall id c e e' C, 
               E e C e' -> 
               E (EAssgn id c e) (C_assgn id c C) e'
  | E_prim   : forall p e e' (vs : list (sig value)) C es,
               E e C e' ->
               E (EPrim p ((extract_exp vs) ++ e::es)) (C_prim p vs C es) e'
  | E_app_1  : forall f f' C F ids es,
               E f C f' ->
               E (EApp f F es) (C_app_1 C ids es) f'
  | E_app_2  : forall body F ids e e' (vs : list (sig value)) C es,
               E e C e' ->
               E (EApp (EFunction ids body) F ((extract_exp vs) ++ e::es)) 
                 (C_app_2 (exist value (EFunction ids body) (VFunction ids body)) ids vs C es) e'.

Inductive thread : Type :=
  | TExpr : exp -> thread
  | Wrong : thread.




Definition i := (Id 5).
Definition a := (EId i CNone).
Definition b := IFE a 
                THEN LET i ::= a IN (i % (CNone) ::= (EConst 6) )
                ELSE WHILE a DO a.
Definition p := (EConst 5) p+ 6.
Print b.

Inductive heap : Type :=
| HEmpty : heap
| HHeap  : forall e, value e -> id -> heap -> heap.

Print heap.
Example heapa := HEmpty.
Example heapb := HHeap (EConst 5) (VConst 5) (Id 0) HEmpty.

Definition sync_state := id -> nat.

Definition empty_sync : sync_state :=
  fun _ => 0.

Fixpoint lookup_heap (st : heap) (X:id) : option (sig value) :=
match st with
| HHeap a b c d => if (beq_id c X) then Some (exist value a b) else lookup_heap d X
| HEmpty => None
end.

(* Goal (forall y, lookup_heap (HHeap (EConst 3) (VConst 3) (Id 5) HEmpty) (Id 5) <> y). *)
(* intro. intro. destruct y. simpl in H. inversion H. destruct s. inversion H1. ... *)


Definition myheap := HHeap (EConst 5) (VConst 5) (Id 0) HEmpty.

(* Definition lookup_heap (st : heap) (X:id) : option (ex value) := *)
(* match st with *)
(* | HEmpty => None *)
(* | HHeap a b c d => Some (ex_intro value a b) *)
(* end. *)

Definition update_sync (st : sync_state) (X:id) (n : nat) : sync_state :=
  fun X' => if beq_id X X' then n else st X'.

Print value.


(* Definition extract (v : option value) := match v with *)
(*   | Some a => a *)
(*   | None   => VConst 0 *)
(* end. *)


Definition I (p : primitive) (vs : list exp) (sync_heap : sync_state) : option ((sig value) * sync_state)  := 
match p with
  | Assert  => None
  | Plus    => match vs with
                 |  (EConst a)::(EConst b)::[] => 
                      Some (exist value (EConst (a + b)) (VConst (a+b)), sync_heap)
                 | _ => None
               end
  | NewLock => None
  | Acquire => None
  | Release => None
end.



Inductive step : heap -> sync_state -> list thread -> Prop :=
  | SWhile : forall (e1 e2 : exp) (heap : heap) (sync : sync_state) (t t' : list thread), 
              step heap sync (t ++ (TExpr (WHILE e1 DO e2))::t') ->
              step heap sync (t ++ (TExpr (IFE e1 THEN e2; (WHILE e1 DO e2)  ELSE (EConst 0)))::t')
  | SIf    : forall (e1 e2 : exp) heap sync t t' v,
             value v -> v <> (EConst 0) -> 
             step heap sync (t ++ (TExpr (IFE (EValue v) THEN e1 ELSE e2))::t') ->
             step heap sync (t ++ (TExpr e1)::t')
  | SIfZ   : forall (e1 e2 : exp) heap sync t t',
             step heap sync (t ++ (TExpr (IFE (EConst 0) THEN e1 ELSE e2))::t') ->
             step heap sync (t ++ (TExpr e2)::t')
  | SLet   : forall x v e (p : value v) heap sync t t',
             lookup_heap heap x = None ->
             step heap sync (t ++ (TExpr (LET x ::= v IN e))::t') ->
             step (HHeap v p x heap) sync (t ++ (TExpr e)::t')
  | SLookup: forall x c heap sync t t' v p,
             step heap sync (t ++ (TExpr (x %% c))::t') ->
             lookup_heap heap x = Some (exist value v p) -> 
             step heap sync (t ++ (TExpr v)::t')
  | SAssgn : forall x c v p heap sync t t',
             value v ->
             step heap sync (t ++ (TExpr (x % (c) ::= v))::t') ->
             step (HHeap v p x heap) sync (t ++ (TExpr (EValue v))::t')
  | SPrim  : forall p (es : list exp) heap sync sync' v' t t' val,
             I p es sync = Some (exist value v' val, sync') ->
             step heap sync (t ++ (TExpr (EPrim p es))::t') ->
             step heap sync' (t ++ (TExpr v')::t')
  | SWrong : forall p (es : list exp) heap sync sync' t t',
             I p es sync = None ->
             step heap sync (t ++ (TExpr (EPrim p es))::t') ->
             step heap sync' (t ++ (Wrong)::t').

Example Example1 : forall heap sync_state t t', step heap sync_state (t ++ (TExpr ((EConst 1) p+ 2))::t') ->
  step heap sync_state (t ++ (TExpr (EConst 3))::t').
  intros heap sync' t t' H. 
  apply SPrim with (p:=Plus) (es:=[EConst 1, EConst 2]) (val:=VConst 3) (sync:=sync'). 
  reflexivity.
  assumption.
Qed.

Check (EConst 1) p+ 2 p+ 3.

Example Example2 : forall heap sync_state t t', step heap sync_state (t ++ (TExpr (IFE (EConst 2) p+ 3 THEN (EConst 5) ELSE (EConst 6)))::t') ->
  step heap sync_state (t ++ (TExpr (EConst 5))::t').
  intros heap sync' t t' H. 
  apply SIf with (e2:=(EConst 6)) (v:=EConst 5).
  apply VConst.
  discriminate.
  admit.
Qed.



