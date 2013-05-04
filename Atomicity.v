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
 Require Import Rel.

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
  | EId       : id -> conflict -> exp
  | EAssgn    : id -> conflict -> exp -> exp
  | ESeq      : exp -> exp -> exp
  | EPrim     : primitive -> list exp -> exp
  | EApp      : exp -> list id -> list exp -> exp
  | EIf       : exp -> exp -> exp -> exp
  | EWhile    : exp -> exp -> exp
  | ELet      : id -> exp -> exp -> exp
  | EFork     : exp -> exp
  | EAtomic   : exp -> exp
  | EInAtomic : exp -> exp.

Hint Constructors exp.

Inductive value : exp -> Prop :=
  | VConst   : forall n, value (EConst n)
  | VSyncLoc : forall id, value (ESyncLoc id)
  | VFunction: forall lids exp, value (EFunction lids exp).

Hint Constructors value.

Inductive thread : Type :=
  | TExpr : exp -> thread
  | Wrong : thread.

Notation "x '%' b '::=' n" := (EAssgn x b n) (at level 60).
Notation "x '%%' b" := (EId x b) (at level 60).
Notation "a ';' b" := (ESeq a b) (at level 60).
Notation "a 'e+' b" := (EPrim Plus [a, b]) (at level 60).
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
  | C_seq_1  : C -> exp -> C
  | C_seq_2  : exp -> C -> C
  | C_inatom : C -> C.

Hint Constructors C.

Inductive ae : exp -> Prop :=
  | ae_if    : forall cond e1 e2, value cond -> ae (EIf cond e1 e2)
  | ae_let   : forall id v e, value v -> ae (ELet id v e)
  | ae_id    : forall id c, ae (EId id c)
  | ae_assgn : forall id c v, value v -> ae (EAssgn id c v)
  | ae_prim  : forall prim vs, Forall value vs -> ae (EPrim prim vs)
  | ae_app   : forall f F vs, value f -> Forall value vs -> ae (EApp f F vs)
  | ae_atom  : forall e, ae (EAtomic e)
  | ae_inatom: forall v, value v -> ae (EInAtomic v).

Hint Constructors ae.

Fixpoint extract_exp (l : list (sig value)) :=
match l with
| [] => []
| hd::tl => match hd with
            | exist e p => e::(extract_exp tl)
            end
end.

Eval simpl in extract_exp [exist value (EConst 5) (VConst 5), exist value (ESyncLoc (Id 6)) (VSyncLoc (Id 6))].


(* The relation that decomposes an expression into a context and  *)
(* an expression in the hole of the context *)
Inductive D   : exp -> C -> exp -> Prop :=
  | DHole     : forall e, D e C_hole e
  | DAssgn    : forall C rhs' id conflict rhs,
                D rhs C rhs' -> 
                D (EAssgn id conflict rhs) (C_assgn id conflict C) rhs'
  | DSeq1     : forall e1 C v1 e2,
                D e1 C v1 ->
                D (ESeq e1 e2) (C_seq_1 C e2) v1
  | DSeq2     : forall v e C e',
                value v ->
                D e C e' ->
                D (ESeq v e) (C_seq_2 v C) e'
  | DPrim     : forall p e e' (vs : list (sig value)) C es,
                D e C e' ->
                D (EPrim p ((extract_exp vs) ++ e::es)) (C_prim p vs C es) e'
  | DApp1     : forall f f' C F ids es,
                D f C f' ->
                D (EApp f F es) (C_app_1 C ids es) f'
  | DApp2     : forall body F ids e e' (vs : list (sig value)) C es,
                D e C e' ->
                D (EApp (EFunction ids body) F ((extract_exp vs) ++ e::es))
                  (C_app_2 (exist value (EFunction ids body) (VFunction ids body)) ids vs C es) e'
  | DIf       : forall cond C cond' e1 e2,
                D cond C cond' ->
                D (EIf cond e1 e2) (C_if C e1 e2) cond'
  | DLet      : forall id e C e' body,
                D e C e' ->
                D (ELet id e body) (C_let id C body) e'
  | DInAtomic : forall e C e',
                D e C e' ->
                D (EInAtomic e) (C_inatom C) e'.

Hint Constructors D.
    

Fixpoint plug (e : exp) (cxt : C) := 
match cxt with
  | C_hole   => e
  | C_assgn id conflict cxt => EAssgn id conflict (plug e cxt)
  | C_prim  p vs cxt es     => EPrim p ((extract_exp vs) ++ (plug e cxt)::es)
  | C_app_1 cxt F es        => EApp (plug e cxt) F es
  | C_app_2 (exist f p) F vs cxt es   
                            => EApp f F ((extract_exp vs) ++ (plug e cxt)::es)
  | C_if    cxt e1 e2       => EIf (plug e cxt) e1 e2
  | C_let   id cxt body     => ELet id (plug e cxt) body
  | C_seq_1 cxt e2          => ESeq (plug e cxt) e2
  | C_seq_2 e1  cxt         => ESeq e1 (plug e cxt)
  | C_inatom cxt             => EInAtomic (plug e cxt)
end.

Definition i := (Id 5).
Definition a := (EId i CNone).
Definition b := IFE a 
                THEN LET i ::= a IN (i % (CNone) ::= (EConst 6) )
                ELSE WHILE a DO a.
Definition p := (EConst 5) e+ (EConst 6).
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


(* Inductive red : exp -> exp -> Prop := *)


(* Hint Constructors red. *)


Inductive progstate : Type :=
  | ProgState : heap -> sync_state -> list thread -> progstate.

Reserved Notation "'[|' ha '//' sa '//' ta1 ',' ea ',' ta2 '===>' hb '//' sb '//' tb1 ',' eb ',' tb2 '|]'" (at level 50, no associativity).


Inductive step : progstate -> progstate -> Prop :=
  | SIf    : forall e C ae e' e1 e2 heap1 heap' sync sync' t t',
             D e C ae ->
             [| heap1 // sync // t, ae, t' ===> heap' // sync' // t, e', t' |]  ->
             [| heap1 // sync // t, (IFE e THEN e1 ELSE e2), t' ===>
                heap'// sync'// t, (IFE (plug e' C) THEN e1 ELSE e2), t' |]
  | SIfV   : forall (v e1 e2 : exp) heap sync t t',
             value v -> 
             [| heap // sync // t, (IFE v THEN e1 ELSE e2), t' ===>
                heap // sync // t, e1, t' |]
  | SIfZ   : forall e1 e2 heap sync t t',
             [| heap // sync // t, IFE (EConst 0) THEN e1 ELSE e2, t' ===>
                heap // sync // t, e2, t' |] 
  | SWhile : forall (e1 e2 : exp) (heap : heap) (sync : sync_state) (t t' : list thread),
             [| heap // sync // t, (WHILE e1 DO e2), t' ===>
                heap // sync // t, (IFE e1 THEN e2; (WHILE e1 DO e2)  ELSE (EConst 0)), t' |]
  | SLet1  : forall x e e' C ae heap sync heap' sync' body t t',
             lookup_heap heap x = None ->
             D e C ae ->
             [| heap // sync // t, ae, t' ===> heap' // sync' // t, e', t' |] ->
             [| heap // sync // t, (LET x ::= e IN body), t' ===>
                heap'// sync'// t, (LET x::= (plug e' C) IN body), t' |]
  | SLet2  : forall x v p body heap sync t t',
             lookup_heap heap x = None ->
             value v ->
             [| heap // sync // t, (LET x ::= v IN body), t' ===> 
                (HHeap v p x heap) // sync // t, body, t' |]
  | SLookup: forall x c heap sync t t' v p,
             lookup_heap heap x = Some (exist value v p) ->
             [| heap // sync // t, x %% c, t' ===> heap // sync // t, v, t' |]
  | SAssgn1: forall x c e C ae e' heap sync heap' sync' t t',
             D e C ae ->
             [| heap // sync // t, ae, t' ===> heap' // sync' // t, e', t' |] ->
             [| heap // sync // t, x % (c) ::= e, t' ===>
                heap'// sync'// t, x % (c) ::= (plug e' C), t' |]
  | SAssgn2: forall x c v p heap sync t t',
             value v ->
             [| heap // sync // t, x % (c) ::= v, t' ===>
                (HHeap v p x heap) // sync // t, v, t' |]
  | SPrim1  : forall p esa e C ae e' esb heap heap' sync sync' t t',
              Forall value esa ->
              D e C ae ->
              [| heap // sync // t, ae, t' ===> heap' // sync' // t, e', t' |] ->
              [| heap // sync // t, EPrim p (esa ++ e::esb), t' ===> 
                 heap'// sync'// t, EPrim p (esa ++ (plug e' C)::esb), t' |]
  | SPrim2  : forall p (es : list exp) heap sync sync' v' pv t t',
              Forall value es ->
              I p es sync = Some (exist value v' pv, sync') ->
              [| heap // sync // t, EPrim p es, t' ===>
                 heap // sync'// t, v', t' |]
  | SWrong  : forall p (es : list exp) heap sync t t',
              Forall value es ->
              I p es sync = None ->
              step (ProgState heap sync (t ++ (TExpr (EPrim p es))::t'))
                   (ProgState heap sync (t ++ Wrong::t'))
  | SApp1   : forall f C ae e' F es heap heap' sync sync' t t',
              D f C ae ->
              [| heap // sync // t, ae, t' ===> heap' // sync' // t, e', t' |] ->
              [| heap // sync // t, EApp f F es, t' ===>
                 heap'// sync'// t, EApp (plug e' C) F es, t' |]
  | SApp2   : forall ids vs e C ae e' F es body t t' heap sync heap' sync',
              D e C ae ->
              [| heap // sync // t, e, t' ===> heap' // sync' // t, e', t' |] ->
              [| heap // sync // t, EApp (EFunction ids body) F ((extract_exp vs) ++ e::es), t' ===>
                 heap' // sync' // t, EApp (EFunction ids body) F ((extract_exp vs) ++ e'::es), t' |]
  | SApp3   : forall ids vs v p F es body t t' heap sync,
              [| heap // sync // t, EApp (EFunction ids body) F ((extract_exp vs) ++ v::es), t' ===>
                 heap // sync // t, EApp (EFunction ids body) F ((extract_exp (vs ++ [exist value v p])) ++ es), t' |]
  | SSeq1   : forall e C ae e' e2 t t' heap heap' sync sync',
              D e C ae ->
              [| heap // sync // t, ae, t' ===> heap' // sync' // t, e', t' |] ->
              [| heap // sync // t, e; e2, t'  ===> heap' // sync' // t, (plug e' C); e2, t' |]
  | SSeq2   : forall v e2 t t' heap sync,
              value v ->
              [| heap // sync // t, v; e2, t'  ===> heap // sync // t, e2, t' |]
  | SAtomic : forall e t t' heap sync,
              [| heap // sync // t, EAtomic e, t'  ===> heap // sync // t, EInAtomic e, t' |]
  | SInAtom1: forall e C ae e' heap heap' sync sync' t t',
              D e C ae ->
              [| heap // sync // t, ae, t' ===> heap' // sync' // t, e', t' |] ->
              [| heap // sync // t, EInAtomic e, t' ===> heap' // sync' // t, EInAtomic (plug e' C), t' |]
  | SInAtom2: forall v heap sync t t',
              value v ->
              [| heap // sync // t, EInAtomic v, t' ===> heap // sync // t, v, t' |]
  | SFork   : forall e heap sync t t',
              [| heap // sync // t, EFork e, t' ===> heap // sync // t, EConst 0, t' ++ [TExpr e] |]
  where "'[|' ha '//' sa '//' ta1 ',' ea ',' ta2 '===>' hb '//' sb '//' tb1 ',' eb ',' tb2 '|]'" := 
  (step (ProgState ha sa (ta1 ++ (TExpr ea)::ta2))
        (ProgState hb sb (tb1 ++ (TExpr eb)::tb2))).

Hint Constructors step.

Hint Constructors refl_step_closure.

Definition many_steps := refl_step_closure step.

Notation "'[|' ha '//' sa '//' ta1 ',' ea ',' ta2 '===>*' hb '//' sb '//' tb1 ',' eb ',' tb2 '|]'" := 
(many_steps (ProgState ha sa (ta1 ++ (TExpr ea)::ta2))
            (ProgState hb sb (tb1 ++ (TExpr eb)::tb2))) (at level 50, no associativity).


Example Example1 : forall heap sync_state t t', [| heap // sync_state // t, (EConst 1) e+ (EConst 2), t' ===>
  heap // sync_state // t, EConst 3, t' |].
  intros.
  apply SPrim2 with (pv:=VConst 3); auto.
Qed.

Example Example2 : forall heap sync t t',
  [| heap // sync // t, IFE (EConst 2) e+ (EConst 3) THEN (EConst 5) ELSE (EConst 6), t' ===>
     heap // sync // t, IFE (EConst 5) THEN (EConst 5) ELSE (EConst 6), t' |].
  intros. apply SIf with (ae:=(EConst 2) e+ (EConst 3)) (C:=C_hole).
  auto. apply SPrim2 with (pv:=VConst 5); auto.
Qed.



Example Example3 : forall heap sync t t',
  [| heap // sync // t, IFE (EConst 2) e+ (EConst 3) THEN (EConst 5) ELSE (EConst 6), t' ===>*
     heap // sync // t, EConst 5, t' |].
Proof with simpl; auto.
  intros. 
  eapply rsc_step. 
  eapply SIf... 
  eapply SPrim2...
  eapply rsc_step...
Qed.