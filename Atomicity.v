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
Require Import Recdef.

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
  | Minus   : primitive
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
  | EAssert   : exp -> exp
  | EPlus     : exp -> exp -> exp
  | EMinus    : exp -> exp -> exp
  | ENewLock  : id  -> exp
  | EAcquire  : id  -> exp
  | ERelease  : id  -> exp
  | EApp      : exp -> list id -> list exp -> exp
  | EIf       : exp -> exp -> exp -> exp
  | EWhile    : exp -> exp -> exp
  | ELet      : id -> exp -> exp -> exp
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
Notation "x '%%' b" := (EId x b) (at level 70).
Notation "a ';' b" := (ESeq a b) (at level 80).
Notation "a 'e+' b" := (EPlus a b) (at level 70).
Notation "a 'e-' b" := (EMinus a b) (at level 70).
Notation "'IFE' x 'THEN' a 'ELSE' b" := (EIf x a b) (at level 80).
Notation "'WHILE' a 'DO' b" := (EWhile a b) (at level 60).
Notation "'LET' a '::=' b 'IN' c" := (ELet a b c) (at level 60).

Inductive C  : Set :=
  | C_hole   : C
  | C_assgn  : id -> conflict -> C -> C
  | C_plus1  : C -> exp -> C
  | C_plus2  : exp -> C -> C
  | C_minus1 : C -> exp -> C
  | C_minus2 : exp -> C -> C
  | C_assert : C -> C
  | C_app_1  : C -> list id -> list exp -> C
  | C_app_2  : sig value -> list id -> list (sig value) -> C -> list exp -> C
  | C_if     : C -> exp -> exp -> C
  | C_let    : id -> C -> exp -> C
  | C_seq  : C -> exp -> C
  | C_inatom : C -> C.

Hint Constructors C.

Inductive ae : exp -> Prop :=
  | ae_if    : forall cond e1 e2, value cond -> ae (EIf cond e1 e2)
  | ae_let   : forall id v e, value v -> ae (ELet id v e)
  | ae_id    : forall id c, ae (EId id c)
  | ae_assgn : forall id c v, value v -> ae (EAssgn id c v)
  | ae_assert   : forall e, value e -> ae (EAssert e)
  | ae_plus   : forall a b, value a -> value b -> ae (EPlus a b)
  | ae_minus  : forall a b, value a -> value b -> ae (EMinus a b)
  | ae_newlock: forall id, ae (ENewLock id)
  | ae_acquire: forall id, ae (EAcquire id)
  | ae_release: forall id, ae (ERelease id)
  | ae_app   : forall f F vs, value f -> Forall value vs -> ae (EApp f F vs)
  | ae_atom  : forall e, ae (EAtomic e)
  | ae_inatom: forall v, value v -> ae (EInAtomic v)
  | ae_seq   : forall v e, value v -> ae (ESeq v e).

Hint Constructors ae.

Fixpoint extract_exp (v : (sig value)) : exp :=
match v with
  | exist e p => e
end.

Fixpoint extract_exps (l : list (sig value)) := map extract_exp l.

Eval simpl in extract_exps [exist value (EConst 5) (VConst 5), exist value (ESyncLoc (Id 6)) (VSyncLoc (Id 6))].


(* The relation that decomposes an expression into a context and  *)
(* an expression in the hole of the context *)
Inductive D   : exp -> C -> exp -> Prop :=
  | DHole     : forall e, D e C_hole e
  | DAssgn    : forall C rhs' id conflict rhs,
                D rhs C rhs' -> 
                D (EAssgn id conflict rhs) (C_assgn id conflict C) rhs'
  | DSeq      : forall e1 C e1' e2,
                D e1 C e1' ->
                D (ESeq e1 e2) (C_seq C e2) e1'
  | DAssert   : forall e C ae, 
                D e C ae ->
                D (EAssert e) (C_assert C) ae
  | DPlus1    : forall a C ae b,
                D a C ae ->
                D (EPlus a b) (C_plus1 C b) ae
  | DPlus2    : forall v b C ae,
                value v ->
                D b C ae ->
                D (EPlus v b) (C_plus2 v C) ae
  | DMinus1   : forall a C ae b,
                D a C ae ->
                D (EMinus a b) (C_minus1 C b) ae
  | DMinus2   : forall v b C ae,
                value v ->
                D b C ae ->
                D (EMinus v b) (C_minus2 v C) ae
  | DApp1     : forall f f' C F ids es,
                D f C f' ->
                D (EApp f F es) (C_app_1 C ids es) f'
  | DApp2     : forall body F ids e e' (vs : list (sig value)) C es,
                D e C e' ->
                D (EApp (EFunction ids body) F ((extract_exps vs) ++ e::es))
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
  | C_plus1 cxt b           => EPlus (plug e cxt) b
  | C_plus2 v   cxt         => EPlus v (plug e cxt)
  | C_minus1 cxt b          => EMinus (plug e cxt) b
  | C_minus2 v   cxt        => EMinus v (plug e cxt)
  | C_assert cxt            => EAssert (plug e cxt)
  | C_app_1 cxt F es        => EApp (plug e cxt) F es
  | C_app_2 (exist f p) F vs cxt es   
                            => EApp f F ((extract_exps vs) ++ (plug e cxt)::es)
  | C_if    cxt e1 e2       => EIf (plug e cxt) e1 e2
  | C_let   id cxt body     => ELet id (plug e cxt) body
  | C_seq   cxt e2          => ESeq (plug e cxt) e2
  | C_inatom cxt            => EInAtomic (plug e cxt)
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

Definition sync_state := id -> option nat.

Definition empty_sync : sync_state :=
  fun _ => None.

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
  fun X' => if beq_id X X' then Some n else st X'.

Print value.

(* Definition extract (v : option value) := match v with *)
(*   | Some a => a *)
(*   | None   => VConst 0 *)
(* end. *)


Reserved Notation "'EVAL' 'I_' p '||' vs ',' M ',' tid '===>' '< v ',' sb '>'" (at level 60, no associativity).


Inductive I : primitive -> list exp -> sync_state -> nat -> sig value -> sync_state -> Prop := 
| IAssert : forall e M tid,   e <> EConst 0 ->
                              I Assert [e] M tid (exist value (EConst 0) (VConst 0)) M
| IPlus   : forall a b M tid, I Plus   [EConst a, EConst b] M tid (exist value (EConst (a+b)) (VConst (a+b))) M
| IMinus  : forall a b M tid, I Minus  [EConst a, EConst b] M tid (exist value (EConst (a-b)) (VConst (a-b))) M
| INewLock: forall m M tid,   M m = None ->
                              I NewLock []  M tid (exist value (ESyncLoc m) (VSyncLoc m)) (update_sync M m 0)
| IAcquire: forall m M tid,   M m = Some 0 ->
                              I Acquire [ESyncLoc m] M tid (exist value (ESyncLoc m) (VSyncLoc m)) (update_sync M m tid)
| IRelease: forall m M tid,   M m = Some tid ->
                              I Release [ESyncLoc m] M tid (exist value (ESyncLoc m) (VSyncLoc m)) (update_sync M m 0).

Fixpoint contains_inatom e : bool :=
  match e with 
    | EConst _ => false
    | ESyncLoc _ => false
    | EFunction _ e => contains_inatom e
    | EId _ _  => false
    | EAssgn _ _ e => contains_inatom e
    | ESeq e1 e2 => 
      contains_inatom e1 || contains_inatom e2
    | EPlus a b  => contains_inatom a || contains_inatom b
    | EMinus a b  => contains_inatom a || contains_inatom b
    | EAssert e  => contains_inatom e
    | ENewLock _ => false
    | EAcquire _ => false
    | ERelease  _ => false
    | EApp f _ args => 
      (contains_inatom f) ||
      (fold_left orb (map contains_inatom args) false)
    | EIf c b1 b2 => 
      contains_inatom c ||
      contains_inatom b1 ||
      contains_inatom b2 
    | EWhile c b => 
      contains_inatom c ||
      contains_inatom b
    | ELet _ lhs rhs =>
      contains_inatom lhs ||
      contains_inatom rhs
    | EAtomic e => contains_inatom e
    | EInAtomic e => true
end.

Fixpoint contains_inatom_threads (ts : list thread) : bool :=
match ts with
| [] => false
| t::tl => match t with
           | TExpr e => contains_inatom e || contains_inatom_threads tl
           | _       => false
           end
end.



Inductive threadstate : Type :=
  | ThreadState : heap -> sync_state -> thread -> threadstate.


Reserved Notation "'[|' ha '//' sa '//' ea '===>' hb '//' sb '//' eb '|]'" (at level 50, no associativity).

Inductive tstep : threadstate -> threadstate -> Prop :=
  | SIf    : forall e C ae e' e1 e2 heap heap' sync sync',
             D e C ae ->
             [| heap // sync // ae ===> heap' // sync' // e' |]  ->
             [| heap // sync // (IFE e THEN e1 ELSE e2) ===>
                heap'// sync'// (IFE (plug e' C) THEN e1 ELSE e2) |]
  | SIfV   : forall (v e1 e2 : exp) heap sync,
             value v -> 
             v <> EConst 0 ->
             [| heap // sync // (IFE v THEN e1 ELSE e2) ===>
                heap // sync // e1 |]
  | SIfZ   : forall e1 e2 heap sync,
             [| heap // sync // IFE (EConst 0) THEN e1 ELSE e2 ===>
                heap // sync // e2 |] 
  | SWhile : forall (e1 e2 : exp) (heap : heap) (sync : sync_state),
             [| heap // sync // (WHILE e1 DO e2) ===>
                heap // sync // (IFE e1 THEN e2; (WHILE e1 DO e2)  ELSE (EConst 0)) |]
  | SLet1  : forall x e e' C ae heap sync heap' sync' body,
             lookup_heap heap x = None ->
             D e C ae ->
             [| heap // sync // ae ===> heap' // sync' // e' |] ->
             [| heap // sync // (LET x ::= e IN body) ===>
                heap'// sync'// (LET x::= (plug e' C) IN body) |]
  | SLet2  : forall x v p body heap sync,
             lookup_heap heap x = None ->
             value v ->
             [| heap // sync // (LET x ::= v IN body) ===> 
                (HHeap v p x heap) // sync // body |]
  | SLookup: forall x c heap sync v p,
             lookup_heap heap x = Some (exist value v p) ->
             [| heap // sync // x %% c ===> heap // sync // v |]
  | SAssgn1: forall x c e C ae e' heap sync heap' sync',
             D e C ae ->
             [| heap // sync // ae ===> heap' // sync' // e' |] ->
             [| heap // sync // x % (c) ::= e ===>
                heap'// sync'// x % (c) ::= (plug e' C) |]
  | SAssgn2: forall x c v p heap sync,
             value v ->
             [| heap // sync // x % (c) ::= v ===>
                (HHeap v p x heap) // sync // v |]
  | SAssert1: forall heap sync heap' sync'  e C ae e', 
             D e C ae ->
             [| heap // sync // ae ===> heap' // sync' // e' |] ->
             [| heap // sync // EAssert e ===> heap' // sync' // EAssert (plug e' C) |]
  | SAssert2:forall heap sync e,
             value e ->
             e <> EConst 0 ->
             [| heap // sync // EAssert e ===> heap // sync // EConst 0 |]
  | SPlus1 : forall a C ae e' b heap sync heap' sync',
             D a C ae ->
             [| heap // sync // ae ===> heap' // sync' // e' |] ->
             [| heap // sync // EPlus a b ===> heap' // sync' // EPlus (plug e' C) b |]
  | SPlus2 : forall v e C ae e' heap sync heap' sync',
             value v ->
             D e C ae ->
             [| heap // sync // ae ===> heap' // sync' // e' |] ->
             [| heap // sync // EPlus v e ===> heap' // sync' // EPlus v (plug e' C) |]
  | SPlus3 : forall a b heap sync,
             [| heap // sync // EPlus (EConst a) (EConst b) ===> heap // sync // EConst (a + b) |]
  | SMinus1 : forall a C ae e' b heap sync heap' sync',
             D a C ae ->
             [| heap // sync // ae ===> heap' // sync' // e' |] ->
             [| heap // sync // EMinus a b ===> heap' // sync' // EMinus (plug e' C) b |]
  | SMinus2 : forall v e C ae e' heap sync heap' sync',
             value v ->
             D e C ae ->
             [| heap // sync // ae ===> heap' // sync' // e' |] ->
             [| heap // sync // EMinus v e ===> heap' // sync' // EMinus v (plug e' C) |]
  | SMinus3 : forall a b heap sync,
             [| heap // sync // EMinus (EConst a) (EConst b) ===> heap // sync // EConst (a - b) |]
  | SNewLock: forall m heap sync,  
              sync m = None ->
              [| heap // sync // ENewLock m ===> heap // (update_sync sync m 0) // ESyncLoc m |]
  | SAcquire: forall m tid heap sync,
              sync m = Some 0 ->
              [| heap // sync // EAcquire m ===> heap // (update_sync sync m tid) // ESyncLoc m |]
  | SRelease: forall m tid heap sync,
              sync m = Some tid ->
              [| heap // sync // ERelease m ===> heap // (update_sync sync m 0) // ESyncLoc m |]
  (* | SWrong  : forall p vs heap tid v sync sync', *)
  (*             Forall value vs -> *)
  (*             ~ I p vs sync tid v sync' -> *)
  (*             tstep (ThreadState heap sync (TExpr (EPrim p vs))) *)
  (*                  (ThreadState heap sync Wrong) *)
  | SApp1   : forall f C ae e' F es heap heap' sync sync',
              D f C ae ->
              [| heap // sync // ae ===> heap' // sync' // e' |] ->
              [| heap // sync // EApp f F es ===>
                 heap'// sync'// EApp (plug e' C) F es |]
  | SApp2   : forall ids vs e C ae e' F es body heap sync heap' sync',
              D e C ae ->
              [| heap // sync // ae ===> heap' // sync' // e' |] ->
              [| heap // sync // EApp (EFunction ids body) F ((extract_exps vs) ++ e::es) ===>
                 heap'// sync'// EApp (EFunction ids body) F ((extract_exps vs) ++ e'::es) |]
  | SApp3   : forall ids vs v p F es body heap sync,
              [| heap // sync // EApp (EFunction ids body) F ((extract_exps vs) ++ v::es) ===>
                 heap // sync // EApp (EFunction ids body) F ((extract_exps (vs ++ [exist value v p])) ++ es) |]
  | SSeq1   : forall e C ae e' e2 heap heap' sync sync',
              D e C ae ->
              [| heap // sync // ae ===> heap' // sync' // e' |] ->
              [| heap // sync // e; e2 ===> heap' // sync' // (plug e' C); e2 |]
  | SSeq2   : forall v e2 heap sync,
              value v ->
              [| heap // sync // v; e2 ===> heap // sync // e2 |]
  | SAtomic : forall e heap sync,
              [| heap // sync // EAtomic e ===> heap // sync // EInAtomic e |]
  | SInAtom1: forall e C ae e' heap heap' sync sync',
              D e C ae ->
              [| heap // sync // ae ===> heap' // sync' // e' |] ->
              [| heap // sync // EInAtomic e ===> heap' // sync' // EInAtomic (plug e' C) |]
  | SInAtom2: forall v heap sync,
              value v ->
              [| heap // sync // EInAtomic v ===> heap // sync // v |]
  where "'[|' ha '//' sa '//' ea '===>' hb '//' sb '//' eb '|]'" := 
  (tstep (ThreadState ha sa (TExpr ea))
        (ThreadState hb sb (TExpr eb))).

Hint Constructors tstep.

Inductive progstate : Type :=
  | ProgState : heap -> sync_state -> list thread -> progstate.

Reserved Notation "'[|' ha '//' sa '//' ta1 ',' ea ',' ta2 '===>' hb '//' sb '//' tb1 ',' eb ',' tb2 '|]'" (at level 50, no associativity).

Inductive step : progstate -> progstate -> Prop :=
  | Step : forall ha hb sa sb ta1 ta2 tb1 tb2 ea eb,
             [| ha // sa // ea ===> hb // sb // eb |] ->
             [| ha // sa // ta1, ea, ta2 ===> hb // sb // tb1, eb, tb2 |]
  where "'[|' ha '//' sa '//' ta1 ',' ea ',' ta2 '===>' hb '//' sb '//' tb1 ',' eb ',' tb2 '|]'" := 
  (step (ProgState ha sa (ta1 ++ (TExpr ea)::ta2))
        (ProgState hb sb (tb1 ++ (TExpr eb)::tb2))).

Hint Constructors step.


Reserved Notation "'[|' ha '//' sa '//' ta1 ',' ea ',' ta2 '===>>' hb '//' sb '//' tb1 ',' eb ',' tb2 '|]'" (at level 50, no associativity).

Inductive coarsestep : progstate -> progstate -> Prop :=
  | CoarseStep : forall heap sync heap' sync' ta1 ta2 tb1 tb2 e e',
                 (contains_inatom_threads ta1) = false -> 
                 (contains_inatom_threads ta2) = false ->
                 (contains_inatom_threads tb1) = false -> 
                 (contains_inatom_threads tb2) = false ->
                 [| heap // sync // ta1, e, ta2 ===> heap' // sync' // tb1, e', tb2 |] ->
                 [| heap // sync // ta1, e, ta2 ===>> heap' // sync' // tb1, e', tb2 |]
  where "'[|' ha '//' sa '//' ta1 ',' ea ',' ta2 '===>>' hb '//' sb '//' tb1 ',' eb ',' tb2 '|]'" :=
  (coarsestep (ProgState ha sa (ta1 ++ (TExpr ea)::ta2))
        (ProgState hb sb (tb1 ++ (TExpr eb)::tb2))).

Hint Constructors refl_step_closure.

Definition  many_tsteps := refl_step_closure tstep.

Notation "'[|' ha '//' sa '//' ea '===>*' hb '//' sb '//' eb '|]'" := 
(many_tsteps (ThreadState ha sa (TExpr ea))
             (ThreadState hb sb (TExpr eb))) (at level 50, no associativity).

Definition  many_steps := refl_step_closure step.

Notation "'[|' ha '//' sa '//' ta1 ',' ea ',' ta2 '===>*' hb '//' sb '//' tb1 ',' eb ',' tb2 '|]'" := 
(many_steps (ProgState ha sa (ta1 ++ (TExpr ea)::ta2))
            (ProgState hb sb (tb1 ++ (TExpr eb)::tb2))) (at level 50, no associativity).


Example Example1 : forall heap sync_state ta tb, [| heap // sync_state // ta, (EConst 1) e+ (EConst 2), tb ===>*
  heap // sync_state // ta, EConst 3, tb |].
Proof with simpl; auto.
  intros h s ta tb.
  eapply rsc_step...
Qed.

Example Example2 : forall heap sync ta tb,
  [| heap // sync // ta, IFE (EConst 2) e+ (EConst 3) THEN (EConst 5) ELSE (EConst 6), tb ===>*
     heap // sync // ta, IFE (EConst 5) THEN (EConst 5) ELSE (EConst 6), tb |].
Proof with simpl; auto.
  intros.
  eapply rsc_step.
  eapply Step.
  eauto.
  eauto.
Qed.

Example Example3 : forall heap sync ta tb,
  [| heap // sync // ta, IFE (EConst 2) e+ (EConst 3) THEN (EConst 5) ELSE (EConst 6), tb ===>*
     heap // sync // ta, EConst 5, tb |].
Proof with simpl; auto.
  intros. 
  eapply rsc_step.
  eapply Step.
  eapply SIf...
  eapply rsc_step.
  eapply Step.
    eapply SIfV...
    discriminate.
  eapply rsc_refl.
  Grab Existential Variables. auto. auto.
Qed.

Definition X := Id 0.

Example Example4 : forall heap sync ta tb,
  [| (HHeap (EConst 1) (VConst 1) X heap) // sync // ta, 
     WHILE (X %% (CNone)) DO (X % (CNone) ::= ((X %% (CNone)) e- (EConst 1))), tb ===>*
     (HHeap (EConst 0) (VConst 0) X (HHeap (EConst 1) (VConst 1) X heap)) // sync // ta, EConst 0, tb |].
Proof with simpl; auto.
  intros.
  eapply rsc_step...
  eapply rsc_step.
  eapply Step.
    eapply SIf...
    eapply SLookup...
  eapply rsc_step.
  eapply Step.
    eapply SIfV... discriminate.
  eapply rsc_step.
  eapply Step.
    eapply SSeq1...
    eapply SAssgn1...
    eapply SMinus1... 
    eapply SLookup...
  eapply rsc_step.
  apply Step.
    eapply SSeq1... 
    eapply SAssgn1...
  eapply rsc_step.
  apply Step.
    eapply SSeq1...
  eapply rsc_step...
  eapply rsc_step...
  eapply rsc_step.
  apply Step.
    eapply SIf...
    eapply SLookup...
  eauto.
  Grab Existential Variables. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
Qed.

(* Things we would like to show here:
   1) The expression produced by decomposition is always an active expression.
   2)
*)
Lemma decomp : forall e, value e \/ (exists C, exists e', D e C e' /\ ae e').
Proof with simpl; auto.
  intros. 
  induction e.
  Case "EConst". left...
  Case "ESyncLoc". left...
  Case "EFunction". left...
  Case "id %% c". right... eauto.
  Case "id % c ::= e". right... destruct IHe; eauto. 
  destruct H. destruct H. destruct H. eauto.
  Case "e1; e2". right... destruct IHe1.
    SCase "value e1". destruct IHe2. 
      SSCase "value e2". eauto. 
      SSCase "e2 contains an ae". destruct H0. destruct H0. destruct H0. eauto.
    SCase "e1 contains an ae". destruct H. destruct H. destruct H. eauto. 
  Case "EAssert". admit. 
  Case "EPlus". admit.
  Case "EMinus". admit.
  Case "ENewLock". admit.
  Case "EAcquire". admit.
  Case "ERelease". admit.
  Case "EApp".  admit. (* We might not do functions *)
  Case "EIf". right. destruct IHe1. 
    SCase "value cond". eauto.
    SCase "cond contains an ae". inversion H.  inversion H0. inversion H1. eauto.
  Case "EWhile". admit. (* While desugars, so there's no real active expression here *)
  Case "ELet". right. destruct IHe1. 
    SCase "value e1". eauto.
    SCase "e1 contains an ae". inversion H. inversion H0. inversion H1. eauto.
  Case "EAtomic". right. eauto.
  Case "EInAtomic". right. inversion IHe. 
    SCase "value e". eauto.
    SCase "e contains an ae". inversion H. inversion H0. inversion H1. eauto.
Qed.

(******** Typing rules and proofs **************)


Inductive atom : Set := 
| TTop : atom
| TAtom : atom
| TLeft : atom
| TRight : atom
| TBoth : atom.

(* Axiom has_type : exp -> atom -> Prop. *)

(* Lemma 
For all threads t, all output states s, if P typechecks then there
exists some reduced P' such that P' steps to s for all threads.
*)

(* Mover function *)

(* Axiom  has_type_dec : forall e a,  *)
(*   {has_type e a} + {~ has_type  e a}. *)

(* Definition get_type e : atom := *)
(*   if (has_type_dec e TTop) then TTop *)
(*   else if (has_type_dec e TAtom) then TAtom *)
(*   else if (has_type_dec e TLeft) then TLeft *)
(*   else if (has_type_dec e TRight) then TRight *)
(*   else TBoth. *)

(* Hint Transparent move_right. *)

(* Eval  in (move_right [((EConst 1), Id 1), ((EConst 2), Id 2)]).  *)


(* Eval  compute in (move_right [((EConst 1), Id 1), ((EConst 2), Id 2)]). *)

(* Eval simpl in (List.length [1]). *)

(* Fixpoint reorder_int (beg : list (exp * id)) (tail : list (exp * id)) : list (exp * id) := *)
(*     match tail with  *)
(*       | [] => (reverse beg) *)
(*       | (e i) ::rest =>  *)
(*         match (get_type_dec e) with *)
(*           | TRight =>  *)
(*             match (move_right tail) with  *)
              
                        
(*           | TLeft =>  *)
(*           | TBoth => *)
(*           (* do nothing for TAtom and TTop *) *)
(*           | _ => rerder_int (e i)::beg rest *)
(*     end. *)

(* Fixpoint reorder (l : list (exp * id)) : list (exp * id) := *)
(*   reorder_int [] l. *)

Fixpoint lub (a1 a2: atom) : atom  := 
  match a1, a2 with
    | _, TTop => TTop
    | TTop, _ => TTop
    | _, TAtom => TAtom
    | TAtom, _ => TAtom
    | TLeft, TRight => TAtom
    | TRight, TLeft => TAtom
    | TBoth, r => r
    | l, TBoth => l
    | _, _ => TTop
end.

Definition  seq_comp (a1 a2: atom) : atom := 
  match a1, a2 with
    | TTop, _ => TTop
    | _, TTop => TTop
    | TBoth, r => r
    | l, TBoth => l
    | TRight, TLeft => TAtom
    | TRight, TRight => TRight
    | TRight, TAtom => TAtom
    | TLeft, TLeft => TLeft
    | TLeft, _ => TTop
    | TAtom, TLeft => TAtom
    | TAtom, _ => TTop
  end.

Definition iterative_closure a : atom := 
  match a with 
    | TTop => TTop
    | TAtom => TTop
    | a => a
  end.

Definition  prim_type p : atom := 
  match p with
  | Assert  => TBoth
  | Plus    => TBoth
  | Minus   => TBoth
  | NewLock => TBoth
  | Acquire => TRight
  | Release => TLeft
end.

Definition seq_comp_many ts : atom :=
  match ts with 
    | hd::tl   => fold_left seq_comp tl hd
    | []       => TBoth
end.

Inductive reduce_args : list exp -> heap -> sync_state -> list exp -> heap -> sync_state -> Prop :=
| reduce_nil  : forall h s, reduce_args [] h s [] h s
| reduce_cons : forall e v es vs h s h' s' h'' s'', value v ->
                                         [| h // s // e ===>* h' // s' // v |] ->
                                         reduce_args es h' s' vs h'' s'' ->
                                         reduce_args (e::es) h s (v::vs) h'' s''.

Inductive result : Set :=
| RConst    : result 
| RSyncLoc  : result
| RFunction : result.

Inductive result_type : exp -> result -> Prop :=
| R_Const   : forall n, result_type (EConst n) RConst
| R_SyncLoc : forall id, result_type (ESyncLoc id) RSyncLoc
| R_Plus    : forall a b,
              result_type a RConst ->
              result_type b RConst ->
              result_type (EPlus a b) RConst
| R_Minus   : forall a b,
              result_type a RConst ->
              result_type b RConst ->
              result_type (EMinus a b) RConst
| R_Assert  : forall e te, 
              result_type e te ->
              result_type (EAssert e) RConst
| R_NewLock : forall id, result_type (ENewLock id) RSyncLoc
| R_Acquire : forall id, result_type (EAcquire id) RSyncLoc
| R_Release : forall id, result_type (ERelease id) RSyncLoc
(* | R_Read    : forall *)
| R_Assgn   : forall id c e te, 
              result_type e te ->
              result_type (EAssgn id c e) te
| R_If      : forall cond e1 e2 tc te,
              result_type cond tc ->
              result_type e1 te ->
              result_type e2 te ->
              result_type (IFE cond THEN e1 ELSE e2) te
| R_While   : forall cond body tc tb,
              result_type cond tc ->
              result_type cond tb ->
              result_type (WHILE cond DO body) RConst
| R_Atomic  : forall e te,
              result_type e te ->
              result_type (EAtomic e) te
| R_InAtomic: forall e te,
              result_type e te ->
              result_type (EInAtomic e) te.

(* We folded our primitives into the type  *)

Inductive has_type : exp -> atom -> Prop := 
| T_Const     : forall n, has_type  (EConst n) TBoth
| T_SyncLoc   : forall id, has_type (ESyncLoc id) TBoth
| T_Function  : forall lids body, has_type (EFunction lids body) TBoth
| T_Plus      : forall a b ta tb, 
                has_type a ta ->
                has_type b tb ->
                has_type (EPlus a b) (seq_comp_many [ta, tb, prim_type Plus])
| T_Minus     : forall a b ta tb, 
                has_type a ta ->
                has_type b tb ->
                has_type (EMinus a b) (seq_comp_many [ta, tb, prim_type Minus])
| T_Assert    : forall e te,
                has_type e te ->
                has_type (EAssert e) (seq_comp te (prim_type Assert))
| T_NewLock   : forall id,
                has_type (ENewLock id) (prim_type NewLock)
| T_Acquire   : forall id,
                has_type (EAcquire id) (prim_type Acquire)
| T_Release   : forall id,
                has_type (ERelease id) (prim_type Release)
(* | T_Fun       : forall  *)
| T_Read      : forall id,
                has_type (EId id CNone) TBoth
| T_ReadRace  : forall id, 
                has_type (EId id CRace) TAtom
| T_Assgn     : forall id e t, 
                has_type e t -> 
                has_type (EAssgn id CNone e) (seq_comp t TBoth)
| T_AssgnRace : forall id e t, 
                has_type e t -> 
                has_type (EAssgn id CRace e) (seq_comp t TAtom)
| T_Let      : forall id e1 t1 e2 t2,
               has_type e1 t1 ->
               has_type e2 t2 ->
               has_type (ELet id e1 e2) (seq_comp t1 t2)
| T_If       : forall cond b1 b2 t1 t2 t3, 
               has_type cond t1 -> 
               has_type b1 t2 -> 
               has_type b2 t3 -> 
               has_type (EIf cond b1 b2) (seq_comp t1 (lub t2 t3))
| T_While    : forall cond t1 body t2,
               has_type cond t1 ->
               has_type body t2 ->
               has_type (EWhile cond body) 
                        (seq_comp t1 (iterative_closure (seq_comp t1 t2)))
(* We omit invoke *)
| T_Atomic   : forall e t,  
               has_type e t -> 
               t <> TTop ->
               has_type (EAtomic e) t
| T_InAtomic : forall e t,
               has_type e t ->
               t <> TTop ->
               has_type (EInAtomic e) t
(* We omit wrong, because we have no EWrong *).

Tactic Notation "ht_cases" tactic(first) ident(c) :=
  first;
  [ 
  Case_aux c "T_Const" | Case_aux c "T_SyncLoc" | Case_aux c "T_Function" | Case_aux c "T_Plus"
  | Case_aux c "T_Minus" | Case_aux c "T_Assert" | Case_aux c "T_NewLock" 
  | Case_aux c "T_Acquire" | Case_aux c "T_Release" | Case_aux c "T_Read"
  | Case_aux c "T_ReadRace" | Case_aux c "T_Assgn" | Case_aux c "T_AssgnRace"
  | Case_aux c "T_Let" | Case_aux c "T_If" | Case_aux c "T_While" 
  | Case_aux c "T_Atomic" | Case_aux c "T_InAtomic" ].

Hint Constructors has_type.

Fixpoint get_type (e: exp) : atom :=
  match e with 
    | EConst _ => TBoth
    | ESyncLoc _ => TBoth 
    | EFunction _ body => get_type body
    | EId _ CNone => TBoth
    | EId _ CRace => TAtom
    | EAssgn _ CNone e => seq_comp (get_type e) TBoth
    | EAssgn _ CRace e => seq_comp (get_type e) TAtom
    | ESeq e1 e2 => seq_comp (get_type e1) (get_type e2)
    | EAssert e  => (seq_comp (get_type e) (prim_type Assert))
    | EPlus ea eb => (seq_comp_many [get_type ea, get_type eb, prim_type Plus])
    | EMinus ea eb => (seq_comp_many [get_type ea, get_type eb, prim_type Plus])
    | ENewLock  _ => prim_type NewLock
    | EAcquire  _ => prim_type Acquire
    | ERelease  _ => prim_type Release
    | EApp _ _ _ => TTop (* Not dealing with application *)
    | EIf c b1 b2 => seq_comp (get_type c) (lub (get_type b1) (get_type b2))
    | EWhile c b => seq_comp (get_type c) (iterative_closure (seq_comp (get_type c) (get_type b)))
    | ELet _ _ _ => TTop (* Not dealing with application *)
    | EAtomic e  => get_type e
    | EInAtomic e => get_type e
  end.

Definition well_typed (et: thread * atom) : Prop :=
match et with
| ((TExpr e), a) =>  has_type e a
| (Wrong, TBoth) => True
| _ => False
end.

Inductive heap_consistent : heap -> exp -> Prop :=
  | H_Const    : forall h n, heap_consistent h (EConst n)
  | H_SyncLoc  : forall h id, heap_consistent h (ESyncLoc id)
  | H_Function : forall h lids e, 
                heap_consistent h e ->
                heap_consistent h (EFunction lids e)
  | H_Id       : forall h id c v p, 
                (lookup_heap h id) = Some (exist value v p) -> 
                heap_consistent h (EId id c)
  | H_Assgn    : forall h id c e, 
                heap_consistent h e ->
                heap_consistent h (EAssgn id c e)
  | H_Seq      : forall h e1 e2, 
                heap_consistent h e1 ->
                heap_consistent h e2 ->
                heap_consistent h (e1; e2)
  | H_Assert   : forall h e,
                heap_consistent h e ->
                heap_consistent h (EAssert e)
  | H_Plus     : forall h a b,
                heap_consistent h a ->
                heap_consistent h b ->
                heap_consistent h (EPlus a b)
  | H_Minus    : forall h a b,
                heap_consistent h a ->
                heap_consistent h b ->
                heap_consistent h (EMinus a b)
  | H_NewLock  : forall h id, heap_consistent h (ENewLock id)
  | H_Acquire  : forall h id, heap_consistent h (EAcquire id)
  | H_Release  : forall h id, heap_consistent h (ERelease id)
  (* | H_App      : forall h f F exps, heap_consistent h (EApp f F exps) *)
  | H_If       : forall h cond e1 e2,
                heap_consistent h cond ->
                heap_consistent h e1 ->
                heap_consistent h e2 ->
                heap_consistent h (IFE cond THEN e1 ELSE e2)
  | H_While    : forall h cond body, heap_consistent h (WHILE cond DO body)
  | H_Let      : forall h id e1 e2, 
                (lookup_heap h id) = None ->
                heap_consistent h e1 ->
                heap_consistent h e2 ->
                heap_consistent h (LET id ::= e1 IN e2)
  | H_Atomic   : forall h e, 
                heap_consistent h e -> 
                heap_consistent h (EAtomic e)
  | H_InAtomic : forall h e,
                heap_consistent h e ->
                heap_consistent h (EInAtomic e).

Hint Constructors heap_consistent.

Inductive sync_consistent : sync_state -> exp -> Prop :=
  | S_Const    : forall s n, sync_consistent s (EConst n)
  | S_SyncLoc  : forall s id, sync_consistent s (ESyncLoc id)
  | S_Function : forall s lids e, 
                sync_consistent s e ->
                sync_consistent s (EFunction lids e)
  | S_Id       : forall s id c, 
                 sync_consistent s (EId id c)
  | S_Assgn    : forall s id c e, 
                sync_consistent s e ->
                sync_consistent s (EAssgn id c e)
  | S_Seq      : forall s e1 e2, 
                sync_consistent s e1 ->
                sync_consistent s e2 ->
                sync_consistent s (e1; e2)
  | S_Assert   : forall s e,
                sync_consistent s e ->
                sync_consistent s (EAssert e)
  | S_Plus     : forall s a b,
                sync_consistent s a ->
                sync_consistent s b ->
                sync_consistent s (EPlus a b)
  | S_Minus    : forall s a b,
                sync_consistent s a ->
                sync_consistent s b ->
                sync_consistent s (EMinus a b)
  | S_NewLock  : forall s id, 
                s id = None ->
                sync_consistent s (ENewLock id)
  | S_Acquire  : forall s id tid, 
                s id = Some tid ->
                sync_consistent s (EAcquire id)
  | S_Release  : forall s id tid, 
                s id = Some tid ->
                sync_consistent s (ERelease id)
  (* | HApp      : forall s f F exps, sync_consistent s (EApp f F exps) *)
  | S_If       : forall s cond e1 e2,
                sync_consistent s cond ->
                sync_consistent s e1 ->
                sync_consistent s e2 ->
                sync_consistent s (IFE cond THEN e1 ELSE e2)
  | S_While    : forall s cond body, sync_consistent s (WHILE cond DO body)
  | S_Let      : forall s id e1 e2, 
                sync_consistent s e1 ->
                sync_consistent s e2 ->
                sync_consistent s (LET id ::= e1 IN e2)
  | S_Atomic   : forall s e, 
                sync_consistent s e -> 
                sync_consistent s (EAtomic e)
  | S_InAtomic : forall s e,
                sync_consistent s e ->
                sync_consistent s (EInAtomic e).

Hint Constructors sync_consistent.

Theorem assgn_progress : forall e T id c h s (ta tb : list (thread * atom)),
    has_type e T ->
    Forall well_typed ta ->
    Forall well_typed tb ->
    value e \/ (exists C ae e' h' s',
               D e C ae /\ [|h // s // ae ===> h' // s' // e'|] /\
               [| h // s // fst (split ta), e, fst (split tb) ===> 
                  h'// s'// fst (split ta), plug e' C, fst (split tb)|] /\
               Forall well_typed tb /\ Forall well_typed ta) ->
    exists C0 ae0 e' h' s',
     D (id % (c) ::= e) C0 ae0 /\
     [|h // s // ae0 ===> h' // s' // e'|] /\
     [| h // s // fst (split ta), id % (c) ::= e, fst (split tb) ===> 
        h'// s'// fst (split ta), plug e' C0, fst (split tb)|] /\
     Forall well_typed tb /\ Forall well_typed ta.
Proof with simpl; auto. intros.
inversion H2...
    SCase "e is a value". exists C_hole. exists (id % (c) ::= e). exists e. exists (HHeap e H3 id h). exists s. split...
    SCase "e is an exp". inversion_clear H3 as [C]. inversion_clear H4 as [ae]. inversion_clear H3 as [e'].  
                         inversion_clear H4 as [h']. inversion_clear H3 as [s']. 
                         inversion_clear H4. inversion_clear H5. inversion_clear H6.
                         exists (C_assgn id c C). exists ae. exists e'. exists h'. exists s'.
                         split... split... split...
      SSCase "===>". apply Step. apply SAssgn1 with (ae:=ae)...
Qed.

Definition env_consistent (h : heap) (s : sync_state) (e : exp) := heap_consistent h e /\ sync_consistent s e.

Ltac solve_R H := inversion H as [R]; exists R; solve_by_inversion_step auto.
Ltac solve_env H1 H2 H3 := inversion H1; unfold env_consistent; inversion H2; inversion H3; auto. 


Theorem progress_thread : 
  forall e T h s (ta tb : list (thread * atom)), 
    Forall well_typed ta ->
    Forall well_typed tb ->
    has_type e T ->
    (exists R, result_type e R) ->
    env_consistent h s e ->
    value e \/ exists C ae e' h' s', D e C ae /\ [| h // s // ae ===> h' // s' // e' |] /\
      [| h // s // fst (split ta), e, fst (split tb) ===>
         h' // s' // fst (split ta), (plug e' C), fst (split tb) |] /\ Forall well_typed tb /\ Forall well_typed ta.
Proof with simpl; auto.
  intros. 
  ht_cases (induction H1) Case. 
  Case "T_Const". left...
  Case "T_SyncLoc". left...
  Case "T_Function". left...
  Case "T_Plus". destruct IHhas_type1... solve_R H2. solve_env H3 H1 H4.
    SCase "value a". right. destruct IHhas_type2... solve_R H2. solve_env H3 H4 H5.
      SSCase "value b". inversion H2 as [R]; subst. inversion H5; subst. 
                        inversion H8; subst; try solve_by_inversion_step auto.
                        inversion H10; subst; try solve_by_inversion_step auto. exists C_hole. exists (EConst n e+ EConst n0).
                        exists (EConst (n + n0)). exists h. exists s. split... 
      SSCase "b is an exp". inversion_clear H4 as [C]. inversion_clear H5 as [ae]. inversion_clear H4 as [e']. 
                            inversion_clear H5 as [h']. inversion_clear H4 as [s'].
                            inversion_clear H5. inversion_clear H6. inversion_clear H7.
                            exists (C_plus2 a0 C). exists ae. exists e'. exists h'. exists s'.
                            split... split... split...
        SSSCase "===>". apply Step. apply SPlus2 with (ae:=ae)...
    SCase "a is an exp". right. inversion_clear H1 as [C]. inversion_clear H4 as [ae]. inversion_clear H1 as [e']. 
                                inversion_clear H4 as [h']. inversion_clear H1 as [s'].
                                inversion_clear H4. inversion_clear H5. inversion_clear H6.
                                exists (C_plus1 C b0). exists ae. exists e'. exists h'. exists s'.
                                split... split... split...
        SSSCase "===>". apply Step. apply SPlus1 with (ae:=ae)... 
  Case "T_Minus". destruct IHhas_type1... solve_R H2. solve_env H3 H1 H4. 
    SCase "value a". right. destruct IHhas_type2... solve_R H2.  solve_env H3 H4 H5. 
      SSCase "value b". inversion H2 as [R]; subst. inversion H5; subst.
                        inversion H8; subst; try solve_by_inversion_step auto.
                        inversion H10; subst; try solve_by_inversion_step auto. exists C_hole. exists (EConst n e- EConst n0).
                        exists (EConst (n - n0)). exists h. exists s. split... 
      SSCase "b is an exp". inversion_clear H4 as [C]. inversion_clear H5 as [ae]. inversion_clear H4 as [e']. 
                            inversion_clear H5 as [h']. inversion_clear H4 as [s'].
                            inversion_clear H5. inversion_clear H6. inversion_clear H7.
                            exists (C_minus2 a0 C). exists ae. exists e'. exists h'. exists s'.
                            split... split... split...
        SSSCase "===>". apply Step. apply SMinus2 with (ae:=ae)...
    SCase "a is an exp". right. inversion_clear H1 as [C]. inversion_clear H4 as [ae]. inversion_clear H1 as [e']. 
                                inversion_clear H4 as [h']. inversion_clear H1 as [s'].
                                inversion_clear H4. inversion_clear H5. inversion_clear H6.
                                exists (C_minus1 C b0). exists ae. exists e'. exists h'. exists s'.
                                split... split... split...
        SSSCase "===>". apply Step. apply SMinus1 with (ae:=ae)... 
  Case "T_Assert". right. destruct IHhas_type... inversion H2 as [R]. inversion H4; subst. exists te0... solve_env H3 H4 H5.
    SCase "value e". exists C_hole. exists (EAssert e). exists (EConst 0). exists h. exists s.
                     split... split... apply SAssert2... admit.
                     split... apply Step. apply SAssert2... admit.
    SCase "e is an exp". inversion_clear H4 as [C]. inversion_clear H5 as [ae]. inversion_clear H4 as [e'].
                         inversion_clear H5 as [h']. inversion_clear H4 as [s'].
                         inversion_clear H5. inversion_clear H6. inversion_clear H7.
                         exists (C_assert C). exists ae. exists e'. exists h'. exists s'.
                         split... split... split... apply Step. apply SAssert1 with (ae:=ae)...
  Case "T_NewLock". right. exists C_hole. exists (ENewLock id). exists (ESyncLoc id). exists h. exists (update_sync s id 0). 
                           inversion H3. inversion H4. split...
  Case "T_Acquire". right. exists C_hole. exists (EAcquire id). exists (ESyncLoc id). exists h. exists (update_sync s id 1).
                           inversion H3. inversion H4. split... split...
    SCase "===>". apply SAcquire. admit. split... split... apply SAcquire. admit. 
  Case "T_Release". right. exists C_hole. exists (ERelease id). exists (ESyncLoc id). exists h. exists (update_sync s id 0).
                           inversion H3. inversion H4. split... split...
    SCase "===>". apply SRelease with (tid:=tid)... split... 
                  apply Step. apply SRelease with (tid:=tid)...
  Case "T_Read". right. inversion H3; inversion H1. 
                        exists C_hole. exists (id %% CNone). exists v. exists h. exists s. 
                        split... split... apply SLookup with (p:=p0)... 
                        split... apply Step. apply SLookup with (p:=p0)...
  Case "T_ReadRace". right. inversion H3; inversion H1.
                        exists C_hole. exists (id %% CRace). exists v. exists h. exists s. 
                        split... split... apply SLookup with (p:=p0)... 
                        split... apply Step. apply SLookup with (p:=p0)...
  Case "T_Assgn". right. apply assgn_progress with (T:=t)... destruct IHhas_type... solve_R H2. solve_env H3 H4 H5. 
  SCase "T_ReadRace". right. apply assgn_progress with (T:=t)... destruct IHhas_type... solve_R H2. solve_env H3 H4 H5.
  SCase "T_Let". admit.
  SCase "T_If". right. destruct IHhas_type1... inversion H2; inversion H1;  exists tc... solve_env H3 H1 H4.
    SSCase "value cond". destruct cond; inversion H1; exists C_hole.
      SSSCase "EConst n". destruct n.
        SSSSCase "EConst 0". exists (IFE EConst 0 THEN b1 ELSE b2). exists b2. exists h. exists s. split... 
        SSSSCase "EConst n". exists (IFE EConst (S n) THEN b1 ELSE b2). exists b1. exists h. exists s.
                             split... split... 
                             eapply SIfV... discriminate. split... 
                             apply Step. apply SIfV... discriminate.
      SSSCase "ESyncLoc". exists (IFE ESyncLoc i0 THEN b1 ELSE b2). exists b1. exists h. exists s.
                          split... split... eapply SIfV... discriminate.
                          split... apply Step. apply SIfV... discriminate.
      SSSCase "EFunction". exists (IFE EFunction l cond THEN b1 ELSE b2). exists b1. exists h. exists s.
                           split... split... apply SIfV... discriminate.
                           split... apply Step. apply SIfV... discriminate.
    SSCase "cond is an exp". inversion_clear H1 as [C]. inversion_clear H4 as [ae]. inversion_clear H1 as [e']. 
                             inversion_clear H4 as [h']. inversion_clear H1 as [s'].
                             inversion_clear H4. inversion_clear H5. inversion_clear H6.
                             exists (C_if C b1 b2). exists ae. exists e'. exists h'. exists s'.
                             split... split... split...
      SSSCase "===>". apply Step. apply SIf with (ae:=ae)... 
  SCase "T_While". right. exists C_hole. exists (WHILE cond DO body).
                          exists (IFE cond THEN body; WHILE cond DO body ELSE EConst 0). 
                          exists h. exists s. split... 
  SCase "T_Atomic". right. exists C_hole. exists (EAtomic e). exists (EInAtomic e). exists h. exists s. split...
  SCase "T_InAtomic". right. destruct IHhas_type... solve_R H2. solve_env H3 H5 H6. 
    SSCase "value e". exists C_hole. exists (EInAtomic e). exists e. exists h. exists s. split... 
    SSCase "e is an exp". inversion_clear H5 as [C]. inversion_clear H6 as [ae]. inversion_clear H5 as [e']. 
                          inversion_clear H6 as [h']. inversion_clear H5 as [s']. 
                          inversion_clear H6. inversion_clear H7. inversion_clear H8.
                          exists (C_inatom C). exists ae. exists e'. exists h'. exists s'.
                          split... split... split...
      SSSCase "===>". apply Step. apply SInAtom1 with (ae:=ae)...
Qed.

Inductive finished : (thread * atom) -> Prop :=
| FExp   : forall e a, value e -> finished (TExpr e, a)
| FWrong : forall a, finished (Wrong, a).

Hint Constructors finished.

Lemma finished_noatom : forall l, 
                        Forall finished l -> 
                        contains_inatom_threads (fst (split l)) = false.
Proof with simpl; auto.
intros.
assert (forall (A :Type) (a : A) b, a::b = [a] ++ b); auto.
induction H; auto; rewrite H0; rewrite fst_split_comm2. inversion H...  
inversion H2; simpl... admit. (* Not doing functions *)
Qed.

Definition env_well_typed h s (et : thread * atom) : Prop :=
match et with
| ((TExpr e), a) =>  env_consistent h s e
| (Wrong, TBoth) => True
| _ => False
end.

Theorem progress :
  forall h s (ts : list (thread * atom)), 
    Forall well_typed ts ->
    Forall (env_well_typed h s) ts ->
    Forall finished ts \/ 
    exists ta tb e a, ts = ta ++ (TExpr e, a)::tb /\ (* result_type e R /\  *)
    exists C ae e' h' s', D e C ae /\
                            [| h // s // ae ===> h' // s' // e' |] /\
                            [| h // s // fst (split ta), e, fst (split tb) ===>> 
                               h'// s'// fst (split ta), (plug e' C), fst (split tb) |] /\ Forall well_typed ts.
Proof with simpl; auto. 
intros. induction H. left... destruct IHForall. inversion H0... destruct x. induction t. induction e. 
Case "EConst". left...
Case "ESyncLoc". left...
Case "EFunction". left...
Case "i %% c". right. exists []. exists l. exists (i0 %% c). exists a0.  split...
               exists C_hole. exists (i0 %% c). inversion H;  inversion H0; inversion H8; inversion H10. 
               SCase "CNone". exists v. exists h. exists s. split... split... 
                 SSCase "===>". apply SLookup with (p:=p0); auto. split.
                 SSCase "===>>". apply CoarseStep with (ta1:=[]) (ta2:=fst (split l)) (tb1:=[]) (tb2:=fst (split l))...
                   SSSCase "noatom ta2". apply finished_noatom...
                   SSSCase "noatom tb2". apply finished_noatom... 
                   SSSCase "===>". apply Step with (ta1:=[]) (ta2:=fst (split l)) (tb1:=[]) (tb2:=fst (split l)).
                                   apply SLookup with (p:=p0)...
                                   apply Forall_cons...
               SCase "CRace". exists v. exists h. exists s. split... split... 
                 SSCase "===>". apply SLookup with (p:=p0); auto. split.
                 SSCase "===>>". apply CoarseStep with (ta1:=[]) (ta2:=fst (split l)) (tb1:=[]) (tb2:=fst (split l))...
                   SSSCase "noatom ta2". apply finished_noatom...
                   SSSCase "noatom tb2". apply finished_noatom... 
                   SSSCase "===>". apply Step with (ta1:=[]) (ta2:=fst (split l)) (tb1:=[]) (tb2:=fst (split l)).
                                   apply SLookup with (p:=p0)...
                                   apply Forall_cons...
Case "i % c ::= e". right. exists []. exists l. exists (i0 % (c) ::= e). exists a0. split...
                    admit.
Case "e1; e2". admit.
Case "EAssert". admit.
Case "a + b". admit.
Case "a - b". admit.
Case "ENewLock". admit.
Case "EAcquire". admit.
Case "ERelease". admit.
Case "EApp". admit. (* Not doing functions *)
Case "EIf". admit.
Case "EWhile". admit.
Case "ELet". admit. 
Case "EAtomic". admit.
Case "EInAtomic". admit.
left...
right... inversion_clear H2 as [ta]. inversion_clear H3 as [tb]. inversion_clear H2 as [e]. inversion_clear H3 as [a].
exists (x::ta). exists tb. exists e. exists a. inversion_clear H2. split. rewrite H3. auto.
inversion_clear H4 as [C]. inversion_clear H2 as [ae]. inversion_clear H4 as [e']. inversion_clear H2 as [h']. inversion_clear H4 as [s']. inversion_clear H2. inversion_clear H5. inversion_clear H6.
exists C. exists ae. exists e'. exists h'. exists s'. split... split... split... inversion H5.
apply CoarseStep with (ta1:=fst (split (x::ta))) (ta2:=fst (split tb)) (tb1:=fst (split (x::ta))) (tb2:=fst (split tb)); subst.

 
admit. admit. admit. admit.
apply Step... admit.
Qed.

Lemma values_dont_step : forall h h' s s' e e' ta tb ta' tb',
  value e -> not ([| h // s // ta, e, tb ===>  h' // s' // ta', e', tb' |]).
Proof.
intros. inversion H. unfold not. intros.
Admitted.

(* Next enforces that either an expression steps, or it is a value *)
Inductive next : exp -> exp -> Prop :=
| NStep : forall e C ae e' h h' s s', 
          D e C ae -> 
          [| h // s // ae ===> h' // s' // e' |] ->
          [| h // s // e  ===> h' // s' // (plug e' C) |] ->
          next e e'
| NValue: forall e,
          value e ->
          next e e.
          
Theorem preservation_thread : forall T e e', 
  has_type e T ->
  next e e' ->
  has_type e' T.
Proof with simpl; auto.
  intros. generalize dependent e'. ht_cases (induction H) Case.
  Case "T_Const". intros. inversion H0... inversion H2...
  Case "T_SyncLoc". intros. inversion H0... inversion H2...
  Case "T_Function". intros. inversion H0... inversion H2...
  Case "T_Plus". admit.
  Case "T_Minus". admit.
  Case "T_Assert". admit. 
  (* intros. simpl. destruct te. simpl. apply IHhas_type. inversion H0. subst.  admit. admit; auto. simpl. *)
  (* stuck *)
  Case "T_NewLock". admit.
  Case "T_Acquire". admit.
  Case "T_Release". admit.
  Case "T_Read". admit.
  Case "T_ReadRace". admit.
  Case "T_Assgn". admit.
  Case "T_AssgnRace". admit.
  Case "T_Let". admit.
  Case "T_If". admit.
  Case "T_While". admit.
  Case "T_Atomic". admit.
  Case "T_InAtomic". admit.
Qed.



(* reordering functions and lemmas *)

Fixpoint move_right_l (l : list (exp * id)) (len : nat) : list (exp * id) :=
  match len with
    | 0 => []
    | S n =>
      match l with
        | [] => [] (* impossible *)
        | [a] => [a]
        | a1::(a2::tl) => 
          if (beq_id (snd a1) (snd a2)) then l
          else  match get_type (fst a1), get_type (fst a2) with
                  | TRight, TRight => a2::(move_right_l (a1::tl) n)
                  | TRight, TLeft => a2::(move_right_l (a1::tl) n)
                  | TRight, TBoth => a2::(move_right_l (a1::tl) n)
                  | TBoth, TRight => a2::(move_right_l (a1::tl) n)
                  | TBoth, TLeft => a2::(move_right_l (a1::tl) n)
                  | TBoth, TBoth => a2::(move_right_l (a1::tl) n)
                  | _,_ => l
                end
      end
  end.

Fixpoint move_right (l : list (exp * id)) : list (exp * id) :=
  move_right_l l (List.length l).

Fixpoint move_left_l (l : list (exp * id)) (len : nat) : list (exp * id) :=
  match len with
    | 0 => []
    | S n =>
      match l with
        | [] => [] (* impossible *)
        | [a] => [a]
        | a1::(a2::tl) => 
          if (beq_id (snd a1) (snd a2)) then l
          else  match get_type (fst a1), get_type (fst a2) with
                  | TLeft, TRight => a2::(move_left_l (a1::tl) n)
                  | TLeft, TLeft => a2::(move_left_l (a1::tl) n)
                  | TLeft, TBoth => a2::(move_left_l (a1::tl) n)
                  | TBoth, TRight => a2::(move_left_l (a1::tl) n)
                  | TBoth, TLeft => a2::(move_left_l (a1::tl) n)
                  | TBoth, TBoth => a2::(move_left_l (a1::tl) n)
                  | _,_ => l
                end
      end
  end.

Fixpoint move_left (l : list (exp * id)) : list (exp * id) :=
  rev (move_left_l (rev l) (List.length l)).

(* Takes in a list of expressions and ids that represents an execution trace, and reorders
   it according to the left and right movers. *)
Fixpoint reorder (l : list (exp * id)) : list (exp * id) := admit.

(* Finds an inatomic subexpression in t, if it exists *)
Fixpoint find_inatom (t : thread) : option exp := admit.

(* decomposes a program (list of threads) into a series of small steps, labelled by thread id *)
Fixpoint decomposition (ts : list thread) : (list (exp * id)) := admit.


(* We took out the heap because we know that everything in our heap is a TBoth, and thus don't
need to include it in the tc relation *)
Inductive tc : list thread -> Prop :=
| Typecheck : forall (h : heap) (s : sync_state) (tes : list (thread * atom)),
  Forall well_typed tes ->
  (forall (t : thread) (e : exp), In t (fst (split tes)) ->
    find_inatom t = Some (EInAtomic e) ->
    exists (context: C), t = TExpr (plug (EInAtomic e) context)) ->
  tc (fst (split tes)).



(* 

In English:

Forall programs P that final-step to S such that P decomposes into an execution 
trace E, if P typechecks, then there exists some P' that can final-step to S, and such
that P' decomposes to E' and E' is equivalent to the reordering of E. 

*)

Lemma reduction : forall (ts : list thread) (s : progstate) (e : list (exp * id)),
  many_steps (ProgState HEmpty empty_sync ts) s ->
  decomposition ts = e ->
  tc ts ->
  exists (ts' : list thread) (e' : list (exp * id)), 
    many_steps (ProgState HEmpty empty_sync ts') s /\ 
    decomposition ts' =  e' /\ 
    (reorder e) = e'. 
Admitted.
