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
  fold_left 
  orb 
  (map (fun t => match t with 
                  | TExpr e => contains_inatom e
                  | _ => false
                end) ts)
  false.



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
  | SAssert: forall heap sync e, 
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


Inductive atom : Type  := 
| TTop : atom
| TAtom : atom
| TLeft : atom
| TRight : atom
| TBoth : atom.

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

Inductive has_type : heap -> sync_state -> exp -> atom -> Prop := 
(* | T_subtyp    :  *)
| T_Const     : forall h s n, has_type h s (EConst n) TBoth
| T_SyncLoc   : forall h s id, has_type h s (ESyncLoc id) TBoth
| T_Plus      : forall a b h s ta tb, 
                has_type h s a ta ->
                has_type h s a tb ->
                has_type h s (EPlus a b) (seq_comp_many [ta, tb, prim_type Plus])
| T_Minus     : forall a b h s ta tb, 
                has_type h s a ta ->
                has_type h s a tb ->
                has_type h s (EMinus a b) (seq_comp_many [ta, tb, prim_type Minus])
| T_Assert    : forall e h s te,
                has_type h s e te ->
                has_type h s (EAssert e) (seq_comp te (prim_type Assert))
| T_NewLock   : forall id h s,
                has_type h s (ENewLock id) (prim_type NewLock)
| T_Acquire   : forall id h s,
                has_type h s (EAcquire id) (prim_type Acquire)
| T_Release   : forall id h s,
                has_type h s (ERelease id) (prim_type Release)
(* | T_Fun       : forall  *)
| T_Read      : forall id h s,
  (exists v p, (lookup_heap h id) = Some (exist value v p)) -> 
  has_type h s (EId id CNone) TBoth
| T_ReadRace  : forall id h s, 
  (exists v p, (lookup_heap h id) = Some (exist value v p)) -> 
  has_type h s (EId id CRace) TAtom
| T_Assgn     : forall id h s e t, 
  has_type h s e t -> 
  has_type h s (EAssgn id CNone e) (seq_comp t TBoth)
| T_AssgnRace : forall id h s e t, 
  has_type h s e t -> 
  has_type h s (EAssgn id CRace e) (seq_comp t TAtom)
| T_Let      : forall id h s e1 t1 e2 t2,
  (lookup_heap h id) = None ->
  has_type h s e1 t1 ->
  has_type h s e2 t2 ->
  has_type h s (ELet id e1 e2) (seq_comp t1 t2)
| T_If       : forall h s cond b1 b2 t1 t2 t3, 
  has_type h s cond t1 -> 
  has_type h s b1 t2 -> 
  has_type h s b2 t3 -> 
  has_type h s (EIf cond b1 b2) (seq_comp t1 (lub t2 t3))
| T_While    : forall h s cond t1 body t2,
  has_type h s cond t1 ->
  has_type h s body t2 ->
  has_type h s
  (EWhile cond body) 
  (seq_comp t1 (iterative_closure (seq_comp t1 t2)))
(* We omit invoke *)
| T_Atomic   : forall h s e t,  
  has_type h s e t -> 
  t <> TTop ->
  has_type h s (EAtomic e) t
| T_InAtomic    : forall h s e t,  
  has_type h s e t -> 
  t <> TTop ->
  has_type h s (EInAtomic e) t
(* We omit wrong, because we have no EWrong *).

Hint Constructors has_type.

Definition well_typed (h:heap) (s:sync_state) (et: thread * atom) : Prop :=
match et with
| ((TExpr e), a) =>  has_type h s e a
| (Wrong, TBoth) => True
| _ => False
end.

Lemma heap_change_well_typed : 
  forall h s et id e p, 
    well_typed h s et -> 
    value e ->
    has_type h s e TBoth ->
    well_typed (HHeap e p id h) s et.
Proof.
  intros h s (t,a) id e_new e_new_evidence WT V HT.
  destruct t. 
  Case "TExpr". simpl well_typed in *. induction WT.
    SCase "T_Const". subst. auto.
    SCase "T_SyncLoc". subst. auto.
    SCase "T_Prim". subst. apply T_Prim with (tid:=tid) (v:=v) (s':=s'). inversion H. auto. apply Forall2_cons. 
      (* No induction hypothesis. So sad *) admit. admit. auto.
    SCase "T_Read". subst. apply T_Read. simpl lookup_heap. destruct beq_id. 
      SSCase "ids are equal". exists e_new. exists e_new_evidence. reflexivity.
      SSCase "ids aren't equal". assumption.
    SCase "T_ReadRace". subst. apply T_ReadRace. simpl  lookup_heap. destruct beq_id.
      SSCase "ids are equal". exists e_new. exists e_new_evidence. reflexivity.
      SSCase "ids aren't equal". assumption;
    SCase "T_Assgn". eauto.
    SCase "T_AssgnRace". eauto.
    SCase "T_Let". admit. (* Not dealing with lets for the time being *)
    SCase "T_IF". eauto.
    SCase "T_While". eauto.
    SCase "T_Atomic". eauto.
    SCase "T_Inatomic". eauto.
  Case "Wrong". destruct a; auto.
Qed.

Lemma sync_change_well_typed : 
  forall h s s' et, 
    well_typed h s et -> 
    well_typed h s' et.
Proof with simpl; auto.
intros. induction et as [e t]. induction e.
simpl in *.
Case "TExpr e". induction H; auto.
  SCase "EPrim". inversion H0. 
    SSCase "has_type". Check T_Prim. apply T_Prim with (tid:=tid) (v:=v) (s':=s'0). 
      SSSCase "Forall2". inversion H; subst... apply Forall2_cons. admit. admit. 
      SSSCase "Forall". split; auto. admit.
Case "Wrong". induction t; inversion H. auto.
Qed.


Theorem assgn_progress : forall e T id c h s (ta tb : list (thread * atom)),
    has_type h s e T ->
    Forall (well_typed h s) ta ->
    Forall (well_typed h s) tb ->
    value e \/ (exists (e' : exp) (h' : heap) (s' : sync_state),
                [|h // s // fst (split ta), e, fst (split tb) ===> 
                  h'// s'// fst (split ta), e', fst (split tb)|] /\ 
                Forall (well_typed h' s') tb /\ 
                Forall (well_typed h' s') ta) ->
    (exists (e' : exp) (h' : heap) (s' : sync_state),
       [|h // s // fst (split ta), id % (c) ::= e, 
         fst (split tb) ===> h' // s' // fst (split ta), e', fst (split tb)|] /\
         Forall (well_typed h' s') tb /\ 
         Forall (well_typed h' s') ta).
Proof with simpl; auto. intros.
inversion H2...
    SCase "e is a value". exists e. exists (HHeap e H3 id h). exists s. split. 
      SSCase "===>". apply Step. apply SAssgn2...  split.
      SSCase "tb is well-typed". induction tb.
        SSSCase "tb = []"... 
        SSSCase "tb = a0::tb'". apply Forall_cons. eapply heap_change_well_typed. 
          SSSSCase "a0 is well-typed". solve_by_inversion_step auto.
          SSSSCase "value e"... inversion H1; subst; try inversion H2... 
          SSSSCase "e is TBoth".
            inversion H; subst; try inversion H3... 
            inversion H; subst; try inversion H3... 
          SSSSCase "tb is well-typed w/ new heap". apply IHtb; inversion H1... 
      SSCase "ta is well-typed". induction ta.
        SSSCase "tb = []"...
        SSSCase "tb = a0::tb'". apply Forall_cons. apply heap_change_well_typed.
          SSSSCase "a0 is well-typed". solve_by_inversion_step auto.
          SSSSCase "value e"...
          SSSSCase "e is TBoth".
            inversion H; subst; try inversion H3...
            inversion H; subst; inversion H0; apply IHta; auto.
    SCase "e is an exp". inversion_clear H3 as [e'].  inversion_clear H4 as [h']. 
                         inversion_clear H3 as [s']. exists (id % (c) ::= e'). exists h'. exists s'. 
                         split. inversion_clear H4.
      SSCase "===>". apply Step. admit.
      SSCase "ta & tb are well-typed". inversion H4...
Qed.

Theorem progress_thread : 
  forall e T h s (ta tb : list (thread * atom)), 
    Forall (well_typed h s) ta ->
    Forall (well_typed h s) tb ->
    has_type h s e T ->
    value e \/ exists e' h' s', 
      [| h // s // fst (split ta), e, fst (split tb) ===> 
         h' // s' // fst (split ta), e', fst (split tb) |] /\ Forall (well_typed h' s') tb /\ Forall (well_typed h' s') ta.
Proof with simpl; auto.
  intros. 
  induction H1.
  Case "T_Const". left...
  Case "T_SyncLoc". left...
  Case "T_Prim". right. destruct v. exists x. exists h. exists s'. split. 
    SCase "===>". apply Step. inversion H2. apply SPrim2 with (pv:=v) (tid:=tid). auto. apply H4. split. 
    SCase "tb is well-typed". induction tb... inversion H0. apply Forall_cons. 
      SSCase "a0 is well-typed". apply sync_change_well_typed with (s:=s)...
      SSCase "tb' is well-typed".  apply IHtb...
    SCase "ta is well-typed". induction ta... inversion H. apply Forall_cons. 
      SSCase "a0 is well-typed". apply sync_change_well_typed with (s:=s)...
      SSCase "tb' is well-typed".  apply IHta...
  (* Case "EFunction". left... *)
  Case "T_Read". right. inversion H1 as [v]. inversion H2 as [p].
                        exists v. exists h. exists s. split. 
                        apply Step. eapply SLookup with (p:=p)... split...
  Case "T_ReadRace". right. inversion H1 as [v]. inversion H2 as [p]. 
                            exists v. exists h. exists s. split. 
                            apply Step. eapply SLookup with (p:=p)... split...
  Case "T_Assgn". right. apply assgn_progress with (T:=t)... 
  SCase "T_ReadRace". right. apply assgn_progress with (T:=t)...
  SCase "T_Let". admit.
  SCase "T_If". right. destruct IHhas_type1...
    SSCase "value cond". destruct cond; inversion H1.
      SSSCase "EConst n". destruct n.
        SSSSCase "EConst 0". exists b2. exists h. exists s. split. apply Step. eapply SIfZ... auto.
        SSSSCase "EConst n". exists b1. exists h. exists s. split. apply Step. eapply SIfV... discriminate. auto.
      SSSCase "ESyncLoc". exists b1. exists h. exists s. split. apply Step. eapply SIfV... discriminate. auto.
      SSSCase "EFunction". exists b1. exists h. exists s. split. apply Step. eapply SIfV... discriminate. auto.
    SSCase "cond is an exp". inversion_clear H1 as [e']. inversion_clear H2 as [h']. 
                             inversion_clear H1 as [s']. inversion_clear H2 as [tb']. inversion H1.
                             exists (IFE e' THEN b1 ELSE b2). exists h'. exists s'. split. 
      SSSCase "===>". admit.
      SSSCase "tb' & ta are well-typed". solve_by_inversion_step auto.
  SCase "T_While". right. exists (IFE cond THEN body; WHILE cond DO body ELSE EConst 0). exists h. exists s. split; auto.
  SCase "T_Atomic". right. exists (EInAtomic e). exists h. exists s. split. 
    SSCase "===>". apply Step. eapply SAtomic.
    SSCase "ta & ta are well-typed". destruct IHhas_type...
  SCase "T_InAtomic". right. destruct IHhas_type... 
    SSCase "value e". exists e. exists h. exists s. split.
      SSSCase "===>". apply Step. eapply SInAtom2...
      SSSCase "ta & tb are well-typed"...
    SSCase "e is an exp". inversion_clear H3 as [e']. inversion_clear H4 as [h']. 
                          inversion_clear H3 as [s']. inversion_clear H4 as [tb'].
                          exists (EInAtomic e'). exists h'. exists s'. split.
      SSSCase "===>". admit.
      SSSCase "ta & tb are well-typed". inversion H3...
Qed.

 
Lemma values_dont_step : forall h h' s s' e e' ta tb ta' tb',
  value e -> not ([| h // s // ta, e, tb ===>  h' // s' // ta', e', tb' |]).
Proof.
intros. inversion H. unfold not. intros.
Admitted.

(* Lemma values_dont_step : forall h h' s s' e e' ta tb ta' tb',  *)
(*   value e ->  *)
(*   (not ([| h // s // ta, e, tb ===>  h' // s' // ta', e', tb' |])) \/ *)
(*   exists  *)
(* (*  *) *)

Theorem preservation_thread : forall h s t t' ta tb T,
  well_typed h s ((TExpr t), T) ->
  value t \/ exists h' s' tb',
  [| h // s // ta, t, tb ===> h' // s' // ta, t', tb' |] ->
  well_typed h s ((TExpr t'),T) \/ value t.
Proof.
intros. generalize dependent t'. induction H. left. exists h. exists s. exists tb. intros. apply values_dont_step in H. inversion H. apply VConst.
exists h. exists s. exists tb. intros. apply values_dont_step in H. inversion H. apply VSyncLoc.

admit.
Qed.
 
  


