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
Notation "x '%%' b" := (EId x b) (at level 70).
Notation "a ';' b" := (ESeq a b) (at level 80).
Notation "a 'e+' b" := (EPrim Plus [a, b]) (at level 70).
Notation "a 'e-' b" := (EPrim Minus [a, b]) (at level 70).
Notation "'IFE' x 'THEN' a 'ELSE' b" := (EIf x a b) (at level 80).
Notation "'WHILE' a 'DO' b" := (EWhile a b) (at level 60).
Notation "'LET' a '::=' b 'IN' c" := (ELet a b c) (at level 60).
Notation "'FORK' a" := (EFork a) (at level 60).

Inductive C  : Set :=
  | C_hole   : C
  | C_assgn  : id -> conflict -> C -> C
  | C_prim   : primitive -> list exp -> C -> list exp -> C
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
  | ae_prim  : forall prim vs, Forall value vs -> ae (EPrim prim vs)
  | ae_app   : forall f F vs, value f -> Forall value vs -> ae (EApp f F vs)
  | ae_fork  : forall e, ae (EFork e)
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
  | DSeq     : forall e1 C e1' e2,
                D e1 C e1' ->
                D (ESeq e1 e2) (C_seq C e2) e1'
  | DPrim     : forall p e e' vs C es,
                D e C e' ->
                D
                
                
  (EPrim p (vs ++ e::es)) (C_prim p vs C es) e'
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
  | C_prim  p vs cxt es     => EPrim p (vs ++ ((plug e cxt)::es))
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
  | Minus   => match vs with
                 |  (EConst a)::(EConst b)::[] => 
                      Some (exist value (EConst (a - b)) (VConst (a-b)), sync_heap)
                 | _ => None
               end
  | NewLock => None
  | Acquire => None
  | Release => None
end.

Check fold_left.

Fixpoint contains_inatom e : bool :=
  match e with 
    | EConst _ => false
    | ESyncLoc _ => false
    | EFunction _ e => contains_inatom e
    | EId _ _  => false
    | EAssgn _ _ e => contains_inatom e
    | ESeq e1 e2 => 
      contains_inatom e1 || contains_inatom e2
    | EPrim _ es => fold_left orb (map contains_inatom es) false
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
    | EFork e => contains_inatom e
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
  | SPrim1  : forall p vs e C ae e' es heap heap' sync sync' t t',
              Forall value vs ->
              D e C ae ->
              [| heap // sync // t, ae, t' ===> heap' // sync' // t, e', t' |] ->
              [| heap // sync // t, EPrim p (vs ++ (e::es)), t' ===> 
                 heap'// sync'// t, EPrim p (vs ++ ((plug e' C)::es)), t' |]
  | SPrim2  : forall p vs heap sync sync' v' pv t t',
              Forall value vs ->
              I p vs sync = Some (exist value v' pv, sync') ->
              [| heap // sync // t, EPrim p vs, t' ===>
                 heap // sync'// t, v', t' |]
  | SWrong  : forall p vs heap sync t t',
              Forall value vs ->
              I p vs sync = None ->
              step (ProgState heap sync (t ++ (TExpr (EPrim p vs))::t'))
                   (ProgState heap sync (t ++ Wrong::t'))
  | SApp1   : forall f C ae e' F es heap heap' sync sync' t t',
              D f C ae ->
              [| heap // sync // t, ae, t' ===> heap' // sync' // t, e', t' |] ->
              [| heap // sync // t, EApp f F es, t' ===>
                 heap'// sync'// t, EApp (plug e' C) F es, t' |]
  | SApp2   : forall ids vs e C ae e' F es body t t' heap sync heap' sync',
              D e C ae ->
              [| heap // sync // t, e, t' ===> heap' // sync' // t, e', t' |] ->
              [| heap // sync // t, EApp (EFunction ids body) F ((extract_exps vs) ++ e::es), t' ===>
                 heap' // sync' // t, EApp (EFunction ids body) F ((extract_exps vs) ++ e'::es), t' |]
  | SApp3   : forall ids vs v p F es body t t' heap sync,
              [| heap // sync // t, EApp (EFunction ids body) F ((extract_exps vs) ++ v::es), t' ===>
                 heap // sync // t, EApp (EFunction ids body) F ((extract_exps (vs ++ [exist value v p])) ++ es), t' |]
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

Definition  many_steps := refl_step_closure step.

Notation "'[|' ha '//' sa '//' ta1 ',' ea ',' ta2 '===>*' hb '//' sb '//' tb1 ',' eb ',' tb2 '|]'" := 
(many_steps (ProgState ha sa (ta1 ++ (TExpr ea)::ta2))
            (ProgState hb sb (tb1 ++ (TExpr eb)::tb2))) (at level 50, no associativity).


Example Example1 : forall heap sync_state t t', [| heap // sync_state // t, (EConst 1) e+ (EConst 2), t' ===>*
  heap // sync_state // t, EConst 3, t' |].
Proof with simpl; auto.
  intros.
  eapply rsc_step...
  eapply SPrim2...
Qed.

Example Example2 : forall heap sync t t',
  [| heap // sync // t, IFE (EConst 2) e+ (EConst 3) THEN (EConst 5) ELSE (EConst 6), t' ===>*
     heap // sync // t, IFE (EConst 5) THEN (EConst 5) ELSE (EConst 6), t' |].
Proof with simpl; auto.
  intros. 
  eapply rsc_step.
   eapply SIf...
   eapply SPrim2...
  eapply rsc_refl.
Qed.



Example Example3 : forall heap sync t t',
  [| heap // sync // t, IFE (EConst 2) e+ (EConst 3) THEN (EConst 5) ELSE (EConst 6), t' ===>*
     heap // sync // t, EConst 5, t' |].
Proof with simpl; auto.
  intros. 
  eapply rsc_step.
  eapply SIf...
  eapply SPrim2...
  eapply rsc_step.
    eapply SIfV...
  eauto.
Qed.

Definition X := Id 0.

Example Example4 : forall heap sync t t',
  [| (HHeap (EConst 1) (VConst 1) X heap) // sync // t, 
     WHILE (X %% (CNone)) DO (X % (CNone) ::= ((X %% (CNone)) e- (EConst 1))), t' ===>*
     (HHeap (EConst 0) (VConst 0) X (HHeap (EConst 1) (VConst 1) X heap)) // sync // t, EConst 0, t' |].
Proof with simpl; auto.
  intros.
  eapply rsc_step...
  eapply rsc_step.
    eapply SIf...
    eapply SLookup...
  eapply rsc_step...
  eapply rsc_step.
    eapply SSeq1...
    eapply SAssgn1...
    apply SPrim1 with (vs:=[]) (ae:=X %% CNone)...
    eapply SLookup...
  eapply rsc_step.
    eapply SSeq1... 
    eapply SAssgn1...
    eapply SPrim2...
  eapply rsc_step.
    eapply SSeq1...
  eapply rsc_step...
  eapply rsc_step...
  eapply rsc_step.
    eapply SIf...
    eapply SLookup...
  eauto.
Qed.

(* Things we would like to show here:
   1) The expression produced by decomposition is always an active expression.
   2)
*)
Lemma decomp : forall e, value e \/ (exists C, exists e', D e C e' /\ ae e').
Proof with simpl; auto.
  intros. 
  induction e.
  (* Case EConst *)
  left...
  (* Case ESyncLoc *)
  left...
  (* Case EFunction *)
  left...
  (* Case id %% c *)
  right... eauto.
  (* Case id % c ::= e *)
  right... destruct IHe; eauto. 
  destruct H. destruct H. destruct H. eauto.
  (* Case e1; e2 *)
  right... 
  destruct IHe1.
    (* Case value e1 *) 
    destruct IHe2. 
      (* Case value e2 *)
      eauto. 
      (* Case e2 contains an ae *)
      destruct H0. destruct H0. destruct H0. eauto.
    (* Case e1 contains an ae *)
    destruct H. destruct H. destruct H. eauto. 
  (* Case EPrim *)
    admit.
  (* Case EApp *)
  admit. (* We might not do functions *)
  (* Case EIf *)
  right. destruct IHe1. 
    (* The condition is a value *)
    eauto.
    (* The condition contains an ae *)
    inversion H.  inversion H0. inversion H1. eauto.
  (* Case EWhile *)
  admit. (* While desugars, so there's no real active expression here *)
  (* Case ELet *)
  right. destruct IHe1. 
    (* The expression is a value *)
    eauto.
    (* The expression contains an ae *)
    inversion H. inversion H0. inversion H1. eauto.
  (* Case EFork *)
  right. eauto.
  (* Case EAtomic *)
  right. eauto.
  (* Case EInAtomic *)
  right. inversion IHe. 
    (* expression is a value *)
    eauto.
    (* expression contains an ae *)
    inversion H. inversion H0. inversion H1. eauto.
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

Inductive has_type : heap -> sync_state -> exp -> atom -> Prop := 
(* | T_subtyp    :  *)
| T_Const     : forall h s n, has_type h s (EConst n) TBoth
| T_SyncLoc   : forall h s id, has_type h s (ESyncLoc id) TBoth
| T_Prim      : forall h s p es ts,
  Forall2 (has_type h s) es ts -> 
  has_type h s (EPrim p es) (seq_comp_many (ts ++ [prim_type p]))
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
| T_Fork     : forall h s e t,
  has_type h s e t -> 
  has_type h s (EFork e) TAtom
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
    SCase "T_Prim". subst. apply T_Prim. induction H. auto. apply Forall2_cons. 
      (* No induction hypothesis. So sad *) admit. admit.
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
    SCase "T_Fork". eauto.
    SCase "T_Atomic". eauto.
    SCase "T_Inatomic". eauto.
  Case "Wrong". destruct a; auto.
Qed.

Theorem progress_thread : 
  forall e T h s (ta tb : list (thread * atom)), 
    Forall (well_typed h s) ta ->
    Forall (well_typed h s) tb ->
    has_type h s e T ->
    value e \/ exists e' h' s' (tb' : list (thread * atom)), 
      [| h // s // fst (split ta), e, fst (split tb) ===> 
         h' // s' // fst (split ta), e', fst (split tb') |] /\ Forall (well_typed h' s') tb' /\ Forall (well_typed h' s') ta.
Proof with simpl; auto.
  intros. 
  induction H1.
  Case "T_Const". left...
  Case "T_SyncLoc". left...
  Case "T_Prim". right. admit.
  (* Case "EFunction". left... *)
  Case "T_Read". right. exists v. exists h. exists s. exists tb. split. eapply SLookup with (p:=p0)... split...
  Case "T_ReadRace". right; exists v; exists h; exists s; exists tb. split. eapply SLookup with (p:=p0)... split...
  Case "EAssgn". right. destruct IHhas_type...
     exists e. exists (HHeap e H2 id h). exists s. exists tb. split. apply SAssgn2... split. induction tb. auto. apply Forall_cons. eapply heap_change_well_typed. inversion H0... auto. 
       inversion H1; subst; try inversion H2... apply IHtb. inversion H0; subst. assumption. 
     inversion H0 as [e']. exists e'. 
     inversion H1 as [h']. exists h'. 
     inversion H2 as [s']. exists s'. 
     inversion H3 as [tb']. exists tb'.
     Check SAssgn1.
     apply SAssgn1.
     repeat esplit. eapply SAssgn1... 

  Case "ESeq". right. (* repeat esplit. eapply SSeq1...  *) admit.
  Case "EPrim". right. induction l. inversion H. inversion H3. subst. repeat esplit. eapply SPrim2... 
  
 (* generalize dependent h'. *)
 (* generalize dependent s'. *)
 (* generalize dependent ta'. *)
 (* generalize dependent tb'. *)
  (* exists (extract_exp (lookup_heap h i0)). *)
Admitted.
Qed.
 
  