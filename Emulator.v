Require Import IPR.Common.
Require Import IPR.Machine.
Require Import IPR.Tactics.

Require Import List.
Require Import Program.Equality.

Inductive eproc (S I O : Type) : Type -> Type :=
| ECall : I -> eproc _ _ _ O
| EGet : eproc _ _ _ S
| EPut : S -> eproc _ _ _ unit
| ERet : forall T, T -> eproc _ _ _ T
| EBind : forall T T1, eproc _ _ _ T1 -> (T1 -> eproc _ _ _ T) -> eproc _ _ _ T
| EWhile : eproc _ _ _ bool -> eproc _ _ _ unit -> eproc _ _ _ unit.

Arguments ECall [S I O].
Arguments EGet {S I O}.
Arguments EPut {S I O}.
Arguments ERet [S I O T].
Arguments EBind [S I O T T1].
Arguments EWhile [S I O].

Declare Scope eproc_scope.
Delimit Scope eproc_scope with eproc.
Notation "x <- p1 ; p2" := (EBind p1 (fun x => p2))
                            (at level 60, right associativity) : eproc_scope.
Notation "p1 ;; p2" := (_ <- p1; p2)%eproc (at level 60, right associativity) : eproc_scope.
Notation "p1 >>= p2" := (EBind p1 p2) (at level 50, left associativity, only parsing) : eproc_scope.
Notation "'Ret'" := (ERet) (at level 10) : eproc_scope.
Notation "'Call' a" := (ECall a) (at level 10) : eproc_scope.
Notation "'Get'" := (EGet) (at level 10) : eproc_scope.
Notation "'Put'" := (EPut) (at level 10) : eproc_scope.
Notation "'While'" := (EWhile) (at level 10) : eproc_scope.

Local Open Scope eproc.

Inductive eexec {S Il Ir Ol Or : Type} (M : machine (Il + Ir) (Ol + Or)) :
  forall T, eproc S Ir Or T -> (M.(state) * S) -> result T (M.(state) * S) -> Prop :=
| EexecCall : forall ms es i ms' o,
    M.(step) ms (inr i) (Result (inr o) ms') ->
    eexec _ _ (Call i) (ms, es) (Result o (ms', es))
| EexecGet : forall ms es,
    eexec _ _ (Get) (ms, es) (Result es (ms, es))
| EexecPut : forall (es' : S) ms es,
    eexec _ _ (Put es') (ms, es) (Result tt (ms, es'))
| EexecRet : forall T (v : T) s,
    eexec _ _ (Ret v) s (Result v s)
| EexecBind : forall T T1 (p : eproc _ _ _ T1) (p' : T1 -> eproc _ _ _ T) s v s' res,
    eexec _ _ p s (Result v s') ->
    eexec _ _ (p' v) s' res ->
    eexec _ _ (p >>= p') s res
| EexecWhileTrue : forall (g : eproc _ _ _ bool) (b : eproc _ _ _ unit) s s' s'' res,
    eexec _ _ g s (Result true s') ->
    eexec _ _ b s' (Result tt s'') ->
    eexec _ _ (While g b) s'' res ->
    eexec _ _ (While g b) s res
| EexecWhileFalse : forall (g : eproc _ _ _ bool) (b : eproc _ _ _ unit) s s',
    eexec _ _ g s (Result false s') ->
    eexec _ _ (While g b) s (Result tt s')
.

Arguments eexec [S Il Ir Ol Or].

Create HintDb emulator.
Hint Constructors eexec : emulator.

Ltac rinv_eexec_head :=
  repeat lazymatch goal with
    | [ H : eexec _ _ (ECall _) _ _ |- _ ] => inv_exec H
    | [ H : eexec _ _ (EGet) _ _ |- _ ] => inv_exec H
    | [ H : eexec _ _ (EPut _) _ _ |- _ ] => inv_exec H
    | [ H : eexec _ _ (ERet _) _ _ |- _ ] => inv_exec H
    | [ H : eexec _ _ (EBind _ _) _ _ |- _ ] => inv_exec H
    | [ H : eexec _ _ (EWhile _ _) _ _ |- _ ] => inv_exec H
    end.

(* emulates M1's behavior in terms of M2; has emulator state type S *)
Record emulator (I2 O2 I1 O1 : Type) :=
  {
    estate : Type;
    einit : estate;
    estep : I1 -> eproc estate I2 O2 O1
  }.

Arguments estate [I2 O2 I1 O1].
Arguments einit [I2 O2 I1 O1].
Arguments estep [I2 O2 I1 O1].

Fixpoint expand_state {S I O T} (S' : Type)
  (p : eproc S I O T) : eproc (S' * S) I O T :=
  match p with
  | Call i => Call i
  | Ret v => Ret v
  | Get => (x <- Get; Ret (snd x))
  | Put s => (s's <- Get; Put (fst s's, s))
  | p1 >>= p2 => (x <- expand_state S' p1; expand_state S' (p2 x))
  | While g b => While (expand_state S' g) (expand_state S' b)
  end.

Fixpoint inline_calls {S1 I2 O2 T S2 I3 O3 : Type}
                      (p : eproc S1 I2 O2 T)
                      (e2 : I2 -> eproc S2 I3 O3 O2) :
  eproc (S1 * S2) I3 O3 T :=
  match p with
  | Call i => expand_state S1 (e2 i)
  | Ret v => Ret v
  | Get => (ss' <- Get; Ret (fst ss'))
  | Put s => (ss' <- Get; Put (s, snd ss'))
  | p1 >>= p2 => (x <- inline_calls p1 e2; inline_calls (p2 x) e2)
  | While g b => While (inline_calls g e2) (inline_calls b e2)
  end.

Definition emulator_compose {I1 O1 I2 O2 I3 O3 : Type}
                            (e1 : emulator I3 O3 I2 O2)
                            (e2 : emulator I2 O2 I1 O1) : emulator I3 O3 I1 O1 :=
  {|
    estate := (e2.(estate) * e1.(estate))%type;
    einit := (e2.(einit), e1.(einit));
    estep := fun i => inline_calls (e2.(estep) i) e1.(estep)
  |}.

Notation "e1 ∘ e2" := (emulator_compose e1 e2) (at level 65, no associativity) : eproc_scope.

Lemma expand_state_preserve :
  forall (Il Ol I1 O1 I2 O2 I3 O3 ES32 S21 : Type)
    (M3 : machine (Il + I3) (Ol + O3))
    (e32i : eproc ES32 I3 O3 O2)
    o ms es2 ms' es2' es1,
    eexec M3 O2 e32i (ms, es2) (Result o (ms', es2')) ->
    eexec M3 O2 (expand_state S21 e32i) (ms, (es1, es2)) (Result o (ms', (es1, es2'))).
Proof.
  intros Il Ol I1 O1 I2 O2 I3 O3 ES32 S21 M3 e32i o ms es2 ms' es2' es1 H.
  dependent induction H; eauto with emulator.
  - (* bind *)
    destruct s'.
    specialize (IHeexec1 _ _ _ _ _ es1 eq_refl eq_refl).
    specialize (IHeexec2 _ _ _ _ _ es1 eq_refl eq_refl).
    eauto with emulator.
  - (* while *)
    destruct s', s''.
    specialize (IHeexec1 _ _ _ _ _ es1 eq_refl eq_refl).
    specialize (IHeexec2 _ _ _ _ _ es1 eq_refl eq_refl).
    specialize (IHeexec3 _ _ _ _ _ es1 eq_refl eq_refl).
    eauto with emulator.
Qed.

Lemma eexec_while_ind :
  forall (Il Ol I1 O1 S : Type) (M : machine (Il + I1) (Ol + O1)) (g : eproc S I1 O1 bool) (b : eproc S I1 O1 unit)
    (P : M.(state) -> S -> M.(state) -> S -> Prop),
    (forall ms es ms' es', eexec M bool g (ms, es) (Result false (ms', es')) -> P ms es ms' es') ->
    (forall ms es ms1 es1 ms2 es2 ms' es', eexec M bool g (ms, es) (Result true (ms1, es1)) ->
                      eexec M unit b (ms1, es1) (Result tt (ms2, es2)) ->
                      eexec M unit (While g b) (ms2, es2) (Result tt (ms', es')) ->
                      P ms2 es2 ms' es' ->
                      P ms es ms' es') ->
    forall ms es ms' es',
      eexec M unit ((While) g b) (ms, es) (Result tt (ms', es')) ->
      P ms es ms' es'.
Proof.
  intros Il Ol I1 O1 S M g b P Hfalse Htrue ms es ms' es' Hexec.
  dependent induction Hexec.
  - destruct s' as (? & ?), s'' as (? & ?).
    specialize (IHHexec3 _ _ _ Hfalse Htrue _ _ _ _ eq_refl JMeq_refl eq_refl JMeq_refl).
    specialize (Htrue _ _ _ _ _ _ _ _ Hexec1 Hexec2 Hexec3).
    auto.
  - auto.
Qed.

Lemma expand_state_preserve' :
  forall (Il Ol O2 I3 O3 ES32 S21 : Type)
    (M3 : machine (Il + I3) (Ol + O3))
    (e32i : eproc ES32 I3 O3 O2)
    o ms es2 ms' es2' es1 es1',
    eexec M3 O2 (expand_state S21 e32i) (ms, (es1, es2)) (Result o (ms', (es1', es2'))) ->
    eexec M3 O2 e32i (ms, es2) (Result o (ms', es2')) /\ es1 = es1'.
Proof.
  intros Il Ol O2 I3 O3 ES32 S21 M3 e32i.
  induction e32i; intros; simpl in *.
  - rinv_eexec_head.
    eauto with emulator.
  - rinv_eexec_head.
    eauto with emulator.
  - rinv_eexec_head.
    eauto with emulator.
  - rinv_eexec_head.
    eauto with emulator.
  - (* bind *)
    rinv_eexec_head.
    destruct s' as (?, (?, ?)).
    destruct (H _ _ _ _ _ _ _ _ H8).
    destruct (IHe32i _ _ _ _ _ _ _ H6).
    subst.
    eauto with emulator.
  - (* while *)
    remember (expand_state S21 e32i1) as g eqn:Hg; clear Hg.
    remember (expand_state S21 e32i2) as b eqn:Hb; clear Hb.
    remember (es1, es2) as es.
    remember (es1', es2') as es'.
    replace es1 with (fst es) by (subst; auto).
    replace es1' with (fst es') by (subst; auto).
    replace es2 with (snd es) by (subst; auto).
    replace es2' with (snd es') by (subst; auto).
    clear Heqes.
    clear Heqes'.
    clear es1 es2 es1' es2'.
    destruct o.
    eapply eexec_while_ind with (P := fun ms es ms' es' => eexec M3 unit (While e32i1 e32i2) (ms, snd es) (Result tt (ms', snd es')) /\ fst es = fst es'); [ | | exact H ].
    + clear ms ms' es es' H.
      intros.
      destruct es, es'.
      destruct (IHe32i1 _ _ _ _ _ _ _ H).
      eauto with emulator.
    + clear ms ms' es es' H.
      intros.
      destruct es, es1, es2, es'.
      destruct (IHe32i1 _ _ _ _ _ _ _ H).
      destruct (IHe32i2 _ _ _ _ _ _ _ H0).
      destruct H2.
      subst.
      eauto with emulator.
Qed.

Inductive eexec_trace {S Il Ir Ol Or : Type} :
  forall T, eproc S Ir Or T -> S -> trace (Il + Ir) (Ol + Or) -> result T S -> Prop :=
| EexecTraceCall : forall es i o,
    eexec_trace _ (Call i) es (IO (inr i) (inr o) :: nil) (Result o es)
| EexecTraceRet : forall T (v : T) es,
    eexec_trace _ (Ret v) es nil (Result v es)
| EexecTraceGet : forall es,
    eexec_trace _ (Get) es nil (Result es es)
| EexecTracePut : forall es es',
    eexec_trace _ (Put es') es nil (Result tt es')
| EexecTraceBind : forall T T1 (p : eproc _ _ _ T1) (p' : T1 -> eproc _ _ _ T) es tr1 v es' tr2 res,
    eexec_trace _ p es tr1 (Result v es') ->
    eexec_trace _ (p' v) es' tr2 res ->
    eexec_trace _ (p >>= p') es (tr1 ++ tr2) res
| EexecTraceWhileTrue : forall (g : eproc _ _ _ bool) (b : eproc _ _ _ unit) es tr1 es' tr2 es'' tr3 res,
    eexec_trace _ g es tr1 (Result true es') ->
    eexec_trace _ b es' tr2 (Result tt es'') ->
    eexec_trace _ (While g b) es'' tr3 res ->
    eexec_trace _ (While g b) es (tr1 ++ tr2 ++ tr3) res
| EexecTraceWhileFalse : forall (g : eproc _ _ _ bool) (b : eproc _ _ _ unit) es tr es',
    eexec_trace _ g es tr (Result false es') ->
    eexec_trace _ (While g b) es tr (Result tt es')
.

Arguments eexec_trace [S Il Ir Ol Or].

Theorem eexec_eexec_trace : forall (S Ir Il Or Ol : Type) (T : Type) (p : eproc S Ir Or T)
                              (M : machine (Il + Ir) (Ol + Or)) s es res s' es',
  eexec M _ p (s, es) (Result res (s', es')) <->
  ( exists tr,
    execution M s tr s' /\
    eexec_trace _ p es tr (Result res es') ).
Proof.
  split.
  - intro H.
    dependent induction H.
    + eexists; split; [ | econstructor ].
      econstructor; eauto. econstructor.
    + eexists; split; [ | econstructor ].
      econstructor.
    + eexists; split; [ | econstructor ].
      econstructor.
    + eexists; split; [ | econstructor ].
      econstructor.
    + destruct s'0 as [s'0 es'0].
      specialize (IHeexec1 _ _ _ _ _ eq_refl eq_refl).
      specialize (IHeexec2 _ _ _ _ _ eq_refl eq_refl).
      destruct IHeexec1 as (io1 & He1 & Hi1).
      destruct IHeexec2 as (io2 & He2 & Hi2).
      eexists; split; [ | econstructor ]; eauto.
      eapply execution_join; eauto.
    + destruct s'0 as [s'0 es'0].
      destruct s'' as [s'' es''].
      specialize (IHeexec1 _ _ _ _ _ eq_refl eq_refl).
      specialize (IHeexec2 _ _ _ _ _ eq_refl eq_refl).
      specialize (IHeexec3 _ _ _ _ _ eq_refl eq_refl).
      destruct IHeexec1 as (io1 & He1 & Hi1).
      destruct IHeexec2 as (io2 & He2 & Hi2).
      destruct IHeexec3 as (io3 & He3 & Hi3).
      eexists; split; [ | eapply EexecTraceWhileTrue ]; eauto.
      eapply execution_join; eauto.
      eapply execution_join; eauto.
    + specialize (IHeexec _ _ _ _ _ eq_refl eq_refl).
      destruct IHeexec as (io & He & Hi).
      eexists; split; [ | eapply EexecTraceWhileFalse ]; eauto.
  - intro H.
    destruct H as (io & He & Hi).
    revert He.
    revert s'.
    revert s.
    dependent induction Hi; intros.
    + inversion He; clear He; subst.
      inversion H5; clear H5; subst.
      econstructor. eauto.
    + inversion He; clear He; subst.
      econstructor.
    + inversion He; clear He; subst.
      econstructor.
    + inversion He; clear He; subst.
      econstructor.
    + eapply execution_split in He.
      destruct He as (? & He1 & He2).
      specialize (IHHi1 _ _ _ eq_refl _ _ He1).
      specialize (IHHi2 _ _ _ eq_refl _ _ He2).
      econstructor; eauto.
    + eapply execution_split in He.
      destruct He as (? & He1 & He2).
      eapply execution_split in He2.
      destruct He2 as (? & He2 & He3).
      specialize (IHHi1 _ _ _ eq_refl _ _ He1).
      specialize (IHHi2 _ _ _ eq_refl _ _ He2).
      specialize (IHHi3 _ _ _ eq_refl _ _ He3).
      eapply EexecWhileTrue; eauto.
    + eapply EexecWhileFalse; eauto.
Qed.
