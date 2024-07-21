Require Import IPR.Common.
Require Import IPR.Machine.
Require Import IPR.Tactics.

Require Import List.
Require Import Logic.FunctionalExtensionality.
Require Import Program.Equality.

Inductive dproc (I O : Type) : Type -> Type :=
| DCall : I -> dproc _ _ O
| DRet : forall T, T -> dproc _ _ T
| DBind : forall T T1, dproc _ _ T1 -> (T1 -> dproc _ _ T) -> dproc _ _ T
| DWhile : dproc _ _ bool -> dproc _ _ unit -> dproc _ _ unit
| DChoose : forall T (p1 p2 : dproc _ _ T), dproc _ _ T.

Arguments DCall [I O].
Arguments DRet [I O T].
Arguments DBind [I O T T1].
Arguments DWhile [I O].
Arguments DChoose [I O T].

Declare Scope dproc_scope.
Delimit Scope dproc_scope with dproc.
Notation "x <- p1 ; p2" := (DBind p1 (fun x => p2))
                            (at level 60, right associativity) : dproc_scope.
Notation "p1 ;; p2" := (_ <- p1; p2)%dproc (at level 60, right associativity) : dproc_scope.
Notation "p1 >>= p2" := (DBind p1 p2) (at level 50, left associativity, only parsing) : dproc_scope.
Notation "'Call' a" := (DCall a) (at level 10) : dproc_scope.
Notation "'Ret' v" := (DRet v) (at level 10) : dproc_scope.
Notation "'While'" := (DWhile) (at level 10) : dproc_scope.
Notation "p1 || p2" := (DChoose p1 p2) (at level 50, left associativity) : dproc_scope.

Local Open Scope dproc.

Inductive dexec {Il Ir Ol Or : Type} (M : machine (Il + Ir) (Ol + Or)) :
  forall T, dproc Il Ol T -> M.(state) -> result T M.(state) -> Prop :=
| DexecCall : forall s i s' o,
    M.(step) s (inl i) (Result (inl o) s') ->
    dexec _ _ (Call i) s (Result o s')
| DexecRet : forall T (v : T) s,
    dexec _ _ (Ret v) s (Result v s)
| DexecBind : forall T T1 (p : dproc _ _ T1) (p' : T1 -> dproc _ _ T) s v s' res,
    dexec _ _ p s (Result v s') ->
    dexec _ _ (p' v) s' res ->
    dexec _ _ (p >>= p') s res
| DexecWhileTrue : forall (g : dproc _ _ bool) (b : dproc _ _ unit) s s' s'' s''',
    dexec _ _ g s (Result true s') ->
    dexec _ _ b s' (Result tt s'') ->
    dexec _ _ (While g b) s'' (Result tt s''') ->
    dexec _ _ (While g b) s (Result tt s''')
| DexecWhileFalse : forall (g : dproc _ _ bool) (b : dproc _ _ unit) s s',
    dexec _ _ g s (Result false s') ->
    dexec _ _ (While g b) s (Result tt s')
| DexecChooseL : forall T (p p' : dproc _ _ T) s res,
    dexec _ _ p s res ->
    dexec _ _ (p || p') s res
| DexecChooseR : forall T (p p' : dproc _ _ T) s res,
    dexec _ _ p' s res ->
    dexec _ _ (p || p') s res
.

Arguments dexec [Il Ir Ol Or].

Create HintDb driver.
Hint Constructors dexec : driver.

Ltac rinv_dexec_head :=
  repeat lazymatch goal with
    | [ H : dexec _ _ (DCall _) _ _ |- _ ] => inv_exec H
    | [ H : dexec _ _ (DRet _) _ _ |- _ ] => inv_exec H
    | [ H : dexec _ _ (DBind _ _) _ _ |- _ ] => inv_exec H
    | [ H : dexec _ _ (DWhile _ _) _ _ |- _ ] => inv_exec H
    | [ H : dexec _ _ (DChoose _ _) _ _ |- _ ] => inv_exec H
    end.

(* drives M1 in terms of M2-level operations; we choose to not make this stateful *)
Definition driver (I1 O1 I2 O2 : Type) :=
  I2 -> dproc I1 O1 O2.

Fixpoint inline_calls {I1 O1 I2 O2 T : Type}
  (p : dproc I2 O2 T)
  (d1 : driver I1 O1 I2 O2) : dproc I1 O1 T :=
  match p with
  | Call i => d1 i
  | Ret v => Ret v
  | p1 >>= p2 => x <- inline_calls p1 d1; inline_calls (p2 x) d1
  | While g b => While (inline_calls g d1) (inline_calls b d1)
  | p1 || p2 => inline_calls p1 d1 || inline_calls p2 d1
  end.

Definition driver_compose {I1 O1 I2 O2 I3 O3 : Type}
  (d1 : driver I1 O1 I2 O2)
  (d2 : driver I2 O2 I3 O3) : driver I1 O1 I3 O3 :=
  fun i3 => inline_calls (d2 i3) d1.

Notation "d1 ∘ d2" := (driver_compose d1 d2) (at level 65, no associativity) : dproc_scope.

Theorem driver_compose_assoc :
  forall {I1 O1 I2 O2 I3 O3 I4 O4 : Type}
    (d1 : driver I1 O1 I2 O2)
    (d2 : driver I2 O2 I3 O3)
    (d3 : driver I3 O3 I4 O4),
    d1 ∘ (d2 ∘ d3) = (d1 ∘ d2) ∘ d3.
Proof.
  intros.
  unfold driver_compose.
  apply functional_extensionality.
  intros i4.
  remember (d3 i4) as di3 eqn:Hdi3; clear Hdi3; clear d3.
  induction di3; simpl; f_equal; auto.
  apply functional_extensionality; auto.
Qed.

Inductive dexec_trace {Il Ir Ol Or : Type} :
  forall T, dproc Il Ol T -> trace (Il + Ir) (Ol + Or) -> T -> Prop :=
| DexecTraceCall : forall i o,
    dexec_trace _ (Call i) (IO (inl i) (inl o) :: nil) o
| DexecTraceRet : forall T (v : T),
    dexec_trace _ (Ret v) nil v
| DexecTraceBind : forall T T1 (p : dproc _ _ T1) (p' : T1 -> dproc _ _ T) tr1 tr2 v res,
    dexec_trace _ p tr1 v ->
    dexec_trace _ (p' v) tr2 res ->
    dexec_trace _ (p >>= p') (tr1 ++ tr2) res
| DexecTraceWhileTrue : forall (g : dproc _ _ bool) (b : dproc _ _ unit) tr1 tr2 tr3,
    dexec_trace _ g tr1 true ->
    dexec_trace _ b tr2 tt ->
    dexec_trace _ (While g b) tr3 tt ->
    dexec_trace _ (While g b) (tr1 ++ tr2 ++ tr3) tt
| DexecTraceWhileFalse : forall (g : dproc _ _ bool) (b : dproc _ _ unit) tr,
    dexec_trace _ g tr false ->
    dexec_trace _ (While g b) tr tt
| DexecTraceChooseL : forall T (p p' : dproc _ _ T) tr res,
    dexec_trace _ p tr res ->
    dexec_trace _ (p || p') tr res
| DexecTraceChooseR : forall T (p p' : dproc _ _ T) tr res,
    dexec_trace _ p' tr res ->
    dexec_trace _ (p || p') tr res
.

Arguments dexec_trace [Il Ir Ol Or].

Theorem dexec_dexec_trace : forall (Il Ir Ol Or : Type) (T : Type) (p : dproc Il Ol T)
                              (M : machine (Il + Ir) (Ol + Or)) s res s',
  dexec M _ p s (Result res s') <->
  ( exists tr,
    execution M s tr s' /\
    dexec_trace _ p tr res ).
Proof.
  split.
  - intro H.
    dependent induction H.
    + eexists; split; [ | econstructor ].
      econstructor; eauto. econstructor.
    + eexists; split; [ | econstructor ].
      econstructor.
    + specialize (IHdexec1 _ _ eq_refl).
      specialize (IHdexec2 _ _ eq_refl).
      destruct IHdexec1 as (io1 & He1 & Hi1).
      destruct IHdexec2 as (io2 & He2 & Hi2).
      eexists; split; [ | econstructor ]; eauto.
      eapply execution_join; eauto.
    + specialize (IHdexec1 _ _ eq_refl).
      specialize (IHdexec2 _ _ eq_refl).
      specialize (IHdexec3 _ _ eq_refl).
      destruct IHdexec1 as (io1 & He1 & Hi1).
      destruct IHdexec2 as (io2 & He2 & Hi2).
      destruct IHdexec3 as (io3 & He3 & Hi3).
      eexists; split; [ | eapply DexecTraceWhileTrue ]; eauto.
      eapply execution_join; eauto.
      eapply execution_join; eauto.
    + specialize (IHdexec _ _ eq_refl).
      destruct IHdexec as (io & He & Hi).
      eexists; split; [ | eapply DexecTraceWhileFalse ]; eauto.
    + specialize (IHdexec _ _ eq_refl).
      destruct IHdexec as (io & He & Hi).
      eexists; split; [ | eapply DexecTraceChooseL ]; eauto.
    + specialize (IHdexec _ _ eq_refl).
      destruct IHdexec as (io & He & Hi).
      eexists; split; [ | eapply DexecTraceChooseR ]; eauto.
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
    + eapply execution_split in He.
      destruct He as (? & He1 & He2).
      specialize (IHHi1 _ _ He1).
      specialize (IHHi2 _ _ He2).
      econstructor; eauto.
    + eapply execution_split in He.
      destruct He as (? & He1 & He2).
      eapply execution_split in He2.
      destruct He2 as (? & He2 & He3).
      specialize (IHHi1 _ _ He1).
      specialize (IHHi2 _ _ He2).
      specialize (IHHi3 _ _ He3).
      eapply DexecWhileTrue; eauto.
    + eapply DexecWhileFalse; eauto.
    + eapply DexecChooseL; eauto.
    + eapply DexecChooseR; eauto.
Qed.
